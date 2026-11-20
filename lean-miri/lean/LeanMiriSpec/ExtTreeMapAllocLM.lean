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
`protectorEndAccessIsWrite?`, `execProtectorEndAccess`, `execFrameExitMiri`,
`isSyntacticallySized`, `validateRawPtrFastPath`, `validateRawPtrFull`,
`validateSafeThinRef`, `vtableMatchesExpectedSpec`, `VTableWorldWF`,
`SaltedVTableWorldWF`, `validateWideDynSafePtr`, `validateWideDynSafePtrDeep`,
`validateWideDynSafePtrWithBytes`, `visitConcreteValue`) and the vendored
`lean-miri` model under `lean-miri/vendor/Miri` plus the `LM-3.1` / `LM-3.2`
simulation relations (`StateRelLM3_1`, `StateRelLM3_2`, `annealResolvePtr`,
`annealValidityHooks`).

## Axiom policy

* Every theorem whose statement touches only choice-free types depends on at
  most `propext` and `Quot.sound` (zero `Classical.choice`).
* Theorems whose statements mention vendored `Miri.Memory.MemoryState` (which
  embeds `Miri.Memory.KeyedArray` over `Std.HashMap`), `StateRelLM3_1` /
  `StateRelLM3_2`, `Miri.Interpreter.ValidityMachine`,
  `Miri.Interpreter.ValidityVisitor.validatePlace`, `annealValidityHooks`, or
  `Miri.TreeBorrows.BorrowTree.releaseProtector` inherit `Classical.choice`
  from those vendored definitions and depend on at most
  `[propext, Classical.choice, Quot.sound]`, matching `LeanMiriSpec.FloatCastLM`
  and `LeanMiriSpec.WitFloatCastLM`.
* `sorryAx`, `Lean.ofReduceBool` (`native_decide`), `unsafe`, and custom axioms
  are strictly forbidden (`0` allowed) and checked for every public theorem via
  `#guard_msgs in #print axioms` in Part 4.

## Overview of proved correspondence

* **Part 1A** — `Miri.Memory.AllocId` and `MiriAllocId` exact full-width
  bijection (`allocId_bijection`), `ofUInt64`, `==`, keyed-map order, and
  `toTrustedAllocId`.
* **Part 1B** — kind, mutability, `AllocationInfo`, and full error-vocabulary
  translations (including unconditional `deallocErrOfMiri_toMiri` round-trip
  covering `layoutMismatch`).
* **Part 1C** — `MiriAllocRows`, `KeyedArray` first-match & `any?` theorems,
  and the live `Miri.Memory.MemoryState` bridge: `MemoryState.toKeyed`,
  `isAllocLive`, `getAllocInfo` (with duplicate-global & alignment-bound
  characterization), `getLiveAllocSizeAndAlign`, `checkPtrAccess`,
  `reserveAllocId`, `insertAllocation` / `allocatePtr`, `deallocatePtrWith`
  (exact failure ordering + detached-state retention), `MachineHooks.memoryRaceAccess`
  / `AllocationMachine.deallocate` (`RaceDetectorMode` & `detachRaceClock`),
  and `KeyedStateRelLM3_1` / `KeyedStateRelLM3_2` lifting + live/dead array
  permutation invariance.
* **Part 1D** — `Miri.Memory.{sizeAsI64, checkAndDerefPtr, checkPtrAccess,
  getPtrAccess}` against keyed/linear worlds and `annealResolvePtr` / `PtrRel`.
* **Part 1E** — `RetagPolicy.create`, `Permission.associatedAccess`,
  `TraversalTree.traverse` (both `VisitChildrenOfAccessed` and
  `SkipChildrenOfAccessed`, closing the `nodes.length + 1` vs `tree.nodes.size`
  fuel gap on rooted trees), vendored `BorrowTree.releaseProtector` (missing
  tag, no-access skip, strict-descendant preservation, sibling foreign access),
  and `MachineHooks.beforeStackPopWithEnsure` batch protector retention.
* **Part 2** — `ValidityVisitor.classifyPointerAccessError`, general
  `VTable.checkForTypeRead` (principal-less and principal-bearing under
  key-injective `stableKey`, plus the `stableKey`-collision separation witness),
  `VTable.{getPtrVTableTypeRead, getSizeAndAlignRead, getPointer}` against
  `VTableWorldWF` / `SaltedVTableWorldWF` / `upcastVTableToAutoTraits`,
  `lean-miri#79` `[T; N]` syntactic `Sized` fast-path & `validateSafeThinRef`
  against `ValidityVisitor` / `ValidityMachine` / `annealValidityHooks`, and
  `lean-miri#82` wide-`dyn` vtable-before-data-UB precedence, `mayDangle`
  `addressTooClose`, recursive `childSession` (`validatePlace`), field-before-
  inhabited `(bool, !)` / `(u32, !)`, zero `fn()`, surrogate `char`, `O(1)`
  ZST-array `[(); usize::MAX]`, fail-closed fuel, and 16-byte nested wide refs.
* **Part 2D** — strengthenings across Parts 1C, 1E, and 2: `KeyedStateRelLM3_*` ↔
  `StateRelLM3_*` equivalences and `StateRelLM3_1` / `StateRelLM3_2` invariance under ANY `live`
  permutation and ANY `dead` array (no distinct-key hypothesis); the deallocation data-race stage
  (`MachineHooks.memoryRaceAccess`) against `machineDeallocHook` as one relational theorem over
  every branch, and the exact two-sided race-table effect of `AllocationMachine.deallocate`
  (`detachRaceClock`); `MachineHooks.beforeStackPopWithEnsure` for ARBITRARILY many protectors as a pure
  release fold, with a whole-frame simulation against `execFrameExitMiri` lifted from any
  per-release simulation; state/choice-polymorphic vtable reads (`VTableReadsWorldAt`), every
  invalid vtable form beating every data-pointer check through `ValidityVisitor.validatePlace` for
  both `recursive = false` and `recursive = true`, and the exact fail-closed wide-pointer boundary
  of `annealValidityHooks`.
* **Part 3** — closed (hypothesis-free) non-vacuity canaries across all parts.
* **Part 4** — exhaustive `#guard_msgs in #print axioms` pins for every public
  theorem.
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
  | .layoutMismatch id actualSize requestedSize actualAlign requestedAlign =>
    some (.layoutMismatch (ofMiriAllocId id) actualSize.bytes requestedSize.bytes
      (UInt8.ofNat actualAlign.pow2) (UInt8.ofNat requestedAlign.pow2))
  | .hookFailure _ message => some (.hookFailure message)
  | .duplicateDeadAllocation id => some (.duplicateDeadAllocation (ofMiriAllocId id))
  | _ => none

/-- Every theory deallocation failure — including `layoutMismatch` — round-trips
unconditionally through the vendored `Miri.Memory.MemoryLifecycleError` vocabulary. -/
theorem deallocErrOfMiri_toMiri (e : DeallocErr) :
    deallocErrOfMiri (deallocErrToMiri e) = some e := by
  cases e with
  | layoutMismatch id s₁ s₂ a₁ a₂ =>
    show some (DeallocErr.layoutMismatch _ s₁ s₂ (UInt8.ofNat a₁.toNat) (UInt8.ofNat a₂.toNat)) = _
    rw [UInt8.ofNat_toNat, UInt8.ofNat_toNat]
    rfl
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

/-- `resolveWithBase` instantiated at `mach.lookupBaseAddr` IS `annealResolvePtr mach`
definitionally (`rfl`), so no stand-in resolver remains. -/
theorem resolveWithBase_eq_annealResolvePtr (mach : AnnealMachine) :
    resolveWithBase mach.lookupBaseAddr = annealResolvePtr mach := rfl

/-- Direct `annealResolvePtr` form of `ptrRel_resolvesAs` for an `AnnealMachine`. -/
theorem ptrRel_annealResolvePtr_resolvesAs {allocMap : List AllocMapEntry}
    {p : Trusted.Rustc.V2026_06_01.MirAst.ProvenancePtr}
    {mptr : Miri.Memory.Pointer AnnealProv} (h : PtrRel allocMap p mptr)
    (mach : AnnealMachine)
    (hbase : ∀ e ∈ allocMap, mach.lookupBaseAddr e.allocId = some (annealStackBaseAddr e.allocId)) :
    ∃ e ∈ allocMap, e.tag = p.tag ∧
      ResolvesAs (annealResolvePtr mach) ⟨mptr.offset, some mptr.provenance⟩
        (some (ofMiriAllocId e.allocId, UInt64.ofNat p.offsetBytes)) :=
  ptrRel_resolvesAs h mach.lookupBaseAddr hbase

/-- Direct `annealResolvePtr` form of `ptrRel_checkPtrAccess_isOk_eq_keyed`. -/
theorem ptrRel_annealResolvePtr_checkPtrAccess_isOk_eq_keyed {allocMap : List AllocMapEntry}
    {p : Trusted.Rustc.V2026_06_01.MirAst.ProvenancePtr}
    {mptr : Miri.Memory.Pointer AnnealProv} (h : PtrRel allocMap p mptr)
    (mach : AnnealMachine)
    (hbase : ∀ e ∈ allocMap, mach.lookupBaseAddr e.allocId = some (annealStackBaseAddr e.allocId))
    (target : Miri.Memory.PointerArithmetic) (size : Miri.ABI.Size)
    (msg : Miri.Memory.CheckInAllocMsg) (kw : KeyedAllocWorld) :
    ∃ e ∈ allocMap, e.tag = p.tag ∧
      (Miri.Memory.checkPtrAccess target ⟨mptr.offset, some mptr.provenance⟩ size msg
          (annealResolvePtr mach) (keyedLookup kw)).isOk =
        kw.checkPtrAccess (some (ofMiriAllocId e.allocId, UInt64.ofNat p.offsetBytes))
          size.bytes.toNat :=
  ptrRel_checkPtrAccess_isOk_eq_keyed h mach.lookupBaseAddr hbase target size msg kw

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

/-! ### Live `Miri.Memory.KeyedArray` & `Miri.Memory.MemoryState` bridge (`lean-miri#73`) -/

local macro "miriKAIndexStep" : term =>
  `(miri_etm_private% Miri.Memory.KeyedArray Miri.Memory.indexStep)
local macro "miriKACanonicalIndex" : term =>
  `(miri_etm_private% Miri.Memory.KeyedArray Miri.Memory.canonicalIndex)
local macro "miriKAKeys" : term =>
  `(miri_etm_private% Miri.Memory.KeyedArray Miri.Memory.KeyedArray.keys)
local macro "miriKARows" : term =>
  `(miri_etm_private% Miri.Memory.KeyedArray Miri.Memory.KeyedArray.rows)
local macro "miriKAIndexState" : term =>
  `(miri_etm_private% Miri.Memory.KeyedArray Miri.Memory.KeyedArray.indexState)
local macro "miriKAExact" : term =>
  `(miri_etm_private% Miri.Memory.KeyedArray Miri.Memory.KeyedArray.exact)
local macro "miriKAKeysMatchRows" : term =>
  `(miri_etm_private% Miri.Memory.KeyedArray Miri.Memory.KeyedArray.keysMatchRows)
local macro "miriMSIssuedTable" : term =>
  `(miri_etm_private% Miri.Memory.MemoryState Miri.Memory.MemoryState.issuedIdTable)
local macro "miriMSGlobalTable" : term =>
  `(miri_etm_private% Miri.Memory.MemoryState Miri.Memory.MemoryState.globalTable)
local macro "miriMSExtraFnTable" : term =>
  `(miri_etm_private% Miri.Memory.MemoryState Miri.Memory.MemoryState.extraFnPtrTable)
local macro "miriMSVaListTable" : term =>
  `(miri_etm_private% Miri.Memory.MemoryState Miri.Memory.MemoryState.vaListTable)
local macro "miriMSContainsId" : term =>
  `(miri_etm_private% Miri.Memory.MemoryState Miri.Memory.MemoryState.containsId)
local macro "miriMSFindLive?" : term =>
  `(miri_etm_private% Miri.Memory.MemoryState Miri.Memory.MemoryState.findLive?)
local macro "miriMSInsertLive" : term =>
  `(miri_etm_private% Miri.Memory.MemoryState Miri.Memory.MemoryState.insertLive)
local macro "miriMSRemoveLive" : term =>
  `(miri_etm_private% Miri.Memory.MemoryState Miri.Memory.MemoryState.removeLive)
local macro "miriMSInsertDead" : term =>
  `(miri_etm_private% Miri.Memory.MemoryState Miri.Memory.MemoryState.insertDead)
local macro "miriMLInsertWithId" : term =>
  `(miri_etm_private% Miri.Memory.MemoryState Miri.Memory.MemoryLifecycle.insertAllocationWithId)

private def positionsOf {K : Type} [BEq K] (key : K) : Nat → List K → List Nat
  | _, [] => []
  | off, k :: rest =>
    if k == key then off :: positionsOf key (off + 1) rest
    else positionsOf key (off + 1) rest

private theorem foldl_indexStep_getElem? {K : Type} [BEq K] [Hashable K] [LawfulBEq K]
    [LawfulHashable K] (ks : List K) (key : K) :
    ∀ (off : Nat) (m : Std.HashMap K (Array Nat)),
      (ks.foldl miriKAIndexStep (off, m)).2[key]? =
        match m[key]? with
        | some arr => some (arr ++ (positionsOf key off ks).toArray)
        | none =>
          match positionsOf key off ks with
          | [] => none
          | p :: ps => some ((p :: ps).toArray) := by
  induction ks with
  | nil =>
    intro off m
    simp only [List.foldl_nil, positionsOf]
    cases m[key]? with
    | none => rfl
    | some arr =>
      show some arr = some (arr ++ ([] : List Nat).toArray)
      simp
  | cons k rest ih =>
    intro off m
    simp only [List.foldl_cons]
    change (rest.foldl miriKAIndexStep
      (off + 1, m.insert k ((m.getD k #[]).push off))).2[key]? = _
    rw [ih]
    simp only [Std.HashMap.getElem?_insert, positionsOf]
    by_cases hk : k = key
    · subst hk
      simp only [beq_self_eq_true, ↓reduceIte, Std.HashMap.getD_eq_getD_getElem?]
      cases hm : m[k]? with
      | none =>
        simp only [Option.getD_none]
        show some (#[].push off ++ (positionsOf k (off + 1) rest).toArray) =
          some ((off :: positionsOf k (off + 1) rest).toArray)
        congr 1
        apply Array.toList_inj.mp
        simp
      | some arr =>
        simp only [Option.getD_some]
        congr 1
        apply Array.toList_inj.mp
        simp
    · have hne : (k == key) = false := beq_false_of_ne hk
      simp only [hne, Bool.false_eq_true, ↓reduceIte]

private theorem positionsOf_head_find? {K V : Type} [BEq K] [LawfulBEq K]
    (keyFn : V → K) (key : K) (rows : List V) :
    ∀ (base : Nat) (full : List V),
      (∀ i, i < rows.length → full[base + i]? = rows[i]?) →
      (match positionsOf key base (rows.map keyFn) with
       | [] => none
       | p :: _ => full[p]?) =
        rows.find? (fun v => keyFn v == key) := by
  induction rows with
  | nil =>
    intro base full _
    rfl
  | cons v rest ih =>
    intro base full hfull
    simp only [List.map_cons, positionsOf, List.find?]
    by_cases hk : keyFn v == key
    · simp only [hk, ↓reduceIte]
      have h0 := hfull 0 (by simp)
      simpa using h0
    · simp only [hk, Bool.false_eq_true, ↓reduceIte]
      exact ih (base + 1) full fun i hi => by
        have := hfull (i + 1) (by simp; omega)
        simpa [Nat.add_assoc, Nat.add_comm 1 i] using this

/-- **Certified `KeyedArray.find?` exactness**: for any lawful key type (`UInt64`, `Nat`, ...),
the hash-indexed `Miri.Memory.KeyedArray.find?` returns the exact first matching row of
`table.toArray`. -/
theorem keyedArray_find?_eq_list_find? {K V : Type} [BEq K] [Hashable K] [LawfulBEq K]
    [LawfulHashable K] {keyFn : V → K} (table : Miri.Memory.KeyedArray K V keyFn) (key : K) :
    table.find? key = table.toArray.toList.find? (fun v => keyFn v == key) := by
  have hexact : (miriKAIndexState table).2[key]? =
      match positionsOf key 0 (table.toArray.toList.map keyFn) with
      | [] => none
      | p :: ps => some ((p :: ps).toArray) := by
    have h1 := congrArg Prod.snd (miriKAExact table)
    have h2 : (miriKAKeys table).toList = table.toArray.toList.map keyFn := by
      have hm := miriKAKeysMatchRows table
      change (miriKAKeys table).toList = (miriKARows table).toList.map keyFn
      rw [hm, Array.toList_map]
    change (miriKAIndexState table).2[key]? = _
    rw [h1]
    change ((miriKAKeys table).foldl miriKAIndexStep (0, {})).2[key]? = _
    rw [← Array.foldl_toList, h2, foldl_indexStep_getElem?]
    simp
  have hget : (miriKAIndexState table).2.get? key = (miriKAIndexState table).2[key]? :=
    Std.HashMap.get?_eq_getElem?
  unfold Miri.Memory.KeyedArray.find?
  change (do
      let indices ← (miriKAIndexState table).2.get? key
      let rowIndex ← indices[0]?
      (miriKARows table)[rowIndex]?) = _
  rw [hget, hexact]
  have hpos := positionsOf_head_find? keyFn key table.toArray.toList 0 table.toArray.toList
    (fun i _ => by simp)
  rw [← hpos]
  cases hps : positionsOf key 0 (table.toArray.toList.map keyFn) with
  | nil => rfl
  | cons p ps =>
    change (miriKARows table)[p]? = table.toArray.toList[p]?
    simp [Miri.Memory.KeyedArray.toArray]

private def anyForInStep {V : Type} (rows : Array V) (p : V → Bool)
    (rowIndex : Nat) (_ : Option Bool × Unit) : Id (ForInStep (Option Bool × Unit)) :=
  match rows[rowIndex]? with
  | some value =>
    if p value = true then pure (ForInStep.done (some true, ()))
    else pure (ForInStep.yield (none, ()))
  | none => pure (ForInStep.yield (none, ()))

private theorem forIn_any_loop {V : Type} (rows : Array V) (p : V → Bool) (idxs : List Nat) :
    (Id.run do
      for rowIndex in idxs.toArray do
        if let some value := rows[rowIndex]? then
          if p value then return true
      return false) =
      idxs.any (fun i => match rows[i]? with | some v => p v | none => false) := by
  have hstep : ∀ (xs : List Nat),
      (forIn (m := Id) xs (none, ()) (anyForInStep rows p)).1 =
      if xs.any (fun i => match rows[i]? with | some v => p v | none => false) then some true
      else none := by
    intro xs
    induction xs with
    | nil => rfl
    | cons i rest ih =>
      rcases hri : rows[i]? with _ | v
      · simp only [List.any_cons, List.forIn_cons, anyForInStep, hri, bind, Bind.bind,
          pure, Pure.pure, Bool.false_or]
        exact ih
      · cases hpv : p v with
        | true =>
          simp only [List.any_cons, List.forIn_cons, anyForInStep, hri, hpv, ↓reduceIte,
            bind, Bind.bind, pure, Pure.pure, Bool.true_or]
        | false =>
          simp only [List.any_cons, List.forIn_cons, anyForInStep, hri, hpv, Bool.false_eq_true,
            ↓reduceIte, bind, Bind.bind, pure, Pure.pure, Bool.false_or]
          exact ih
  have heq : (Id.run do
      for rowIndex in idxs.toArray do
        if let some value := rows[rowIndex]? then
          if p value then return true
      return false) =
      match (forIn (m := Id) idxs (none, ()) (anyForInStep rows p)).1 with
      | some r => r
      | none => false := by
    simp only [Id.run, pure, Pure.pure, bind, Bind.bind, List.forIn_toArray]
    have hfun : (fun (rowIndex : Nat) (_ : Option Bool × Unit) =>
        match rows[rowIndex]? with
        | some value =>
          if p value = true then ForInStep.done (some true, ())
          else ForInStep.yield (none, ())
        | _ => ForInStep.yield (none, ())) = anyForInStep rows p := by
      funext rowIndex _
      rcases h : rows[rowIndex]? with _ | v <;> simp [anyForInStep, h, pure, Pure.pure]
    rw [hfun]
    cases (forIn (m := Id) idxs (none, ()) (anyForInStep rows p)).1 <;> rfl
  rw [heq, hstep]
  cases idxs.any (fun i => match rows[i]? with | some v => p v | none => false) <;> rfl

private theorem positionsOf_any {K V : Type} [BEq K] [LawfulBEq K]
    (keyFn : V → K) (key : K) (p : V → Bool) (rows : List V) :
    ∀ (base : Nat) (full : List V),
      (∀ i, i < rows.length → full[base + i]? = rows[i]?) →
      (positionsOf key base (rows.map keyFn)).any
          (fun i => match full[i]? with | some v => p v | none => false) =
        rows.any (fun v => keyFn v == key && p v) := by
  induction rows with
  | nil =>
    intro base full _
    rfl
  | cons v rest ih =>
    intro base full hfull
    simp only [List.map_cons, positionsOf, List.any_cons]
    have hrest := ih (base + 1) full fun i hi => by
      have := hfull (i + 1) (by simp; omega)
      simpa [Nat.add_assoc, Nat.add_comm 1 i] using this
    by_cases hk : keyFn v == key
    · simp only [hk, ↓reduceIte, List.any_cons, Bool.true_and]
      have h0 : full[base]? = some v := by
        have := hfull 0 (by simp)
        simpa using this
      rw [h0, hrest]
    · simp only [hk, Bool.false_eq_true, ↓reduceIte, Bool.false_and, Bool.false_or]
      exact hrest

/-- **Certified `KeyedArray.any?` exactness**: `table.any? key p` tests `p` on every row in
`table.toArray` whose key equals `key`. -/
theorem keyedArray_any?_eq_list_any {K V : Type} [BEq K] [Hashable K] [LawfulBEq K]
    [LawfulHashable K] {keyFn : V → K} (table : Miri.Memory.KeyedArray K V keyFn)
    (key : K) (p : V → Bool) :
    table.any? key p = table.toArray.toList.any (fun v => keyFn v == key && p v) := by
  have hexact : (miriKAIndexState table).2[key]? =
      match positionsOf key 0 (table.toArray.toList.map keyFn) with
      | [] => none
      | p :: ps => some ((p :: ps).toArray) := by
    have h1 := congrArg Prod.snd (miriKAExact table)
    have h2 : (miriKAKeys table).toList = table.toArray.toList.map keyFn := by
      have hm := miriKAKeysMatchRows table
      change (miriKAKeys table).toList = (miriKARows table).toList.map keyFn
      rw [hm, Array.toList_map]
    change (miriKAIndexState table).2[key]? = _
    rw [h1]
    change ((miriKAKeys table).foldl miriKAIndexStep (0, {})).2[key]? = _
    rw [← Array.foldl_toList, h2, foldl_indexStep_getElem?]
    simp
  have hget : (miriKAIndexState table).2.get? key = (miriKAIndexState table).2[key]? :=
    Std.HashMap.get?_eq_getElem?
  have hpos := positionsOf_any keyFn key p table.toArray.toList 0 table.toArray.toList
    (fun i _ => by simp)
  rw [← hpos]
  unfold Miri.Memory.KeyedArray.any?
  change (Id.run do
      let some indices := (miriKAIndexState table).2.get? key | return false
      for rowIndex in indices do
        if let some value := (miriKARows table)[rowIndex]? then
          if p value then return true
      return false) = _
  rw [hget, hexact]
  cases hps : positionsOf key 0 (table.toArray.toList.map keyFn) with
  | nil => rfl
  | cons x xs =>
    have hloop := forIn_any_loop (miriKARows table) p (x :: xs)
    simpa [Miri.Memory.KeyedArray.toArray] using hloop

section MemoryStateBridge

variable {Prov Extra MachineKind : Type}

/-- Extract the row-level observation surface (`MiriAllocRows`) directly from a live
vendored `Miri.Memory.MemoryState`. -/
def memoryStateToRows (state : Miri.Memory.MemoryState Prov Extra MachineKind) :
    MiriAllocRows Prov Extra MachineKind where
  nextAllocId := state.nextAllocId
  idSupplyExhausted := state.idSupplyExhausted
  issued := state.issuedIds
  globals := state.globals
  live := state.live
  dead := state.dead

/-- Direct projection of a vendored `Miri.Memory.MemoryState` (with optional race clocks) to
`LinearAllocWorld`. -/
def memoryStateToLinear (proj : RowProjection Prov Extra MachineKind)
    (state : Miri.Memory.MemoryState Prov Extra MachineKind)
    (race : List (MiriAllocId × RaceClockEntry) := []) : LinearAllocWorld :=
  { (memoryStateToRows state).toLinear proj with race := race }

/-- Direct projection of a vendored `Miri.Memory.MemoryState` (with optional race clocks) to
`KeyedAllocWorld`. -/
def memoryStateToKeyed (proj : RowProjection Prov Extra MachineKind)
    (state : Miri.Memory.MemoryState Prov Extra MachineKind)
    (race : List (MiriAllocId × RaceClockEntry) := []) : KeyedAllocWorld :=
  KeyedAllocWorld.ofLinear (memoryStateToLinear proj state race)

theorem allocWorldRel_memoryState (proj : RowProjection Prov Extra MachineKind)
    (state : Miri.Memory.MemoryState Prov Extra MachineKind)
    (race : List (MiriAllocId × RaceClockEntry) := []) :
    AllocWorldRel (memoryStateToLinear proj state race) (memoryStateToKeyed proj state race) :=
  allocWorldRel_ofLinear _

/-- Well-formedness boundary where the vendored `MemoryState`'s auxiliary non-theory tables
(`extraFnPtrTable`, `vaListTable`, and the diagnostic `sourceAllocIdWorldActive` mirror) are
inactive. -/
structure MemoryStateCoreDomain (state : Miri.Memory.MemoryState Prov Extra MachineKind) : Prop where
  noExtraFnPtrs : state.extraFnPtrIds = #[]
  noVaLists : state.vaListIds = #[]
  noSourceAllocWorld : state.sourceAllocIdWorldActive = false

/-- Alignment-exponent fit (`align.pow2 < 256`, strictly weaker than rustc's `Align.MAX.pow2 = 29`)
so `UInt8.ofNat align.pow2` round-trips without 8-bit truncation. -/
structure MemoryStateAlignFit (state : Miri.Memory.MemoryState Prov Extra MachineKind) : Prop where
  liveAlignLt : ∀ row ∈ state.live.toList, row.2.allocation.align.pow2 < 256
  globalAlignLt : ∀ g ∈ state.globals.toList, g.align.pow2 < 256
  deadAlignLt : ∀ d ∈ state.dead.toList, d.align.pow2 < 256

/-- Distinct runtime IDs across the compiler global table: ensures `hasFunctionPointer`
(which scans all rows for `id`) agrees with first-match `findGlobal?`. -/
def MemoryStateGlobalsDistinct (state : Miri.Memory.MemoryState Prov Extra MachineKind) : Prop :=
  (state.globals.toList.map fun g => g.allocId).Nodup

private theorem allocId_value_beq (a b : Miri.Memory.AllocId) :
    (a.value == b.value) = (a == b) := by
  by_cases h : a = b
  · subst h
    rw [beq_self_eq_true, beq_self_eq_true]
  · have hv : a.value ≠ b.value := fun heq => h (by
      cases a; cases b; simp only at heq; subst heq; rfl)
    rw [beq_false_of_ne hv, beq_false_of_ne h]

private theorem array_contains_map_value {α : Type} (arr : Array α)
    (getId : α → Miri.Memory.AllocId) (id : Miri.Memory.AllocId) :
    (arr.map fun x => (getId x).value).contains id.value =
      arr.toList.any (fun x => getId x == id) := by
  rw [← Array.contains_toList, Array.toList_map]
  induction arr.toList with
  | nil => rfl
  | cons x rest ih =>
    simp only [List.map_cons, List.contains_cons, List.any_cons]
    have hswap : (id.value == (getId x).value) = (getId x == id) := by
      rw [allocId_value_beq]
      by_cases h : getId x = id
      · subst h; simp
      · have h' : id ≠ getId x := fun he => h he.symm
        simp [beq_false_of_ne h, beq_false_of_ne h']
    rw [hswap, ih]

private theorem find?_value_eq_find? {α : Type} (xs : List α)
    (getId : α → Miri.Memory.AllocId) (id : Miri.Memory.AllocId) :
    xs.find? (fun x => (getId x).value == id.value) = xs.find? (fun x => getId x == id) := by
  congr 1
  funext x
  exact allocId_value_beq (getId x) id

theorem memoryState_findGlobal?_eq_list_find?
    (state : Miri.Memory.MemoryState Prov Extra MachineKind) (id : Miri.Memory.AllocId) :
    state.findGlobal? id = state.globals.toList.find? (fun g => g.allocId == id) := by
  unfold Miri.Memory.MemoryState.findGlobal?
  rw [keyedArray_find?_eq_list_find?]
  exact find?_value_eq_find? state.globals.toList (fun g => g.allocId) id

theorem memoryState_hasIssuedId_eq_any
    (state : Miri.Memory.MemoryState Prov Extra MachineKind) (id : Miri.Memory.AllocId) :
    state.hasIssuedId id = state.issuedIds.toList.any (fun x => x == id) := by
  unfold Miri.Memory.MemoryState.hasIssuedId Miri.Memory.MemoryState.issuedIds
  rw [Miri.Memory.KeyedArray.contains_rows]
  exact array_contains_map_value (miriMSIssuedTable state).toArray (fun x => x) id

theorem memoryState_hasGlobalId_eq_any
    (state : Miri.Memory.MemoryState Prov Extra MachineKind) (id : Miri.Memory.AllocId) :
    state.hasGlobalId id = state.globals.toList.any (fun g => g.allocId == id) := by
  unfold Miri.Memory.MemoryState.hasGlobalId Miri.Memory.MemoryState.globals
  rw [Miri.Memory.KeyedArray.contains_rows]
  exact array_contains_map_value (miriMSGlobalTable state).toArray (fun g => g.allocId) id

/-- **`MemoryState.isAllocLive` correspondence**: on the core domain (no `extraFnPtr` / `vaList`
entries), vendored `Miri.Memory.MemoryState.isAllocLive` IS `KeyedAllocWorld.isAllocLive`. -/
theorem memoryState_isAllocLive_eq_keyed (proj : RowProjection Prov Extra MachineKind)
    (state : Miri.Memory.MemoryState Prov Extra MachineKind)
    (hcore : MemoryStateCoreDomain state) (id : Miri.Memory.AllocId)
    (race : List (MiriAllocId × RaceClockEntry) := []) :
    state.isAllocLive id = (memoryStateToKeyed proj state race).isAllocLive (ofMiriAllocId id) := by
  have hfn : (miriMSExtraFnTable state).contains id.value = false := by
    rw [Miri.Memory.KeyedArray.contains_rows]
    change (state.extraFnPtrIds.map (fun x => x.value)).contains id.value = false
    rw [hcore.noExtraFnPtrs]
    simp
  have hva : (miriMSVaListTable state).contains id.value = false := by
    rw [Miri.Memory.KeyedArray.contains_rows]
    change (state.vaListIds.map (fun x => x.value)).contains id.value = false
    rw [hcore.noVaLists]
    simp
  have hglob : (miriMSGlobalTable state).contains id.value =
      state.globals.toList.any (fun g => g.allocId == id) :=
    memoryState_hasGlobalId_eq_any state id
  have hlive : state.live.any (fun entry => entry.1 == id) =
      state.live.toList.any (fun entry => entry.1 == id) := by
    rw [← Array.any_toList]
  have hkw : (memoryStateToKeyed proj state race).isAllocLive (ofMiriAllocId id) =
      ((memoryStateToRows state).toKeyed proj).isAllocLive (ofMiriAllocId id) := by
    unfold memoryStateToKeyed memoryStateToLinear MiriAllocRows.toKeyed
      KeyedAllocWorld.isAllocLive KeyedAllocWorld.findLive? KeyedAllocWorld.findGlobal?
      KeyedAllocWorld.ofLinear
    rfl
  rw [hkw, toKeyed_isAllocLive]
  unfold Miri.Memory.MemoryState.isAllocLive
  change (state.live.any (fun entry => entry.1 == id) ||
    (miriMSExtraFnTable state).contains id.value ||
    (miriMSVaListTable state).contains id.value ||
    (miriMSGlobalTable state).contains id.value) = _
  rw [hlive, hfn, hva, hglob]
  simp [memoryStateToRows]

private theorem any_eq_find?_kind_of_nodup
    (gs : List Miri.Memory.GlobalAllocation)
    (hnd : (gs.map fun g => g.allocId).Nodup) (id : Miri.Memory.AllocId) :
    gs.any (fun g => g.allocId == id && g.kind == .function) =
      match gs.find? (fun g => g.allocId == id) with
      | some g => g.kind == .function
      | none => false := by
  induction gs with
  | nil => rfl
  | cons g rest ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    simp only [List.any_cons, List.find?]
    by_cases hid : g.allocId = id
    · subst hid
      simp only [beq_self_eq_true, Bool.true_and]
      have hrest : rest.any (fun g' => g'.allocId == g.allocId && g'.kind == .function) = false := by
        cases h : rest.any (fun g' => g'.allocId == g.allocId && g'.kind == .function) with
        | false => rfl
        | true =>
          obtain ⟨g', hg', hcond⟩ := List.any_eq_true.mp h
          have heq := eq_of_beq (Bool.and_eq_true_iff.mp hcond).1
          exact absurd (List.mem_map.mpr ⟨g', hg', heq⟩) hnd.1
      rw [hrest, Bool.or_false]
    · have hne : (g.allocId == id) = false := beq_false_of_ne hid
      simp only [hne, Bool.false_and, Bool.false_or]
      exact ih hnd.2

/-- **`MemoryState.getAllocInfo` correspondence**: on the core domain with distinct global IDs
and fit alignments (`pow2 < 256`), vendored `Miri.Memory.MemoryState.getAllocInfo` IS
`keyedLookup (memoryStateToKeyed proj state race)`. -/
theorem memoryState_getAllocInfo_eq_keyed (proj : RowProjection Prov Extra MachineKind)
    (state : Miri.Memory.MemoryState Prov Extra MachineKind)
    (hcore : MemoryStateCoreDomain state)
    (hglobNd : MemoryStateGlobalsDistinct state)
    (halign : MemoryStateAlignFit state)
    (id : Miri.Memory.AllocId) (race : List (MiriAllocId × RaceClockEntry) := []) :
    state.getAllocInfo id = keyedLookup (memoryStateToKeyed proj state race) id := by
  have hfnExtra : (miriMSExtraFnTable state).contains id.value = false := by
    rw [Miri.Memory.KeyedArray.contains_rows]
    change (state.extraFnPtrIds.map (fun x => x.value)).contains id.value = false
    rw [hcore.noExtraFnPtrs]; simp
  have hva : (miriMSVaListTable state).contains id.value = false := by
    rw [Miri.Memory.KeyedArray.contains_rows]
    change (state.vaListIds.map (fun x => x.value)).contains id.value = false
    rw [hcore.noVaLists]; simp
  have hhasFn : state.hasFunctionPointer id =
      match state.globals.toList.find? (fun g => g.allocId == id) with
      | some g => g.kind == .function
      | none => false := by
    unfold Miri.Memory.MemoryState.hasFunctionPointer
    change ((miriMSExtraFnTable state).contains id.value ||
      (miriMSGlobalTable state).any? id.value (fun entry => entry.kind == .function)) = _
    rw [hfnExtra, Bool.false_or, keyedArray_any?_eq_list_any]
    have hcongr : state.globals.toList.any
        (fun g => g.allocId.value == id.value && g.kind == .function) =
        state.globals.toList.any (fun g => g.allocId == id && g.kind == .function) := by
      congr 1; funext g; rw [allocId_value_beq]
    change state.globals.toList.any
        (fun g => g.allocId.value == id.value && g.kind == .function) = _
    rw [hcongr]
    exact any_eq_find?_kind_of_nodup state.globals.toList hglobNd id
  have hkwInfo : (memoryStateToKeyed proj state race).getAllocInfo (ofMiriAllocId id) =
      ((memoryStateToRows state).toKeyed proj).getAllocInfo (ofMiriAllocId id) := by
    unfold memoryStateToKeyed memoryStateToLinear MiriAllocRows.toKeyed
      KeyedAllocWorld.getAllocInfo KeyedAllocWorld.findLive? KeyedAllocWorld.findGlobal?
      KeyedAllocWorld.findDead? KeyedAllocWorld.ofLinear
    rfl
  unfold keyedLookup
  rw [hkwInfo, toKeyed_getAllocInfo]
  unfold Miri.Memory.MemoryState.getAllocInfo
  have hliveEq : state.live.find? (fun entry => entry.1 == id) =
      state.live.toList.find? (fun entry => entry.1 == id) := by
    rw [← Array.find?_toList]
  have hdeadEq : state.dead.find? (fun entry => entry.allocId == id) =
      state.dead.toList.find? (fun entry => entry.allocId == id) := by
    rw [← Array.find?_toList]
  simp only [memoryStateToRows, hliveEq, hdeadEq, hhasFn, memoryState_findGlobal?_eq_list_find?,
    hva, Bool.false_eq_true, ↓reduceIte]
  cases hl : state.live.toList.find? (fun entry => entry.1 == id) with
  | some row =>
    have hmem : row ∈ state.live.toList := List.mem_of_find?_eq_some hl
    have hlt : row.2.allocation.align.pow2 < 256 := halign.liveAlignLt row hmem
    simp only [allocInfoToMiri, infoKindToMiri, mutabilityToMiri_ofMiri, pure, Except.pure]
    have hal : Miri.ABI.Align.mk (UInt8.ofNat row.2.allocation.align.pow2).toNat =
        row.2.allocation.align := by
      rcases h_al : row.2.allocation.align with ⟨p⟩
      rw [h_al] at hlt
      dsimp only at hlt ⊢
      have hmod : (UInt8.ofNat p).toNat = p % 256 := by simp [UInt8.ofNat, UInt8.toNat]
      rw [hmod, Nat.mod_eq_of_lt hlt]
    have hsz : Miri.ABI.Size.ofBytes row.2.allocation.byteSize.bytes =
        row.2.allocation.byteSize := rfl
    rw [hal, hsz]
  | none =>
    cases hg : state.globals.toList.find? (fun g => g.allocId == id) with
    | some g =>
      have hmem : g ∈ state.globals.toList := List.mem_of_find?_eq_some hg
      have hlt : g.align.pow2 < 256 := halign.globalAlignLt g hmem
      have hal : Miri.ABI.Align.mk (g.align.pow2 % 256) = g.align := by
        rcases h_al : g.align with ⟨p⟩
        rw [h_al] at hlt
        dsimp only at hlt
        rw [Nat.mod_eq_of_lt hlt]
      cases hgk : g.kind with
      | function | typeId =>
        simp [allocInfoToMiri, globalEntryOfMiri, GlobalAllocEntry.toAllocInfo,
          globalKindOfMiri, infoKindToMiri, mutabilityToMiri,
          Miri.ABI.Size.ZERO, Miri.ABI.Size.ofBytes, Miri.ABI.Align.ONE,
          pure, Except.pure, hgk]
      | vtable =>
        simp [allocInfoToMiri, globalEntryOfMiri, GlobalAllocEntry.toAllocInfo,
          globalKindOfMiri, infoKindToMiri, mutabilityToMiri,
          Miri.ABI.Size.ZERO, Miri.ABI.Size.ofBytes,
          pure, Except.pure, hgk, hal]
      | static | memory =>
        simp [allocInfoToMiri, globalEntryOfMiri, GlobalAllocEntry.toAllocInfo,
          globalKindOfMiri, infoKindToMiri, mutabilityToMiri_ofMiri,
          Miri.ABI.Size.ofBytes, pure, Except.pure, hgk, hal]
    | none =>
      cases hd : state.dead.toList.find? (fun entry => entry.allocId == id) with
      | some d =>
        have hmem : d ∈ state.dead.toList := List.mem_of_find?_eq_some hd
        have hlt : d.align.pow2 < 256 := halign.deadAlignLt d hmem
        simp only [allocInfoToMiri, infoKindToMiri, mutabilityToMiri, pure, Except.pure,
          Bool.false_eq_true, ↓reduceIte]
        have hal : Miri.ABI.Align.mk (UInt8.ofNat d.align.pow2).toNat = d.align := by
          rcases h_al : d.align with ⟨p⟩
          rw [h_al] at hlt
          dsimp only at hlt ⊢
          have hmod : (UInt8.ofNat p).toNat = p % 256 := by simp [UInt8.ofNat, UInt8.toNat]
          rw [hmod, Nat.mod_eq_of_lt hlt]
        have hsz : Miri.ABI.Size.ofBytes d.size.bytes = d.size := rfl
        rw [hal, hsz]
      | none =>
        rfl

/-- **`MemoryState.getLiveAllocSizeAndAlign` correspondence**: exact agreement on live locals,
globals, tombstones (`.useAfterFree`), and absent IDs (`.unavailable`). -/
theorem memoryState_getLiveAllocSizeAndAlign_eq_keyed (proj : RowProjection Prov Extra MachineKind)
    (state : Miri.Memory.MemoryState Prov Extra MachineKind)
    (hcore : MemoryStateCoreDomain state)
    (hglobNd : MemoryStateGlobalsDistinct state)
    (halign : MemoryStateAlignFit state)
    (id : Miri.Memory.AllocId) (msg : Miri.Memory.CheckInAllocMsg)
    (race : List (MiriAllocId × RaceClockEntry) := []) :
    state.getLiveAllocSizeAndAlign id msg =
      match (memoryStateToKeyed proj state race).getLiveAllocSizeAndAlign (ofMiriAllocId id) with
      | .ok (sz, al) => .ok (Miri.ABI.Size.ofBytes sz, ⟨al.toNat⟩)
      | .error (.unavailable _) => .error (.lookup (.unavailable id))
      | .error (.useAfterFree _) => .error (.useAfterFree id msg) := by
  unfold Miri.Memory.MemoryState.getLiveAllocSizeAndAlign KeyedAllocWorld.getLiveAllocSizeAndAlign
  rw [memoryState_getAllocInfo_eq_keyed proj state hcore hglobNd halign id race]
  unfold keyedLookup
  cases hinfo : (memoryStateToKeyed proj state race).getAllocInfo (ofMiriAllocId id) with
  | none => rfl
  | some info =>
    cases hk : info.kind <;>
      simp [allocInfoToMiri, infoKindToMiri, Except.mapError, bind, Except.bind,
        pure, Except.pure, throw, throwThe, MonadExceptOf.throw, hk]

/-- **End-to-end `Miri.Memory.checkPtrAccess` against a live `Miri.Memory.MemoryState`**:
no `MiriAllocRows` stand-in — the real `state.getAllocInfo` passes `checkPtrAccess` iff
`(memoryStateToKeyed proj state race).checkPtrAccess` holds. -/
theorem memoryState_checkPtrAccess_isOk_eq_keyed {ProvExtra : Type}
    (proj : RowProjection Prov Extra MachineKind)
    (state : Miri.Memory.MemoryState Prov Extra MachineKind)
    (hcore : MemoryStateCoreDomain state)
    (hglobNd : MemoryStateGlobalsDistinct state)
    (halign : MemoryStateAlignFit state)
    (target : Miri.Memory.PointerArithmetic) (ptr : Miri.Memory.Pointer (Option Prov))
    (size : Miri.ABI.Size) (msg : Miri.Memory.CheckInAllocMsg)
    (resolve : Miri.Memory.PointerResolver Prov ProvExtra)
    (prov : Option (MiriAllocId × UInt64)) (hres : ResolvesAs resolve ptr prov)
    (race : List (MiriAllocId × RaceClockEntry) := []) :
    (Miri.Memory.checkPtrAccess target ptr size msg resolve state.getAllocInfo).isOk =
      (memoryStateToKeyed proj state race).checkPtrAccess prov size.bytes.toNat := by
  have hlookup : state.getAllocInfo = keyedLookup (memoryStateToKeyed proj state race) := by
    funext id
    exact memoryState_getAllocInfo_eq_keyed proj state hcore hglobNd halign id race
  rw [hlookup]
  exact checkPtrAccess_isOk_eq_keyed target ptr size msg resolve _ prov hres

/-- **Permutation invariance on real `Miri.Memory.MemoryState`**: reordering distinct-key rows
of `live`, `dead`, `globals`, or `issuedIds` leaves `memoryStateToKeyed` PROPOSITIONALLY
IDENTICAL (`KeyedAllocWorld.ext`). -/
theorem memoryState_toKeyed_eq_of_perm (proj : RowProjection Prov Extra MachineKind)
    {s₁ s₂ : Miri.Memory.MemoryState Prov Extra MachineKind}
    (hnext : s₁.nextAllocId = s₂.nextAllocId)
    (hexh : s₁.idSupplyExhausted = s₂.idSupplyExhausted)
    (hiss : s₁.issuedIds.toList.Perm s₂.issuedIds.toList)
    (hglob : s₁.globals.toList.Perm s₂.globals.toList)
    (hglobNd : (s₁.globals.toList.map fun g => g.allocId).Nodup)
    (hlive : s₁.live.toList.Perm s₂.live.toList)
    (hliveNd : (s₁.live.toList.map fun row => row.1).Nodup)
    (hdead : s₁.dead.toList.Perm s₂.dead.toList)
    (hdeadNd : (s₁.dead.toList.map fun d => d.allocId).Nodup)
    {race₁ race₂ : List (MiriAllocId × RaceClockEntry)}
    (hrace : race₁.Perm race₂) (hraceNd : (race₁.map Prod.fst).Nodup) :
    memoryStateToKeyed proj s₁ race₁ = memoryStateToKeyed proj s₂ race₂ := by
  unfold memoryStateToKeyed memoryStateToLinear
  apply keyedOfLinear_eq_of_perm hnext hexh (hiss.map _) (hglob.map _) _ (hlive.map _) _
    (hdead.map _) _ hrace hraceNd
  · show ((s₁.globals.toList.map fun g =>
        (ofMiriAllocId g.allocId, globalEntryOfMiri proj g)).map Prod.fst).Nodup
    rw [List.map_map]; exact nodup_map_ofMiri s₁.globals.toList (fun g => g.allocId) hglobNd
  · show ((s₁.live.toList.map fun row =>
        (ofMiriAllocId row.1, liveEntryOfMiri proj row.2)).map Prod.fst).Nodup
    rw [List.map_map]; exact nodup_map_ofMiri s₁.live.toList (fun row => row.1) hliveNd
  · show ((s₁.dead.toList.map fun d =>
        (ofMiriAllocId d.allocId, deadEntryOfMiri d)).map Prod.fst).Nodup
    rw [List.map_map]; exact nodup_map_ofMiri s₁.dead.toList (fun d => d.allocId) hdeadNd

private theorem memoryState_containsId_eq (proj : RowProjection Prov Extra MachineKind)
    (state : Miri.Memory.MemoryState Prov Extra MachineKind)
    (id : Miri.Memory.AllocId) (race : List (MiriAllocId × RaceClockEntry)) :
    miriMSContainsId state id =
      ((memoryStateToKeyed proj state race).hasIssued (ofMiriAllocId id) ||
        (memoryStateToKeyed proj state race).containsId (ofMiriAllocId id)) := by
  have h1 : (miriMSIssuedTable state).contains id.value =
      (memoryStateToKeyed proj state race).hasIssued (ofMiriAllocId id) := by
    change state.hasIssuedId id = _
    rw [memoryState_hasIssuedId_eq_any]
    have hkw : (memoryStateToKeyed proj state race).hasIssued (ofMiriAllocId id) =
        ((memoryStateToRows state).toKeyed proj).hasIssued (ofMiriAllocId id) := rfl
    rw [hkw, toKeyed_hasIssued]; rfl
  have h2 : state.live.any (fun entry => entry.1 == id) =
      ((memoryStateToKeyed proj state race).findLive? (ofMiriAllocId id)).isSome := by
    have hkw : (memoryStateToKeyed proj state race).findLive? (ofMiriAllocId id) =
        ((memoryStateToRows state).toKeyed proj).findLive? (ofMiriAllocId id) := rfl
    rw [hkw, toKeyed_findLive?, isSome_map_find?, ← Array.any_toList]; rfl
  have h3 : state.dead.any (fun entry => entry.allocId == id) =
      ((memoryStateToKeyed proj state race).findDead? (ofMiriAllocId id)).isSome := by
    have hkw : (memoryStateToKeyed proj state race).findDead? (ofMiriAllocId id) =
        ((memoryStateToRows state).toKeyed proj).findDead? (ofMiriAllocId id) := rfl
    rw [hkw, toKeyed_findDead?, isSome_map_find?, ← Array.any_toList]; rfl
  have h4 : (miriMSGlobalTable state).contains id.value =
      ((memoryStateToKeyed proj state race).findGlobal? (ofMiriAllocId id)).isSome := by
    change state.hasGlobalId id = _
    rw [memoryState_hasGlobalId_eq_any]
    have hkw : (memoryStateToKeyed proj state race).findGlobal? (ofMiriAllocId id) =
        ((memoryStateToRows state).toKeyed proj).findGlobal? (ofMiriAllocId id) := rfl
    rw [hkw, toKeyed_findGlobal?, isSome_map_find?]; rfl
  change ((miriMSIssuedTable state).contains id.value ||
    state.live.any (fun entry => entry.1 == id) ||
    state.dead.any (fun entry => entry.allocId == id) ||
    (miriMSGlobalTable state).contains id.value) = _
  unfold KeyedAllocWorld.containsId
  rw [h1, h2, h3, h4]
  cases (memoryStateToKeyed proj state race).hasIssued (ofMiriAllocId id) <;>
  cases ((memoryStateToKeyed proj state race).findLive? (ofMiriAllocId id)).isSome <;>
  cases ((memoryStateToKeyed proj state race).findDead? (ofMiriAllocId id)).isSome <;>
  cases ((memoryStateToKeyed proj state race).findGlobal? (ofMiriAllocId id)).isSome <;> rfl

/-- **`MemoryState.reserveAllocId` lockstep**: when `sourceAllocIdWorldActive = false`,
vendored `MemoryState.reserveAllocId` transitions the keyed world and outcome in exact
lockstep with `KeyedAllocWorld.reserveAllocId` across all four paths (already exhausted,
wrapping to `0` sentinel, `alreadyIssued` collision with cursor advance, and fresh ID). -/
theorem memoryState_reserveAllocId_eq_keyed (proj : RowProjection Prov Extra MachineKind)
    (state : Miri.Memory.MemoryState Prov Extra MachineKind)
    (hnosrc : state.sourceAllocIdWorldActive = false)
    (race : List (MiriAllocId × RaceClockEntry) := []) :
    let (state', mres) := state.reserveAllocId
    let (kw', kres) := (memoryStateToKeyed proj state race).reserveAllocId
    memoryStateToKeyed proj state' race = kw' ∧
    (mres.map ofMiriAllocId).mapError allocIdErrOfMiri = kres := by
  dsimp only
  unfold Miri.Memory.MemoryState.reserveAllocId KeyedAllocWorld.reserveAllocId
  have hnext : (memoryStateToKeyed proj state race).nextAllocId = state.nextAllocId := rfl
  have hexh : (memoryStateToKeyed proj state race).idSupplyExhausted = state.idSupplyExhausted := rfl
  rw [hnext, hexh]
  cases he : state.idSupplyExhausted with
  | true =>
    simp [Id.run, pure, Pure.pure, Except.map, Except.mapError, allocIdErrOfMiri]
  | false =>
    simp only [hnosrc, Bool.false_and, Bool.false_or, Bool.false_eq_true, ↓reduceIte, Id.run, pure, Pure.pure]
    have hof := allocId_ofUInt64_comm state.nextAllocId
    cases hmk : Miri.Memory.AllocId.ofUInt64 state.nextAllocId with
    | none =>
      rw [hmk] at hof
      simp only [Option.map_none] at hof
      rw [← hof]
      refine ⟨?_, rfl⟩
      apply KeyedAllocWorld.ext
      · rfl
      · rfl
      · intro _; rfl
      · intro _; rfl
      · intro _; rfl
      · intro _; rfl
      · intro _; rfl
    | some allocId =>
      rw [hmk] at hof
      simp only [Option.map_some] at hof
      rw [← hof]
      have hcont := memoryState_containsId_eq proj state allocId race
      cases hc : miriMSContainsId state allocId with
      | true =>
        rw [hc] at hcont
        simp only [hc, ← hcont, ↓reduceIte]
        refine ⟨?_, rfl⟩
        apply KeyedAllocWorld.ext
        · rfl
        · rfl
        · intro _; rfl
        · intro _; rfl
        · intro _; rfl
        · intro _; rfl
        · intro _; rfl
      | false =>
        rw [hc] at hcont
        simp only [hc, ← hcont, Bool.false_eq_true, ↓reduceIte]
        refine ⟨?_, rfl⟩
        apply KeyedAllocWorld.ext
        · rfl
        · rfl
        · intro q
          change (ofLinearIssued (((miriMSIssuedTable state).push allocId).toArray.toList.map
              ofMiriAllocId)).contains q =
            ((ofLinearIssued (state.issuedIds.toList.map ofMiriAllocId)).insert
              (ofMiriAllocId allocId) ()).contains q
          have hpush : ((miriMSIssuedTable state).push allocId).toArray.toList =
              state.issuedIds.toList ++ [allocId] := by
            show ((miriKARows (miriMSIssuedTable state)).push allocId).toList = _
            rw [Array.toList_push]; rfl
          rw [hpush, List.map_append, List.map_singleton]
          simp only [ExtTreeMap0.contains_eq_isSome_get?, isSome_get?_ofLinearIssued,
            List.any_append, List.any_cons, List.any_nil, Bool.or_false]
          by_cases hq : q = ofMiriAllocId allocId
          · subst hq
            rw [ExtTreeMap0.get?_insert_self, beq_self_eq_true, Bool.or_true]; rfl
          · rw [ExtTreeMap0.get?_insert_ne _ _ hq, isSome_get?_ofLinearIssued]
            have hneq : (ofMiriAllocId allocId == q) = false :=
              beq_false_of_ne (fun h => hq h.symm)
            rw [hneq, Bool.or_false]
        · intro _; rfl
        · intro _; rfl
        · intro _; rfl
        · intro _; rfl

private theorem insertLive_toKeyed (proj : RowProjection Prov Extra MachineKind)
    (state : Miri.Memory.MemoryState Prov Extra MachineKind)
    (id : Miri.Memory.AllocId) (entry : Miri.Memory.LocalAllocation Prov Extra MachineKind)
    (race : List (MiriAllocId × RaceClockEntry)) :
    memoryStateToKeyed proj (miriMSInsertLive state id entry) race =
      (memoryStateToKeyed proj state race).insertLive (ofMiriAllocId id) (liveEntryOfMiri proj entry) := by
  apply KeyedAllocWorld.ext
  · rfl
  · rfl
  · intro _; rfl
  · intro _; rfl
  · intro q
    unfold memoryStateToKeyed memoryStateToLinear KeyedAllocWorld.ofLinear
      KeyedAllocWorld.insertLive KeyedAllocWorld.findLive?
    dsimp only [MiriAllocRows.toLinear, memoryStateToRows]
    rw [get?_ofLinearRows]
    change linearFind? (((state.live.filter fun old => old.1 != id).push (id, entry)).toList.map
        fun row => (ofMiriAllocId row.1, liveEntryOfMiri proj row.2)) q =
      ((ofLinearRows (state.live.toList.map fun row =>
        (ofMiriAllocId row.1, liveEntryOfMiri proj row.2))).insert (ofMiriAllocId id)
        (liveEntryOfMiri proj entry)).get? q
    rw [Array.toList_push, List.map_append, List.map_singleton, Array.toList_filter]
    have hfilt : (state.live.toList.filter fun old => old.1 != id).map
        (fun row => (ofMiriAllocId row.1, liveEntryOfMiri proj row.2)) =
        (state.live.toList.map fun row =>
          (ofMiriAllocId row.1, liveEntryOfMiri proj row.2)).filter
          (fun p => p.1 != ofMiriAllocId id) := by
      rw [List.filter_map]
      congr 1; apply congrArg (List.filter · _); funext row
      simp only [Function.comp_apply, bne, ofMiriAllocId_beq]
    rw [hfilt, linearFind?_filter_append_single]
    by_cases hq : q = ofMiriAllocId id
    · subst hq; rw [beq_self_eq_true, ExtTreeMap0.get?_insert_self]; rfl
    · rw [beq_false_of_ne hq, ExtTreeMap0.get?_insert_ne _ _ hq, get?_ofLinearRows]; rfl
  · intro _; rfl
  · intro _; rfl

private theorem removeLive_toKeyed (proj : RowProjection Prov Extra MachineKind)
    (state : Miri.Memory.MemoryState Prov Extra MachineKind)
    (id : Miri.Memory.AllocId) (race : List (MiriAllocId × RaceClockEntry)) :
    memoryStateToKeyed proj (miriMSRemoveLive state id).1 race =
      ((memoryStateToKeyed proj state race).removeLive (ofMiriAllocId id)).1 ∧
    (miriMSRemoveLive state id).2.map (liveEntryOfMiri proj) =
      ((memoryStateToKeyed proj state race).removeLive (ofMiriAllocId id)).2 := by
  have hfind : (miriMSRemoveLive state id).2.map (liveEntryOfMiri proj) =
      (memoryStateToKeyed proj state race).findLive? (ofMiriAllocId id) := by
    have hkw : (memoryStateToKeyed proj state race).findLive? (ofMiriAllocId id) =
        ((memoryStateToRows state).toKeyed proj).findLive? (ofMiriAllocId id) := rfl
    rw [hkw, toKeyed_findLive?]
    show ((state.live.find? fun entry => entry.1 == id).map Prod.snd).map (liveEntryOfMiri proj) = _
    rw [← Array.find?_toList, Option.map_map]; rfl
  refine ⟨?_, ?_⟩
  · apply KeyedAllocWorld.ext
    · unfold KeyedAllocWorld.removeLive; cases (memoryStateToKeyed proj state race).findLive? (ofMiriAllocId id) <;> rfl
    · unfold KeyedAllocWorld.removeLive; cases (memoryStateToKeyed proj state race).findLive? (ofMiriAllocId id) <;> rfl
    · intro _; unfold KeyedAllocWorld.removeLive; cases (memoryStateToKeyed proj state race).findLive? (ofMiriAllocId id) <;> rfl
    · intro _; unfold KeyedAllocWorld.removeLive; cases (memoryStateToKeyed proj state race).findLive? (ofMiriAllocId id) <;> rfl
    · intro q
      have hlhs : (memoryStateToKeyed proj (miriMSRemoveLive state id).1 race).findLive? q =
          if q == ofMiriAllocId id then none
          else (memoryStateToKeyed proj state race).findLive? q := by
        unfold memoryStateToKeyed memoryStateToLinear KeyedAllocWorld.ofLinear
          KeyedAllocWorld.findLive?
        dsimp only [MiriAllocRows.toLinear, memoryStateToRows]
        rw [get?_ofLinearRows, get?_ofLinearRows]
        change linearFind? ((state.live.filter fun old => old.1 != id).toList.map
            fun row => (ofMiriAllocId row.1, liveEntryOfMiri proj row.2)) q = _
        rw [Array.toList_filter]
        have hfilt : (state.live.toList.filter fun old => old.1 != id).map
            (fun row => (ofMiriAllocId row.1, liveEntryOfMiri proj row.2)) =
            (state.live.toList.map fun row =>
              (ofMiriAllocId row.1, liveEntryOfMiri proj row.2)).filter
              (fun p => p.1 != ofMiriAllocId id) := by
          rw [List.filter_map]; congr 1; apply congrArg (List.filter · _); funext row
          simp only [Function.comp_apply, bne, ofMiriAllocId_beq]
        rw [hfilt, linearFind?_filter_ne]
      rw [hlhs]
      unfold KeyedAllocWorld.removeLive
      cases hf : (memoryStateToKeyed proj state race).findLive? (ofMiriAllocId id) with
      | none =>
        by_cases hq : q = ofMiriAllocId id
        · subst hq; simp [hf]
        · simp [beq_false_of_ne hq]
      | some _ =>
        by_cases hq : q = ofMiriAllocId id
        · subst hq
          simp only [beq_self_eq_true, ↓reduceIte, KeyedAllocWorld.findLive?,
            ExtTreeMap0.get?_erase_self]
        · simp only [beq_false_of_ne hq, Bool.false_eq_true, ↓reduceIte,
            KeyedAllocWorld.findLive?]
          rw [ExtTreeMap0.get?_erase_ne _ hq]
    · intro _; unfold KeyedAllocWorld.removeLive; cases (memoryStateToKeyed proj state race).findLive? (ofMiriAllocId id) <;> rfl
    · intro _; unfold KeyedAllocWorld.removeLive; cases (memoryStateToKeyed proj state race).findLive? (ofMiriAllocId id) <;> rfl
  · unfold KeyedAllocWorld.removeLive
    rw [hfind]
    cases (memoryStateToKeyed proj state race).findLive? (ofMiriAllocId id) <;> rfl

private theorem insertDead_toKeyed (proj : RowProjection Prov Extra MachineKind)
    (state : Miri.Memory.MemoryState Prov Extra MachineKind)
    (d : Miri.Memory.DeadAllocation) (race : List (MiriAllocId × RaceClockEntry)) :
    memoryStateToKeyed proj (miriMSInsertDead state d) race =
      (memoryStateToKeyed proj state race).insertDead (ofMiriAllocId d.allocId) (deadEntryOfMiri d) := by
  apply KeyedAllocWorld.ext
  · rfl
  · rfl
  · intro _; rfl
  · intro _; rfl
  · intro _; rfl
  · intro q
    unfold memoryStateToKeyed memoryStateToLinear KeyedAllocWorld.ofLinear
      KeyedAllocWorld.insertDead KeyedAllocWorld.findDead?
    dsimp only [MiriAllocRows.toLinear, memoryStateToRows]
    rw [get?_ofLinearRows]
    change linearFind? (((state.dead.filter fun old => old.allocId != d.allocId).push d).toList.map
        fun x => (ofMiriAllocId x.allocId, deadEntryOfMiri x)) q =
      ((ofLinearRows (state.dead.toList.map fun x =>
        (ofMiriAllocId x.allocId, deadEntryOfMiri x))).insert (ofMiriAllocId d.allocId)
        (deadEntryOfMiri d)).get? q
    rw [Array.toList_push, List.map_append, List.map_singleton, Array.toList_filter]
    have hfilt : (state.dead.toList.filter fun old => old.allocId != d.allocId).map
        (fun x => (ofMiriAllocId x.allocId, deadEntryOfMiri x)) =
        (state.dead.toList.map fun x =>
          (ofMiriAllocId x.allocId, deadEntryOfMiri x)).filter
          (fun p => p.1 != ofMiriAllocId d.allocId) := by
      rw [List.filter_map]; congr 1; apply congrArg (List.filter · _); funext x
      simp only [Function.comp_apply, bne, ofMiriAllocId_beq]
    rw [hfilt, linearFind?_filter_append_single]
    by_cases hq : q = ofMiriAllocId d.allocId
    · subst hq; rw [beq_self_eq_true, ExtTreeMap0.get?_insert_self]; rfl
    · rw [beq_false_of_ne hq, ExtTreeMap0.get?_insert_ne _ _ hq, get?_ofLinearRows]; rfl
  · intro _; rfl

/-- **`MemoryLifecycle.insertAllocation` lockstep**: when size fits `maximumObjectSize`,
`globalKind ≠ some kind`, `sourceAllocIdWorldActive = false`, and the machine extra/root hooks
succeed without mutating memory, vendored `MemoryLifecycle.insertAllocation` transitions
`memoryStateToKeyed` identically to `KeyedAllocWorld.allocate`. -/
theorem memoryState_insertAllocation_eq_keyed [DecidableEq MachineKind] {HookState : Type}
    (proj : RowProjection Prov Extra MachineKind)
    (memory : Miri.Memory.MemoryState Prov Extra MachineKind) (hooksState : HookState)
    (syncMem : Miri.Memory.MemoryState Prov Extra MachineKind → HookState → HookState)
    (allocation : Miri.Memory.Allocation Prov Unit) (kind : Miri.Memory.MemoryKind MachineKind)
    (maxSize : Miri.ABI.Size) (globalKind : Option (Miri.Memory.MemoryKind MachineKind))
    (initExtra : Miri.Memory.MemoryState Prov Extra MachineKind → HookState → Miri.Memory.AllocId →
      Miri.Memory.MemoryKind MachineKind → Miri.ABI.Size → Miri.ABI.Align →
      Miri.Memory.MemoryStateHookResult Prov Extra MachineKind HookState Extra)
    (adjustRoot : Miri.Memory.MemoryState Prov Extra MachineKind → HookState → Miri.Memory.AllocId →
      Miri.Memory.MemoryKind MachineKind →
      Miri.Memory.MemoryStateHookResult Prov Extra MachineKind HookState (Miri.Memory.Pointer Prov))
    (hnosrc : memory.sourceAllocIdWorldActive = false)
    (hfit : ¬ allocation.byteSize.bytes > maxSize.bytes)
    (hnotGlob : globalKind ≠ some kind)
    (extra : Extra) (rootPtr : Miri.Memory.Pointer Prov)
    (hinit : ∀ m s id,
      (initExtra m s id kind allocation.byteSize allocation.align).memory = m ∧
      (initExtra m s id kind allocation.byteSize allocation.align).outcome = .ok extra)
    (hadj : ∀ m s id,
      (adjustRoot m s id kind).memory = m ∧
      (adjustRoot m s id kind).outcome = .ok rootPtr)
    (race : List (MiriAllocId × RaceClockEntry) := []) :
    let mres := Miri.Memory.MemoryLifecycle.insertAllocation memory hooksState syncMem
      allocation kind maxSize globalKind initExtra adjustRoot
    let entry := liveEntryOfMiri proj ⟨kind, allocation.withExtra extra⟩
    let (kw', kres) := (memoryStateToKeyed proj memory race).allocate entry
    memoryStateToKeyed proj mres.memory race = kw' ∧
    (match mres.outcome, kres with
     | .ok p, .ok _ => p = rootPtr
     | .error (.allocationIdError me), .error ke => allocIdErrOfMiri me = ke
     | _, _ => False) := by
  dsimp only
  have hres := memoryState_reserveAllocId_eq_keyed proj memory hnosrc race
  unfold Miri.Memory.MemoryLifecycle.insertAllocation KeyedAllocWorld.allocate
  simp only [Id.run, pure, Pure.pure, bind, Bind.bind, hfit, ↓reduceIte]
  cases hm : memory.reserveAllocId with
  | mk resMem resOut =>
    rw [hm] at hres
    cases hk : (memoryStateToKeyed proj memory race).reserveAllocId with
    | mk kw1 kout =>
      rw [hk] at hres
      rcases hres with ⟨hkw1, hout⟩
      cases resOut with
      | error me =>
        simp only [Except.map, Except.mapError] at hout
        rw [← hout]
        exact ⟨hkw1, rfl⟩
      | ok id =>
        simp only [Except.map, Except.mapError] at hout
        rw [← hout]
        simp only [hnotGlob, ↓reduceIte]
        have h1 := hinit resMem (syncMem resMem (syncMem memory hooksState)) id
        have hunf : miriMLInsertWithId resMem (syncMem memory hooksState) syncMem id allocation kind
            globalKind initExtra adjustRoot =
            (let initialized := initExtra resMem (syncMem resMem (syncMem memory hooksState)) id kind
              allocation.byteSize allocation.align
             let initializedState := syncMem initialized.memory initialized.state
             match initialized.outcome with
             | .ok ex =>
               let inserted := miriMSInsertLive initialized.memory id ⟨kind, allocation.withExtra ex⟩
               let root := adjustRoot inserted (syncMem inserted initializedState) id kind
               let rootState := syncMem root.memory root.state
               match root.outcome with
               | .error msg => ⟨root.memory, rootState, .error (.hookFailure "adjustAllocRootPointer" msg)⟩
               | .ok ptr => ⟨root.memory, rootState, .ok ptr⟩
             | .error msg =>
               ⟨initialized.memory, initializedState, .error (.hookFailure "initLocalAllocation" msg)⟩) := by
          have hdef : miriMLInsertWithId resMem (syncMem memory hooksState) syncMem id allocation kind
              globalKind initExtra adjustRoot =
              (if globalKind = some kind then
                ⟨resMem, syncMem resMem (syncMem memory hooksState), .error .dynamicallyAllocatingGlobal⟩
               else
                let initialized := initExtra resMem (syncMem resMem (syncMem memory hooksState)) id kind
                  allocation.byteSize allocation.align
                let initializedState := syncMem initialized.memory initialized.state
                match initialized.outcome with
                | .ok ex =>
                  let inserted := miriMSInsertLive initialized.memory id ⟨kind, allocation.withExtra ex⟩
                  let root := adjustRoot inserted (syncMem inserted initializedState) id kind
                  let rootState := syncMem root.memory root.state
                  match root.outcome with
                  | .error msg => ⟨root.memory, rootState, .error (.hookFailure "adjustAllocRootPointer" msg)⟩
                  | .ok ptr => ⟨root.memory, rootState, .ok ptr⟩
                | .error msg =>
                  ⟨initialized.memory, initializedState, .error (.hookFailure "initLocalAllocation" msg)⟩) := rfl
          rw [hdef]
          simp only [hnotGlob, ↓reduceIte]
        rw [hunf]
        simp only [h1.1, h1.2]
        have h2 := hadj (miriMSInsertLive resMem id ⟨kind, allocation.withExtra extra⟩)
          (syncMem (miriMSInsertLive resMem id ⟨kind, allocation.withExtra extra⟩)
            (syncMem resMem (initExtra resMem (syncMem resMem (syncMem memory hooksState)) id kind
              allocation.byteSize allocation.align).state)) id
        simp only [h2.1, h2.2]
        refine ⟨?_, trivial⟩
        rw [insertLive_toKeyed, hkw1]

/-- **`MemoryLifecycle.allocatePtr` lockstep**: lifts `memoryState_insertAllocation_eq_keyed`
through `Allocation.tryNew`. -/
theorem memoryState_allocatePtr_eq_keyed [DecidableEq MachineKind] {HookState : Type}
    (proj : RowProjection Prov Extra MachineKind)
    (memory : Miri.Memory.MemoryState Prov Extra MachineKind) (hooksState : HookState)
    (syncMem : Miri.Memory.MemoryState Prov Extra MachineKind → HookState → HookState)
    (size : Miri.ABI.Size) (align : Miri.ABI.Align) (kind : Miri.Memory.MemoryKind MachineKind)
    (init : Miri.Memory.AllocInit) (maxSize : Miri.ABI.Size)
    (globalKind : Option (Miri.Memory.MemoryKind MachineKind))
    (zeroedStorage : Miri.ABI.Size → Miri.ABI.Align → Option (Array UInt8))
    (initExtra : Miri.Memory.MemoryState Prov Extra MachineKind → HookState → Miri.Memory.AllocId →
      Miri.Memory.MemoryKind MachineKind → Miri.ABI.Size → Miri.ABI.Align →
      Miri.Memory.MemoryStateHookResult Prov Extra MachineKind HookState Extra)
    (adjustRoot : Miri.Memory.MemoryState Prov Extra MachineKind → HookState → Miri.Memory.AllocId →
      Miri.Memory.MemoryKind MachineKind →
      Miri.Memory.MemoryStateHookResult Prov Extra MachineKind HookState (Miri.Memory.Pointer Prov))
    (alloc : Miri.Memory.Allocation Prov Unit)
    (htry : Miri.Memory.Allocation.tryNew (Prov := Prov) size align init zeroedStorage = .ok alloc)
    (hnosrc : memory.sourceAllocIdWorldActive = false)
    (hfit : ¬ alloc.byteSize.bytes > maxSize.bytes)
    (hnotGlob : globalKind ≠ some kind)
    (extra : Extra) (rootPtr : Miri.Memory.Pointer Prov)
    (hinit : ∀ m s id,
      (initExtra m s id kind alloc.byteSize alloc.align).memory = m ∧
      (initExtra m s id kind alloc.byteSize alloc.align).outcome = .ok extra)
    (hadj : ∀ m s id,
      (adjustRoot m s id kind).memory = m ∧
      (adjustRoot m s id kind).outcome = .ok rootPtr)
    (race : List (MiriAllocId × RaceClockEntry) := []) :
    let mres := Miri.Memory.MemoryLifecycle.allocatePtr memory hooksState syncMem
      size align kind init maxSize globalKind zeroedStorage initExtra adjustRoot
    let entry := liveEntryOfMiri proj ⟨kind, alloc.withExtra extra⟩
    let (kw', kres) := (memoryStateToKeyed proj memory race).allocate entry
    memoryStateToKeyed proj mres.memory race = kw' ∧
    (match mres.outcome, kres with
     | .ok p, .ok _ => p = rootPtr
     | .error (.allocationIdError me), .error ke => allocIdErrOfMiri me = ke
     | _, _ => False) := by
  have hred : Miri.Memory.MemoryLifecycle.allocatePtr memory hooksState syncMem
      size align kind init maxSize globalKind zeroedStorage initExtra adjustRoot =
      Miri.Memory.MemoryLifecycle.insertAllocation memory (syncMem memory hooksState) syncMem
        alloc kind maxSize globalKind initExtra adjustRoot := by
    unfold Miri.Memory.MemoryLifecycle.allocatePtr
    simp [Id.run, pure, Pure.pure, bind, Bind.bind, htry]
  dsimp only
  rw [hred]
  exact memoryState_insertAllocation_eq_keyed proj memory (syncMem memory hooksState) syncMem
    alloc kind maxSize globalKind initExtra adjustRoot hnosrc hfit hnotGlob extra rootPtr
    hinit hadj race

/-- Exact lockstep between vendored `Miri.Memory.MemoryLifecycle.deallocatePtrWith` and
`KeyedAllocWorld.deallocateWith` across ALL 10 outcome stages in exact source failure order
(`danglingPointer` → `nonzeroOffset` → `globalErr` / `useAfterFree` → `immutableAllocation` →
`memoryKindMismatch` → `layoutMismatch` → `hookFailure` → `duplicateDeadAllocation` → `ok`),
preserving detached-state retention on every post-removal failure. -/
theorem memoryState_deallocatePtrWith_eq_keyed [DecidableEq MachineKind] {HookState ProvExtra : Type}
    (proj : RowProjection Prov Extra MachineKind)
    (memory : Miri.Memory.MemoryState Prov Extra MachineKind) (hooksState : HookState)
    (pointer : Miri.Memory.Pointer (Option Prov))
    (oldSizeAndAlign : Option (Miri.ABI.Size × Miri.ABI.Align))
    (kind : Miri.Memory.MemoryKind MachineKind)
    (hooks : Miri.Memory.MemoryDeallocationHooks Prov Extra MachineKind HookState ProvExtra)
    (dptr : DeallocPtr)
    (khook : KeyedAllocWorld → MiriAllocId → LiveAllocEntry → Except String Unit)
    (hresMem : (hooks.resolvePointer memory (hooks.synchronizeMemory memory hooksState) pointer 0).memory = memory)
    (hresOut :
      match (hooks.resolvePointer memory (hooks.synchronizeMemory memory hooksState) pointer 0).outcome, dptr with
      | .error addr, .dangling daddr => addr = daddr
      | .ok (id, off, _), .provenanced kid koff => ofMiriAllocId id = kid ∧ off.bytes = koff
      | _, _ => False)
    (halignLive : ∀ row ∈ memory.live.toList, row.2.allocation.align.pow2 < 256)
    (halignReq : ∀ sz al, oldSizeAndAlign = some (sz, al) → al.pow2 < 256)
    (hkindFaithful : ∀ row ∈ memory.live.toList,
      (memKindOfMiri proj.machineKind row.2.kind == memKindOfMiri proj.machineKind kind) =
        decide (row.2.kind = kind))
    (race : List (MiriAllocId × RaceClockEntry) := [])
    (hbefore : ∀ m s alloc id pe,
      (hooks.beforeDeallocation m s alloc pointer id pe alloc.byteSize alloc.align kind).memory = m ∧
      (hooks.beforeDeallocation m s alloc pointer id pe alloc.byteSize alloc.align kind).outcome =
        khook (memoryStateToKeyed proj m race) (ofMiriAllocId id)
          (liveEntryOfMiri proj ⟨kind, alloc⟩)) :
    let mres := Miri.Memory.MemoryLifecycle.deallocatePtrWith memory hooksState pointer
      oldSizeAndAlign kind hooks
    let expLayout := oldSizeAndAlign.map fun p => (p.1.bytes, UInt8.ofNat p.2.pow2)
    let kres := (memoryStateToKeyed proj memory race).deallocateWith dptr expLayout
      (memKindOfMiri proj.machineKind kind) khook
    memoryStateToKeyed proj mres.memory race = kres.world ∧
    mres.detached.map (fun p => (ofMiriAllocId p.1, liveEntryOfMiri proj p.2)) = kres.detached ∧
    (match mres.outcome, kres.outcome with
     | .ok (), .ok () => True
     | .error me, .error ke => deallocErrOfMiri me = some ke
     | _, _ => False) := by
  dsimp only
  unfold Miri.Memory.MemoryLifecycle.deallocatePtrWith KeyedAllocWorld.deallocateWith
  simp only [Id.run, pure, Pure.pure, bind, Bind.bind]
  generalize hrv : hooks.resolvePointer memory (hooks.synchronizeMemory memory hooksState) pointer 0 = resolved at hresMem hresOut ⊢
  cases hro : resolved.outcome with
  | error addr =>
    rw [hro] at hresOut
    cases dptr with
    | provenanced _ _ => exact False.elim hresOut
    | dangling daddr =>
      subst hresOut
      exact ⟨by rw [hresMem], rfl, rfl⟩
  | ok triple =>
    rcases triple with ⟨allocId, offset, provExtra⟩
    rw [hro] at hresOut
    cases dptr with
    | dangling _ => exact False.elim hresOut
    | provenanced kid koff =>
      rcases hresOut with ⟨rfl, rfl⟩
      rw [hresMem]
      by_cases hoff : offset.bytes = 0
      · have hne : (offset.bytes != 0) = false := by simp [hoff]
        simp only [hne, Bool.false_eq_true, ↓reduceIte]
        have hrem := removeLive_toKeyed proj memory allocId race
        have hfindGlob : (memoryStateToKeyed proj memory race).findGlobal? (ofMiriAllocId allocId) =
            (memory.findGlobal? allocId).map (globalEntryOfMiri proj) := by
          have hkw : (memoryStateToKeyed proj memory race).findGlobal? (ofMiriAllocId allocId) =
              ((memoryStateToRows memory).toKeyed proj).findGlobal? (ofMiriAllocId allocId) := rfl
          rw [hkw, toKeyed_findGlobal?, memoryState_findGlobal?_eq_list_find?]; rfl
        cases hremM : miriMSRemoveLive memory allocId with
        | mk afterRemove entry? =>
          rw [hremM] at hrem
          rcases hrem with ⟨hremW, hremE⟩
          cases entry? with
          | none =>
            simp only [Option.map_none] at hremE
            rw [← hremE, hfindGlob]
            cases hfg : memory.findGlobal? allocId with
            | none => exact ⟨rfl, rfl, rfl⟩
            | some g => exact ⟨rfl, rfl, rfl⟩
          | some entry =>
            simp only [Option.map_some] at hremE
            rw [← hremE]
            have hmemEntry : ∃ row ∈ memory.live.toList, row.1 = allocId ∧ row.2 = entry := by
              have hfl : (memory.live.toList.find? fun x => x.1 == allocId).map Prod.snd = some entry := by
                have := congrArg Prod.snd hremM
                change (memory.live.find? fun x => x.1 == allocId).map Prod.snd = some entry at this
                rwa [← Array.find?_toList] at this
              cases hfind : memory.live.toList.find? fun x => x.1 == allocId with
              | none => rw [hfind] at hfl; cases hfl
              | some row =>
                rw [hfind] at hfl; injection hfl with hrow2
                exact ⟨row, List.mem_of_find?_eq_some hfind,
                  eq_of_beq (by simpa using List.find?_some hfind), hrow2⟩
            rcases hmemEntry with ⟨row, hrowMem, _, hrow2⟩
            have hmut : (entry.allocation.mutability == .Not) =
                ((liveEntryOfMiri proj entry).mutability == .not) := by
              unfold liveEntryOfMiri mutabilityOfMiri
              cases entry.allocation.mutability <;> rfl
            cases hm : entry.allocation.mutability == .Not with
            | true =>
              rw [hm] at hmut
              simp only [hm, ← hmut, ↓reduceIte]
              exact ⟨hremW, rfl, rfl⟩
            | false =>
              rw [hm] at hmut
              simp only [hm, ← hmut, Bool.false_eq_true, ↓reduceIte]
              have hkEq := hkindFaithful row hrowMem
              rw [hrow2] at hkEq
              by_cases hk : entry.kind = kind
              · have hkBne : ((liveEntryOfMiri proj entry).kind != memKindOfMiri proj.machineKind kind) = false := by
                  show (!(memKindOfMiri proj.machineKind entry.kind == memKindOfMiri proj.machineKind kind)) = false
                  rw [hkEq, decide_eq_true hk]; rfl
                simp only [hk, ne_eq, not_true_eq_false, hkBne, Bool.false_eq_true, ↓reduceIte]
                have hlayAlignLt : entry.allocation.align.pow2 < 256 := by
                  rw [← hrow2]; exact halignLive row hrowMem
                cases hold : oldSizeAndAlign with
                | none =>
                  simp only [Option.map_none, deallocLayoutMismatch?]
                  have hb := hbefore afterRemove (hooks.synchronizeMemory afterRemove
                    (hooks.synchronizeMemory memory resolved.state)) entry.allocation allocId provExtra
                  have hleKind : liveEntryOfMiri proj ⟨kind, entry.allocation⟩ = liveEntryOfMiri proj entry := by
                    cases entry with | mk ek ea => simp only at hk; subst hk; rfl
                  rw [hleKind, hremW] at hb
                  cases hbo : (hooks.beforeDeallocation afterRemove
                    (hooks.synchronizeMemory afterRemove (hooks.synchronizeMemory memory resolved.state))
                    entry.allocation pointer allocId provExtra entry.allocation.byteSize
                    entry.allocation.align kind).outcome with
                  | error msg =>
                    rw [hbo] at hb
                    simp only [← hb.2]
                    exact ⟨by rw [hb.1]; exact hremW, rfl, rfl⟩
                  | ok u =>
                    cases u
                    rw [hbo] at hb
                    simp only [← hb.2]
                    have had : (afterRemove.dead.any fun old => old.allocId == allocId) =
                        (((memoryStateToKeyed proj memory race).removeLive (ofMiriAllocId allocId)).1.findDead?
                          (ofMiriAllocId allocId)).isSome := by
                      rw [← hremW]
                      have hkw : (memoryStateToKeyed proj afterRemove race).findDead? (ofMiriAllocId allocId) =
                          ((memoryStateToRows afterRemove).toKeyed proj).findDead? (ofMiriAllocId allocId) := rfl
                      rw [hkw, toKeyed_findDead?, isSome_map_find?, ← Array.any_toList]; rfl
                    rw [hb.1, had]
                    cases (((memoryStateToKeyed proj memory race).removeLive (ofMiriAllocId allocId)).1.findDead?
                        (ofMiriAllocId allocId)).isSome with
                    | true =>
                      simp only [↓reduceIte]
                      exact ⟨by
                        rw [insertDead_toKeyed]
                        exact congrArg (fun w => w.insertDead (ofMiriAllocId allocId)
                          ⟨entry.allocation.byteSize.bytes, UInt8.ofNat entry.allocation.align.pow2⟩) hremW,
                        rfl, rfl⟩
                    | false =>
                      simp only [Bool.false_eq_true, ↓reduceIte]
                      exact ⟨by
                        rw [insertDead_toKeyed]
                        exact congrArg (fun w => w.insertDead (ofMiriAllocId allocId)
                          ⟨entry.allocation.byteSize.bytes, UInt8.ofNat entry.allocation.align.pow2⟩) hremW,
                        rfl, trivial⟩
                | some pair =>
                  rcases pair with ⟨reqSize, reqAlign⟩
                  have hreqLt := halignReq reqSize reqAlign hold
                  have hszEq : (reqSize != entry.allocation.byteSize) =
                      (reqSize.bytes != entry.allocation.byteSize.bytes) := by
                    rcases reqSize with ⟨b1⟩
                    rcases entry.allocation.byteSize with ⟨b2⟩
                    by_cases hb : b1 = b2
                    · simp [hb]
                    · have hne : ({ bytes := b1 } : Miri.ABI.Size) ≠ { bytes := b2 } :=
                        fun h => hb (congrArg Miri.ABI.Size.bytes h)
                      simp [bne_iff_ne.mpr hne, bne_iff_ne.mpr hb]
                  have halEq : (reqAlign != entry.allocation.align) =
                      (UInt8.ofNat reqAlign.pow2 != UInt8.ofNat entry.allocation.align.pow2) := by
                    by_cases ha : reqAlign.pow2 = entry.allocation.align.pow2
                    · have ha' : reqAlign = entry.allocation.align := by
                        rcases h1 : reqAlign with ⟨p1⟩
                        rcases h2 : entry.allocation.align with ⟨p2⟩
                        rw [h1, h2] at ha; simp at ha; subst ha; rfl
                      simp [ha']
                    · have ha' : reqAlign ≠ entry.allocation.align := fun h => ha (congrArg Miri.ABI.Align.pow2 h)
                      have hu : UInt8.ofNat reqAlign.pow2 ≠ UInt8.ofNat entry.allocation.align.pow2 := by
                        intro h
                        have hnat := congrArg UInt8.toNat h
                        have hm1 : (UInt8.ofNat reqAlign.pow2).toNat = reqAlign.pow2 % 256 := by
                          simp [UInt8.ofNat, UInt8.toNat]
                        have hm2 : (UInt8.ofNat entry.allocation.align.pow2).toNat =
                            entry.allocation.align.pow2 % 256 := by
                          simp [UInt8.ofNat, UInt8.toNat]
                        rw [hm1, hm2, Nat.mod_eq_of_lt hreqLt, Nat.mod_eq_of_lt hlayAlignLt] at hnat
                        exact ha hnat
                      simp [bne_iff_ne.mpr ha', bne_iff_ne.mpr hu]
                  have hdmEq : deallocLayoutMismatch? (liveEntryOfMiri proj entry)
                      (some (reqSize.bytes, UInt8.ofNat reqAlign.pow2)) =
                      if (reqSize != entry.allocation.byteSize || reqAlign != entry.allocation.align) then
                        some (reqSize.bytes, UInt8.ofNat reqAlign.pow2)
                      else none := by
                    unfold deallocLayoutMismatch? liveEntryOfMiri
                    simp only [hszEq, halEq]
                  simp only [Option.map_some, hdmEq]
                  cases hmis : (reqSize != entry.allocation.byteSize || reqAlign != entry.allocation.align) with
                  | true =>
                    simp only [↓reduceIte]
                    exact ⟨hremW, rfl, rfl⟩
                  | false =>
                    simp only [Bool.false_eq_true, ↓reduceIte]
                    have hb := hbefore afterRemove (hooks.synchronizeMemory afterRemove
                      (hooks.synchronizeMemory memory resolved.state)) entry.allocation allocId provExtra
                    have hleKind : liveEntryOfMiri proj ⟨kind, entry.allocation⟩ = liveEntryOfMiri proj entry := by
                      cases entry with | mk ek ea => simp only at hk; subst hk; rfl
                    rw [hleKind, hremW] at hb
                    cases hbo : (hooks.beforeDeallocation afterRemove
                      (hooks.synchronizeMemory afterRemove (hooks.synchronizeMemory memory resolved.state))
                      entry.allocation pointer allocId provExtra entry.allocation.byteSize
                      entry.allocation.align kind).outcome with
                    | error msg =>
                      rw [hbo] at hb
                      simp only [← hb.2]
                      exact ⟨by rw [hb.1]; exact hremW, rfl, rfl⟩
                    | ok u =>
                      cases u
                      rw [hbo] at hb
                      simp only [← hb.2]
                      have had : (afterRemove.dead.any fun old => old.allocId == allocId) =
                          (((memoryStateToKeyed proj memory race).removeLive (ofMiriAllocId allocId)).1.findDead?
                            (ofMiriAllocId allocId)).isSome := by
                        rw [← hremW]
                        have hkw : (memoryStateToKeyed proj afterRemove race).findDead? (ofMiriAllocId allocId) =
                            ((memoryStateToRows afterRemove).toKeyed proj).findDead? (ofMiriAllocId allocId) := rfl
                        rw [hkw, toKeyed_findDead?, isSome_map_find?, ← Array.any_toList]; rfl
                      rw [hb.1, had]
                      cases (((memoryStateToKeyed proj memory race).removeLive (ofMiriAllocId allocId)).1.findDead?
                          (ofMiriAllocId allocId)).isSome with
                      | true =>
                        simp only [↓reduceIte]
                        exact ⟨by
                          rw [insertDead_toKeyed]
                          exact congrArg (fun w => w.insertDead (ofMiriAllocId allocId)
                            ⟨entry.allocation.byteSize.bytes, UInt8.ofNat entry.allocation.align.pow2⟩) hremW,
                          rfl, rfl⟩
                      | false =>
                        simp only [Bool.false_eq_true, ↓reduceIte]
                        exact ⟨by
                          rw [insertDead_toKeyed]
                          exact congrArg (fun w => w.insertDead (ofMiriAllocId allocId)
                            ⟨entry.allocation.byteSize.bytes, UInt8.ofNat entry.allocation.align.pow2⟩) hremW,
                          rfl, trivial⟩
              · have hkBne : ((liveEntryOfMiri proj entry).kind != memKindOfMiri proj.machineKind kind) = true := by
                  show (!(memKindOfMiri proj.machineKind entry.kind == memKindOfMiri proj.machineKind kind)) = true
                  rw [hkEq, decide_eq_false hk]; rfl
                simp only [ne_eq, hk, not_false_eq_true, hkBne, ↓reduceIte]
                exact ⟨hremW, rfl, rfl⟩
      · have hne : (offset.bytes != 0) = true := bne_iff_ne.mpr hoff
        simp only [hne, ↓reduceIte]
        exact ⟨trivial, rfl, rfl⟩

/-- **Exact boundary of `MemoryStateGlobalsDistinct`**: when a `MemoryState` contains duplicate
global rows for the same `AllocId` (`.memory` followed by `.function`), vendored
`MemoryState.getAllocInfo` checks `hasFunctionPointer` (`globalTable.any?`) BEFORE `findGlobal?`
and reports `.function`, whereas first-match `KeyedAllocWorld.getAllocInfo` reports `.liveData`.
Thus `MemoryStateGlobalsDistinct` is not an artifact of the proof but the exact semantic condition
for `memoryState_getAllocInfo_eq_keyed`. -/
theorem memoryState_duplicateGlobal_hasFunctionPointer_separation :
    let id : Miri.Memory.AllocId := ⟨1, by decide⟩
    let gMem : Miri.Memory.GlobalAllocation :=
      ⟨id, .memory, ⟨4⟩, ⟨2⟩, .Not, none⟩
    let gFn : Miri.Memory.GlobalAllocation :=
      ⟨id, .function, Miri.ABI.Size.ZERO, Miri.ABI.Align.ONE, .Not, none⟩
    let emptyMs : Miri.Memory.MemoryState Unit Unit Unit := Miri.Memory.MemoryState.empty
    let ms : Miri.Memory.MemoryState Unit Unit Unit :=
      { emptyMs with
        globalTable := ((Miri.Memory.KeyedArray.empty (·.allocId.value)).push gMem).push gFn }
    let proj : RowProjection Unit Unit Unit := ⟨fun _ => .heap, fun _ => [], fun _ => []⟩
    (ms.getAllocInfo id).map (·.kind) = .ok .function ∧
    ((memoryStateToKeyed proj ms).getAllocInfo (ofMiriAllocId id)).map (·.kind) = some .liveData := by
  intro id gMem gFn emptyMs ms proj
  constructor
  · have hfn : ms.hasFunctionPointer id = true := by
      unfold Miri.Memory.MemoryState.hasFunctionPointer
      rw [keyedArray_any?_eq_list_any]
      have hglob : ((Miri.Memory.KeyedArray.empty (·.allocId.value)).push gMem |>.push gFn).toArray.toList.any
          (fun v => v.allocId.value == id.value && v.kind == .function) = true := rfl
      change (_ || ((Miri.Memory.KeyedArray.empty (·.allocId.value)).push gMem |>.push gFn).toArray.toList.any
          (fun v => v.allocId.value == id.value && v.kind == .function)) = true
      rw [hglob, Bool.or_true]
    have hlive : ms.live.find? (fun entry => entry.1 == id) = none := rfl
    unfold Miri.Memory.MemoryState.getAllocInfo
    simp only [hlive, hfn, ↓reduceIte, pure, Except.pure, Except.map]
  · have hkw : (memoryStateToKeyed proj ms).getAllocInfo (ofMiriAllocId id) =
        ((memoryStateToRows ms).toKeyed proj).getAllocInfo (ofMiriAllocId id) := rfl
    rw [hkw, toKeyed_getAllocInfo]
    rfl

/-- **Exact boundary of `hkindFaithful` on `MiriMemoryKind`**: vendored `MiriMemoryKind`
distinguishes `.rust` from `.c` heap allocations, whereas the 4-kind theory `AllocMemKind`
collapses both to `.heap`. Deallocating a `.machine .rust` allocation as `.machine .c` therefore
triggers `.memoryKindMismatch` in vendored `MemoryLifecycle.deallocatePtrWith` while passing the
kind check in `KeyedAllocWorld.deallocateWith`. -/
theorem memoryState_machineKind_collapse_separation :
    ∀ (alloc : Miri.Memory.Allocation Unit Unit),
      alloc.mutability = .Mut →
      let id : Miri.Memory.AllocId := ⟨1, by decide⟩
      let emptyMs : Miri.Memory.MemoryState Unit Unit Miri.Memory.MiriMemoryKind :=
        Miri.Memory.MemoryState.empty
      let ms : Miri.Memory.MemoryState Unit Unit Miri.Memory.MiriMemoryKind :=
        { emptyMs with live := #[(id, ⟨.machine .rust, alloc⟩)] }
      let proj : RowProjection Unit Unit Miri.Memory.MiriMemoryKind :=
        ⟨fun _ => .heap, fun _ => [], fun _ => []⟩
      let hooks : Miri.Memory.MemoryDeallocationHooks Unit Unit Miri.Memory.MiriMemoryKind Unit Unit :=
        { synchronizeMemory := fun _ _ => ()
          resolvePointer := fun mem _ _ _ => ⟨mem, (), .ok (id, Miri.ABI.Size.ZERO, ())⟩
          beforeDeallocation := fun mem _ _ _ _ _ _ _ _ => ⟨mem, (), .ok ()⟩ }
      (Miri.Memory.MemoryLifecycle.deallocatePtrWith ms () ⟨Miri.ABI.Size.ZERO, some ()⟩ none
        (.machine .c) hooks).outcome = .error (.memoryKindMismatch id) ∧
      ((memoryStateToKeyed proj ms).deallocateWith (.provenanced (ofMiriAllocId id) 0) none
        (memKindOfMiri proj.machineKind (.machine .c)) (fun _ _ _ => .ok ())).outcome = .ok () := by
  intro alloc hmut id emptyMs ms proj hooks
  have hrm : ms.live.find? (fun entry => entry.1 == id) = some (id, ⟨.machine .rust, alloc⟩) := rfl
  constructor
  · unfold Miri.Memory.MemoryLifecycle.deallocatePtrWith
    simp only [hooks, Id.run, pure, Pure.pure, bind, Bind.bind,
      Miri.ABI.Size.ZERO, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    have hrem : miriMSRemoveLive ms id = ({ ms with live := ms.live.filter fun old => old.1 != id },
        some ⟨.machine .rust, alloc⟩) := by
      change ({ ms with live := ms.live.filter fun old => old.1 != id },
        (ms.live.find? fun entry => entry.1 == id).map Prod.snd) = _
      rw [hrm]; rfl
    rw [hrem]
    simp [hmut]
  · unfold KeyedAllocWorld.deallocateWith
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    have hfl : (memoryStateToKeyed proj ms).findLive? (ofMiriAllocId id) =
        some (liveEntryOfMiri proj ⟨.machine .rust, alloc⟩) := by
      have h1 : (memoryStateToKeyed proj ms).findLive? (ofMiriAllocId id) =
          ((memoryStateToRows ms).toKeyed proj).findLive? (ofMiriAllocId id) := rfl
      rw [h1, toKeyed_findLive?]; rfl
    have hfd : ((memoryStateToKeyed proj ms).removeLive (ofMiriAllocId id)).1.findDead?
        (ofMiriAllocId id) = none := by
      have h1 : ((memoryStateToKeyed proj ms).removeLive (ofMiriAllocId id)).1.findDead?
          (ofMiriAllocId id) = (memoryStateToKeyed proj ms).findDead? (ofMiriAllocId id) := rfl
      rw [h1]
      have h2 : (memoryStateToKeyed proj ms).findDead? (ofMiriAllocId id) =
          ((memoryStateToRows ms).toKeyed proj).findDead? (ofMiriAllocId id) := rfl
      rw [h2, toKeyed_findDead?]; rfl
    have hremSnd : ((memoryStateToKeyed proj ms).removeLive (ofMiriAllocId id)).2 =
        some (liveEntryOfMiri proj ⟨.machine .rust, alloc⟩) := by
      unfold KeyedAllocWorld.removeLive; exact hfl
    rw [hremSnd]
    simp only [liveEntryOfMiri, mutabilityOfMiri, hmut, memKindOfMiri, proj,
      bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hfd, Option.isSome_none]
    rfl

end MemoryStateBridge

/-! ### Data-race hook (`MachineHooks.memoryRaceAccess`) & `AllocationMachine.deallocate` bridge -/

/-- When `machine.dataRace = none` (`RaceDetectorMode.unconfigured`), vendored
`Miri.Interpreter.MachineHooks.memoryRaceAccess` is an unconditional no-op matching
`machineDeallocHook .unconfigured`. -/
theorem memoryRaceAccess_unconfigured {K User : Type}
    (machine : Miri.Interpreter.MachineHooks.MachineState K User)
    (hnone : machine.dataRace = none)
    (id : Miri.Memory.AllocId) (range : Miri.Memory.AllocRange)
    (actor : DeallocActor) (clk? : Option RaceClockEntry) (sz : UInt64) :
    Miri.Interpreter.MachineHooks.memoryRaceAccess machine id range (some .Deallocate) .Read =
        (machine, .ok ()) ∧
      machineDeallocHook .unconfigured actor .ok clk? sz = .ok () := by
  refine ⟨?_, rfl⟩
  unfold Miri.Interpreter.MachineHooks.memoryRaceAccess
  simp [hnone, Id.run, pure, Pure.pure]

/-- When `machine.dataRace = some global` (`RaceDetectorMode.configured global.raceDetecting`)
and `id` has no entry in `machine.raceAllocations`, vendored `memoryRaceAccess` fails with
`"allocation missing vector-clock extra"` BEFORE checking `global.raceDetecting`, matching
`machineDeallocHook (.configured raceDetecting) _ _ none _`. -/
theorem memoryRaceAccess_missingClock_before_raceDetecting {K User : Type}
    (machine : Miri.Interpreter.MachineHooks.MachineState K User)
    (global : Miri.Concurrency.GlobalState) (hsome : machine.dataRace = some global)
    (id : Miri.Memory.AllocId)
    (hmiss : machine.raceAllocations.find? (fun entry => entry.1 == id) = none)
    (range : Miri.Memory.AllocRange) (actor : DeallocActor) (tb : DeallocHookSpec) (sz : UInt64) :
    Miri.Interpreter.MachineHooks.memoryRaceAccess machine id range (some .Deallocate) .Read =
        (machine, .error (.invalidProgram "allocation missing vector-clock extra")) ∧
      machineDeallocHook (.configured global.raceDetecting) actor tb none sz =
        .error "MissingVectorClockExtra" := by
  refine ⟨?_, rfl⟩
  unfold Miri.Interpreter.MachineHooks.memoryRaceAccess
  simp [hsome, hmiss, Id.run, pure, Pure.pure, bind, Bind.bind]

/-- When `machine.dataRace = some global` with `global.raceDetecting = false` and `id` has a
vector-clock entry, vendored `memoryRaceAccess` succeeds without checking clocks, matching
`machineDeallocHook (.configured false) actor .ok (some clk) sz`. -/
theorem memoryRaceAccess_raceDetecting_false {K User : Type}
    (machine : Miri.Interpreter.MachineHooks.MachineState K User)
    (global : Miri.Concurrency.GlobalState) (hsome : machine.dataRace = some global)
    (hoff : global.raceDetecting = false)
    (id : Miri.Memory.AllocId) (vc : Miri.Concurrency.VClockAlloc)
    (hpresent : machine.raceAllocations.find? (fun entry => entry.1 == id) = some (id, vc))
    (range : Miri.Memory.AllocRange) (actor : DeallocActor) (clk : RaceClockEntry) (sz : UInt64) :
    Miri.Interpreter.MachineHooks.memoryRaceAccess machine id range (some .Deallocate) .Read =
        (machine, .ok ()) ∧
      machineDeallocHook (.configured false) actor .ok (some clk) sz = .ok () := by
  refine ⟨?_, rfl⟩
  unfold Miri.Interpreter.MachineHooks.memoryRaceAccess
  simp [hsome, hpresent, hoff, Id.run, pure, Pure.pure, bind, Bind.bind]

/-- Zero-sized deallocation ranges never trigger a data race in vendored
`VClockAlloc.writeNonAtomic` (`runRange` takes 0 steps), matching the `sizeBytes != 0` guard of
`machineDeallocHook`. -/
theorem writeNonAtomic_zeroSize_ok (alloc : Miri.Concurrency.VClockAlloc)
    (thread : Miri.Concurrency.ThreadClockSet) (idx : Miri.Concurrency.VectorIdx)
    (start : Miri.Concurrency.ByteSize) (hstart : start.bytes ≤ alloc.allocRanges.length.bytes)
    (actor : DeallocActor) (clk : RaceClockEntry) :
    (alloc.writeNonAtomic ⟨start, Miri.Concurrency.ByteSize.ofU64 0 (by decide)⟩
        thread idx .Deallocate).result = .ok ∧
      machineDeallocHook (.configured true) actor .ok (some clk) 0 = .ok () := by
  refine ⟨?_, rfl⟩
  unfold Miri.Concurrency.VClockAlloc.writeNonAtomic Miri.Concurrency.VClockAlloc.runRange
  simp only [Miri.Concurrency.ByteSize.bytes_ofU64, Nat.add_zero, hstart, ↓reduceIte]
  rfl

/-- Single-cell non-atomic deallocation race characterization against `DeallocActor.ofVClock`:
when a cell has no atomic metadata, no prior readers (`cell.read = .default`), last writer
`(wIdx, wTs)` with `wIdx ≠ actorIdx`, and `thread.clock` records `(actor.viewFor wTid)` at `wIdx`,
vendored `MemoryCellClocks.nonAtomicWriteDetect` reports `.race` iff `hasDeallocDataRace` holds. -/
theorem nonAtomicWriteDetect_dealloc_writer_race_iff
    (cell : Miri.Concurrency.MemoryCellClocks) (thread : Miri.Concurrency.ThreadClockSet)
    (actorIdx : Miri.Concurrency.VectorIdx) (actorTid writerTid : UInt32)
    (vclock : List (UInt32 × UInt64)) (writeTs : UInt64)
    (hneTid : writerTid ≠ actorTid)
    (hnoAtomic : cell.atomicOps = none)
    (hnoRead : cell.read = .default)
    (hwt : cell.write.2.time = writeTs.toNat)
    (hview : (thread.clock.index cell.write.1).time =
      ((DeallocActor.ofVClock actorTid vclock).viewFor writerTid).toNat)
    (hwtNz : writeTs ≠ 0) :
    ((cell.nonAtomicWriteDetect thread actorIdx .Deallocate).result == .race) =
      hasDeallocDataRace (DeallocActor.ofVClock actorTid vclock)
        ⟨writerTid, writeTs, actorTid, 0, []⟩ := by
  have hreadLe : cell.read.le thread.clock = true := by
    rw [hnoRead]
    unfold Miri.Concurrency.VClock.le
    simp [Miri.Concurrency.VClock.length_zero]
    rfl
  unfold Miri.Concurrency.MemoryCellClocks.nonAtomicWriteDetect
    Miri.Concurrency.MemoryCellClocks.writeWasBefore hasDeallocDataRace
  have htid : (writerTid != (DeallocActor.ofVClock actorTid vclock).threadId) = true :=
    bne_iff_ne.mpr hneTid
  have hts : (writeTs != 0) = true := bne_iff_ne.mpr hwtNz
  have hself : (actorTid != (DeallocActor.ofVClock actorTid vclock).threadId) = false :=
    bne_self_eq_false actorTid
  simp only [hnoAtomic, Option.all_none, hreadLe, Bool.and_true, hwt, hview,
    htid, hts, hself, Bool.true_and, Bool.false_and, List.any_nil, Bool.or_false]
  by_cases hle : writeTs.toNat ≤ ((DeallocActor.ofVClock actorTid vclock).viewFor writerTid).toNat
  · have hlt : ¬ ((DeallocActor.ofVClock actorTid vclock).viewFor writerTid < writeTs) := by
      rw [UInt64.lt_iff_toNat_lt]; omega
    simp [hle, hlt]
  · have hlt : (DeallocActor.ofVClock actorTid vclock).viewFor writerTid < writeTs := by
      rw [UInt64.lt_iff_toNat_lt]; omega
    simp [hle, hlt]

local macro "miriAllocMachCallback" : term =>
  `(miri_etm_private% Miri.Interpreter.AllocationMachine Miri.Interpreter.AllocationMachine.callback)

/-- **Machine detach race-clock cleanup (`AllocationMachine.deallocate` ↔ `detachRaceClock`)**:
whenever `deallocatePtrWith` detaches `(id, entry)` (whether `outcome` is `.ok ()` or any
post-removal failure), `Miri.Interpreter.AllocationMachine.deallocate` removes `id` from
`machine.raceAllocations` — matching `detachRaceClock` in `KeyedAllocWorld.deallocateMachine`. -/
theorem allocationMachine_deallocate_detaches_race_on_postRemoval {K User Payload : Type}
    [DecidableEq K]
    (h : Miri.Interpreter.AllocationMachine.DeallocationHooks K User Payload)
    (ptr : Miri.Memory.Pointer (Option Miri.Memory.Provenance))
    (oldLayout : Option (Miri.ABI.Size × Miri.ABI.Align))
    (kind : Miri.Memory.MemoryKind K)
    (st : Miri.Interpreter.MachineHooks.State K User)
    (id : Miri.Memory.AllocId)
    (entry : Miri.Memory.LocalAllocation Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree K)
    (hdet :
      (Miri.Memory.MemoryLifecycle.deallocatePtrWith st.machine.memory ⟨st.machine, none⟩
          ptr oldLayout kind
          { synchronizeMemory := fun memory access => { access with machine := { access.machine with memory } }
            resolvePointer := h.resolvePointer
            beforeDeallocation := miriAllocMachCallback h }).detached =
        some (id, entry))
    (hnoNative : entry.allocation.nativeBuffer = none) :
    let st' :=
      match Miri.Interpreter.AllocationMachine.deallocate h ptr oldLayout kind st with
      | .ok _ s => s
      | .error _ s => s
    st'.machine.raceAllocations.find? (fun e => e.1 == id) = none := by
  dsimp only
  unfold Miri.Interpreter.AllocationMachine.deallocate
  simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind,
    modify, pure, Pure.pure, throw, throwThe, MonadExceptOf.throw]
  generalize hr :
    Miri.Memory.MemoryLifecycle.deallocatePtrWith st.machine.memory ⟨st.machine, none⟩
      ptr oldLayout kind
      { synchronizeMemory := fun memory access => { access with machine := { access.machine with memory } }
        resolvePointer := h.resolvePointer
        beforeDeallocation := miriAllocMachCallback h } = res at hdet ⊢
  rw [hdet]
  simp only [hnoNative, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
  have hfilt : ∀ (xs : Array (Miri.Memory.AllocId × Miri.Concurrency.VClockAlloc)),
      (xs.filter fun e => e.1 != id).find? (fun e => e.1 == id) = none := by
    intro xs
    rw [← Array.find?_toList, Array.toList_filter]
    cases hf : (xs.toList.filter fun e => e.1 != id).find? (fun e => e.1 == id) with
    | none => rfl
    | some x =>
      have hmem := List.mem_of_find?_eq_some hf
      have hpred := List.find?_some hf
      have hne := (List.mem_filter.mp hmem).2
      simp [bne, hpred] at hne
  cases res.outcome <;> exact hfilt _

/-! ### `KeyedStateRelLM3_1` and `KeyedStateRelLM3_2`: lifting `StateRelLM3_1` / `StateRelLM3_2` -/

/-- Classification of `Miri.Memory.MiriMemoryKind` into the 4-kind theory `AllocMemKind`. -/
def miriMemoryKindToTheory : Miri.Memory.MiriMemoryKind → AllocMemKind
  | .global | .externStatic => .global
  | _ => .heap

/-- Canonical row projection for `AnnealMemory` (`AnnealProv`, `Option BorrowTree`,
`MiriMemoryKind`), used to lift `AnnealMachine` states into `KeyedAllocWorld`. -/
def annealRowProjection :
    RowProjection AnnealProv (Option Miri.TreeBorrows.BorrowTree) Miri.Memory.MiriMemoryKind where
  machineKind := miriMemoryKindToTheory
  liveBytes := fun _ => []
  globalBytes := fun _ => []

/-- The keyed `ExtTreeMap0` allocation world of an `AnnealMachine`. -/
def annealMachineToKeyed (mach : AnnealMachine) : KeyedAllocWorld :=
  memoryStateToKeyed annealRowProjection mach.memory

/-- **`KeyedStateRelLM3_1`**: `StateRelLM3_1` paired with its canonical keyed `ExtTreeMap0`
allocation world `kw = annealMachineToKeyed m.machine`. -/
structure KeyedStateRelLM3_1 (body : Trusted.Rustc.V2026_06_01.MirAst.CapturedMir)
    (s : MachineState) (m : AnnealStepState)
    (allocMap : List AllocMapEntry) (kw : KeyedAllocWorld) : Prop where
  stateRel : StateRelLM3_1 body s m allocMap
  keyed_eq : kw = annealMachineToKeyed m.machine

/-- **`KeyedStateRelLM3_2`**: `StateRelLM3_2` paired with its canonical keyed `ExtTreeMap0`
allocation world `kw = annealMachineToKeyed m.machine`. -/
structure KeyedStateRelLM3_2 (body : Trusted.Rustc.V2026_06_01.MirAst.CapturedMir)
    (s : MachineState) (m : AnnealStepState)
    (allocMap : List AllocMapEntry) (kw : KeyedAllocWorld) : Prop where
  stateRel : StateRelLM3_2 body s m allocMap
  keyed_eq : kw = annealMachineToKeyed m.machine

theorem StateRelLM3_1.toKeyed {body : Trusted.Rustc.V2026_06_01.MirAst.CapturedMir}
    {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry} (h : StateRelLM3_1 body s m allocMap) :
    KeyedStateRelLM3_1 body s m allocMap (annealMachineToKeyed m.machine) :=
  ⟨h, rfl⟩

theorem StateRelLM3_2.toKeyed {body : Trusted.Rustc.V2026_06_01.MirAst.CapturedMir}
    {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry} (h : StateRelLM3_2 body s m allocMap) :
    KeyedStateRelLM3_2 body s m allocMap (annealMachineToKeyed m.machine) :=
  ⟨h, rfl⟩

theorem KeyedStateRelLM3_1.toLM3_2 {body : Trusted.Rustc.V2026_06_01.MirAst.CapturedMir}
    {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry} {kw : KeyedAllocWorld}
    (h : KeyedStateRelLM3_1 body s m allocMap kw) :
    KeyedStateRelLM3_2 body s m allocMap kw :=
  ⟨h.stateRel.toLM3_2, h.keyed_eq⟩

/-- **Keyed lookup lifting (`KeyedStateRelLM3_1`)**: for every mapped local `e ∈ allocMap`,
live Anneal locals have a `.stack` live entry in `kw` (so `kw.isAllocLive = true`) and dead
Anneal locals are absent from `kw.findLive?`. -/
theorem keyedStateRelLM3_1_alloc_lookup {body : Trusted.Rustc.V2026_06_01.MirAst.CapturedMir}
    {s : MachineState} {m : AnnealStepState} {allocMap : List AllocMapEntry} {kw : KeyedAllocWorld}
    (h : KeyedStateRelLM3_1 body s m allocMap kw)
    {e : AllocMapEntry} (he : e ∈ allocMap) :
    (∀ slot, Trusted.Sequence.get? s.frame.locals e.localIdx = some slot → slot ≠ .dead →
      ∃ entry, kw.findLive? (ofMiriAllocId e.allocId) = some entry ∧
        entry.kind = .stack ∧ kw.isAllocLive (ofMiriAllocId e.allocId) = true) ∧
    (Trusted.Sequence.get? s.frame.locals e.localIdx = some .dead →
      kw.findLive? (ofMiriAllocId e.allocId) = none) := by
  rcases h with ⟨hs, rfl⟩
  rcases hs with ⟨tf, hframes, _, _, _, _, _, _, _, _, halloc, _⟩
  have hsync := halloc.local_alloc_sync tf hframes e he
  have hfl : (annealMachineToKeyed m.machine).findLive? (ofMiriAllocId e.allocId) =
      (m.machine.memory.live.toList.find? fun row => row.1 == e.allocId).map
        (fun row => liveEntryOfMiri annealRowProjection row.2) := by
    unfold annealMachineToKeyed memoryStateToKeyed memoryStateToLinear
    have hkw : (KeyedAllocWorld.ofLinear
        { (memoryStateToRows m.machine.memory).toLinear annealRowProjection with race := [] }).findLive?
        (ofMiriAllocId e.allocId) =
        ((memoryStateToRows m.machine.memory).toKeyed annealRowProjection).findLive?
          (ofMiriAllocId e.allocId) := rfl
    rw [hkw, toKeyed_findLive?]; rfl
  refine ⟨fun slot hslot hne => ?_, fun hdead => ?_⟩
  · obtain ⟨decl, hdecl, _⟩ := halloc.target_decl e he
    obtain ⟨la, hfind, hkind, _, _⟩ := (hsync.1 slot hslot hne).2.2 decl hdecl
    rw [← Array.find?_toList] at hfind
    refine ⟨liveEntryOfMiri annealRowProjection la, ?_, ?_, ?_⟩
    · rw [hfl, hfind]; rfl
    · simp [liveEntryOfMiri, hkind, memKindOfMiri]
    · unfold KeyedAllocWorld.isAllocLive
      rw [hfl, hfind]; rfl
  · have hnone := hsync.2 hdead
    rw [← Array.find?_toList] at hnone
    rw [hfl, hnone]; rfl

/-- **Keyed pointer-access lifting (`KeyedStateRelLM3_1`)**: for any `PtrRel`-related pointer in a
`KeyedStateRelLM3_1` state on the core memory domain, vendored `Miri.Memory.checkPtrAccess` with
`annealResolvePtr m.machine` and `m.machine.memory.getAllocInfo` agrees identically with
`kw.checkPtrAccess`. -/
theorem keyedStateRelLM3_1_checkPtrAccess {body : Trusted.Rustc.V2026_06_01.MirAst.CapturedMir}
    {s : MachineState} {m : AnnealStepState} {allocMap : List AllocMapEntry} {kw : KeyedAllocWorld}
    (h : KeyedStateRelLM3_1 body s m allocMap kw)
    (hcore : MemoryStateCoreDomain m.machine.memory)
    (hglobNd : MemoryStateGlobalsDistinct m.machine.memory)
    (halign : MemoryStateAlignFit m.machine.memory)
    {p : Trusted.Rustc.V2026_06_01.MirAst.ProvenancePtr}
    {mptr : Miri.Memory.Pointer AnnealProv} (hptr : PtrRel allocMap p mptr)
    (target : Miri.Memory.PointerArithmetic) (size : Miri.ABI.Size)
    (msg : Miri.Memory.CheckInAllocMsg) :
    ∃ e ∈ allocMap, e.tag = p.tag ∧
      (Miri.Memory.checkPtrAccess target ⟨mptr.offset, some mptr.provenance⟩ size msg
          (annealResolvePtr m.machine) m.machine.memory.getAllocInfo).isOk =
        kw.checkPtrAccess (some (ofMiriAllocId e.allocId, UInt64.ofNat p.offsetBytes))
          size.bytes.toNat := by
  rcases h with ⟨hs, rfl⟩
  rcases hs with ⟨_, _, _, _, _, _, _, _, _, _, halloc, _⟩
  have hbase : ∀ e ∈ allocMap, m.machine.lookupBaseAddr e.allocId = some (annealStackBaseAddr e.allocId) :=
    fun e he => (halloc.base_addr_valid e he).2.2
  obtain ⟨e, he, htag, hres⟩ := ptrRel_annealResolvePtr_resolvesAs hptr m.machine hbase
  exact ⟨e, he, htag, memoryState_checkPtrAccess_isOk_eq_keyed annealRowProjection
    m.machine.memory hcore hglobNd halign target _ size msg (annealResolvePtr m.machine) _ hres⟩

private theorem array_find?_eq_of_perm_nodup {α : Type}
    {xs ys : Array (Miri.Memory.AllocId × α)}
    (hperm : xs.toList.Perm ys.toList)
    (hnd : (xs.toList.map Prod.fst).Nodup) (id : Miri.Memory.AllocId) :
    xs.find? (fun row => row.1 == id) = ys.find? (fun row => row.1 == id) := by
  have hnd' : (ys.toList.map Prod.fst).Nodup := (hperm.map Prod.fst).nodup_iff.mp hnd
  rw [← Array.find?_toList, ← Array.find?_toList]
  have hiff : ∀ v : Miri.Memory.AllocId × α,
      xs.toList.find? (fun row => row.1 == id) = some v ↔
        ys.toList.find? (fun row => row.1 == id) = some v := by
    intro ⟨k, a⟩
    have hmemX : xs.toList.find? (fun row => row.1 == id) = some (k, a) ↔
        k = id ∧ (k, a) ∈ xs.toList := by
      constructor
      · intro hf
        exact ⟨eq_of_beq (by simpa using List.find?_some hf), List.mem_of_find?_eq_some hf⟩
      · rintro ⟨rfl, hm⟩
        have hlf : linearFind? (xs.toList.map fun r => (ofMiriAllocId r.1, r.2)) (ofMiriAllocId k) =
            some a := by
          rw [linearFind?_eq_some_iff_mem]
          · exact List.mem_map.mpr ⟨(k, a), hm, rfl⟩
          · rw [List.map_map]; exact nodup_map_ofMiri xs.toList Prod.fst hnd
        rw [linearFind?_map_ofMiri xs.toList Prod.fst Prod.snd k] at hlf
        cases hfx : xs.toList.find? (fun r => r.1 == k) with
        | none => rw [hfx] at hlf; cases hlf
        | some r =>
          rw [hfx] at hlf; injection hlf with hr2
          have hr1 : r.1 = k := eq_of_beq (by simpa using List.find?_some hfx)
          cases r; simp at hr1 hr2; subst hr1; subst hr2; rfl
    have hmemY : ys.toList.find? (fun row => row.1 == id) = some (k, a) ↔
        k = id ∧ (k, a) ∈ ys.toList := by
      constructor
      · intro hf
        exact ⟨eq_of_beq (by simpa using List.find?_some hf), List.mem_of_find?_eq_some hf⟩
      · rintro ⟨rfl, hm⟩
        have hlf : linearFind? (ys.toList.map fun r => (ofMiriAllocId r.1, r.2)) (ofMiriAllocId k) =
            some a := by
          rw [linearFind?_eq_some_iff_mem]
          · exact List.mem_map.mpr ⟨(k, a), hm, rfl⟩
          · rw [List.map_map]; exact nodup_map_ofMiri ys.toList Prod.fst hnd'
        rw [linearFind?_map_ofMiri ys.toList Prod.fst Prod.snd k] at hlf
        cases hfy : ys.toList.find? (fun r => r.1 == k) with
        | none => rw [hfy] at hlf; cases hlf
        | some r =>
          rw [hfy] at hlf; injection hlf with hr2
          have hr1 : r.1 = k := eq_of_beq (by simpa using List.find?_some hfy)
          cases r; simp at hr1 hr2; subst hr1; subst hr2; rfl
    rw [hmemX, hmemY, hperm.mem_iff]
  exact option_eq_of_some_iff hiff

/-- **`live`/`dead` array permutation invariance for `StateRelLM3_1` & `KeyedStateRelLM3_1`**:
reordering distinct-key `live` and `dead` arrays in `m.machine.memory` preserves `StateRelLM3_1`
AND keeps `kw` PROPOSITIONALLY IDENTICAL (`KeyedAllocWorld.ext`), eliminating list-order
preservation obligations on `live`/`dead` arrays. -/
theorem keyedStateRelLM3_1_liveDead_perm_invariant
    {body : Trusted.Rustc.V2026_06_01.MirAst.CapturedMir} {s : MachineState}
    {m : AnnealStepState} {allocMap : List AllocMapEntry} {kw : KeyedAllocWorld}
    (h : KeyedStateRelLM3_1 body s m allocMap kw)
    (live' : Array (Miri.Memory.AllocId ×
      Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind))
    (dead' : Array Miri.Memory.DeadAllocation)
    (hlivePerm : m.machine.memory.live.toList.Perm live'.toList)
    (hliveNd : (m.machine.memory.live.toList.map Prod.fst).Nodup)
    (hdeadPerm : m.machine.memory.dead.toList.Perm dead'.toList)
    (hdeadNd : (m.machine.memory.dead.toList.map fun d => d.allocId).Nodup)
    (hglobNd : MemoryStateGlobalsDistinct m.machine.memory) :
    let m' : AnnealStepState :=
      { m with machine := { m.machine with memory := { m.machine.memory with live := live', dead := dead' } } }
    KeyedStateRelLM3_1 body s m' allocMap kw := by
  dsimp only
  rcases h with ⟨hs, rfl⟩
  rcases hs with ⟨tf, hframes, hrc, hrp, hfr, hac, hcs, hap, hcl, hbor, halloc, hdisj⟩
  let m' : AnnealStepState :=
    { m with machine := { m.machine with memory := { m.machine.memory with live := live', dead := dead' } } }
  have hkeyed : annealMachineToKeyed m.machine = annealMachineToKeyed m'.machine :=
    memoryState_toKeyed_eq_of_perm annealRowProjection
      (s₁ := m.machine.memory) (s₂ := m'.machine.memory)
      rfl rfl (List.Perm.refl _) (List.Perm.refl _)
      hglobNd hlivePerm hliveNd hdeadPerm hdeadNd (List.Perm.refl _) List.nodup_nil
  have hfr' : FrameRelLM3_1 body m'.machine allocMap s.frame tf :=
    hfr.of_live_base (fun e he => hlivePerm.subset he) (fun _ _ _ => rfl)
  have halloc' : AllocMapRel body s m' allocMap :=
    { tags_nodup := halloc.tags_nodup
      local_to_alloc_unique := halloc.local_to_alloc_unique
      alloc_to_local_injective := halloc.alloc_to_local_injective
      target_decl := halloc.target_decl
      base_addr_valid := halloc.base_addr_valid
      borrow_sync := halloc.borrow_sync
      live_key_unique := fun e he la₁ la₂ h1 h2 =>
        halloc.live_key_unique e he la₁ la₂ (hlivePerm.symm.subset h1) (hlivePerm.symm.subset h2)
      local_alloc_sync := fun tf' hfrEq e he => by
        have hsync := halloc.local_alloc_sync tf' hfrEq e he
        have hfindEq : live'.find? (fun x => x.1 == e.allocId) =
            m.machine.memory.live.find? (fun x => x.1 == e.allocId) :=
          (array_find?_eq_of_perm_nodup hlivePerm hliveNd e.allocId).symm
        refine ⟨fun slot hslot hne => ?_, fun hdead => ?_⟩
        · rcases hsync.1 slot hslot hne with ⟨hloc, hsc, hdecl⟩
          refine ⟨hloc, hsc, fun decl hd => ?_⟩
          rcases hdecl decl hd with ⟨la, hfind, hk, ha, hsh⟩
          exact ⟨la, by rw [hfindEq]; exact hfind, hk, ha, hsh⟩
        · rw [hfindEq]; exact hsync.2 hdead }
  exact ⟨.mk tf hframes hrc hrp hfr' hac hcs hap hcl hbor halloc' hdisj, hkeyed⟩

/-- **`live`/`dead` array permutation invariance for `StateRelLM3_2` & `KeyedStateRelLM3_2`**. -/
theorem keyedStateRelLM3_2_liveDead_perm_invariant
    {body : Trusted.Rustc.V2026_06_01.MirAst.CapturedMir} {s : MachineState}
    {m : AnnealStepState} {allocMap : List AllocMapEntry} {kw : KeyedAllocWorld}
    (h : KeyedStateRelLM3_2 body s m allocMap kw)
    (live' : Array (Miri.Memory.AllocId ×
      Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind))
    (dead' : Array Miri.Memory.DeadAllocation)
    (hlivePerm : m.machine.memory.live.toList.Perm live'.toList)
    (hliveNd : (m.machine.memory.live.toList.map Prod.fst).Nodup)
    (hdeadPerm : m.machine.memory.dead.toList.Perm dead'.toList)
    (hdeadNd : (m.machine.memory.dead.toList.map fun d => d.allocId).Nodup)
    (hglobNd : MemoryStateGlobalsDistinct m.machine.memory) :
    let m' : AnnealStepState :=
      { m with machine := { m.machine with memory := { m.machine.memory with live := live', dead := dead' } } }
    KeyedStateRelLM3_2 body s m' allocMap kw := by
  dsimp only
  rcases h with ⟨hs, rfl⟩
  rcases hs with ⟨tf, hframes, hrc, hrp, hfr, hac, hcs, hap, hcl, hbor, halloc, hdisj⟩
  let m' : AnnealStepState :=
    { m with machine := { m.machine with memory := { m.machine.memory with live := live', dead := dead' } } }
  have hkeyed : annealMachineToKeyed m.machine = annealMachineToKeyed m'.machine :=
    memoryState_toKeyed_eq_of_perm annealRowProjection
      (s₁ := m.machine.memory) (s₂ := m'.machine.memory)
      rfl rfl (List.Perm.refl _) (List.Perm.refl _)
      hglobNd hlivePerm hliveNd hdeadPerm hdeadNd (List.Perm.refl _) List.nodup_nil
  have hfr' : FrameRelLM3_2 body m'.machine allocMap s.frame tf :=
    hfr.of_live_base (fun e he => hlivePerm.subset he) (fun _ _ _ => rfl)
  have halloc' : AllocMapRel body s m' allocMap :=
    { tags_nodup := halloc.tags_nodup
      local_to_alloc_unique := halloc.local_to_alloc_unique
      alloc_to_local_injective := halloc.alloc_to_local_injective
      target_decl := halloc.target_decl
      base_addr_valid := halloc.base_addr_valid
      borrow_sync := halloc.borrow_sync
      live_key_unique := fun e he la₁ la₂ h1 h2 =>
        halloc.live_key_unique e he la₁ la₂ (hlivePerm.symm.subset h1) (hlivePerm.symm.subset h2)
      local_alloc_sync := fun tf' hfrEq e he => by
        have hsync := halloc.local_alloc_sync tf' hfrEq e he
        have hfindEq : live'.find? (fun x => x.1 == e.allocId) =
            m.machine.memory.live.find? (fun x => x.1 == e.allocId) :=
          (array_find?_eq_of_perm_nodup hlivePerm hliveNd e.allocId).symm
        refine ⟨fun slot hslot hne => ?_, fun hdead => ?_⟩
        · rcases hsync.1 slot hslot hne with ⟨hloc, hsc, hdecl⟩
          refine ⟨hloc, hsc, fun decl hd => ?_⟩
          rcases hdecl decl hd with ⟨la, hfind, hk, ha, hsh⟩
          exact ⟨la, by rw [hfindEq]; exact hfind, hk, ha, hsh⟩
        · rw [hfindEq]; exact hsync.2 hdead }
  exact ⟨.mk tf hframes hrc hrp hfr' hac hcs hap hcl hbor halloc' hdisj, hkeyed⟩

/-- **Allocation lifting on `KeyedStateRelLM3_1`**: stepping `m.machine.memory` through
`MemoryLifecycle.insertAllocation` advances `kw` by `KeyedAllocWorld.allocate` on the same entry. -/
theorem keyedStateRelLM3_1_insertAllocation_step
    {body : Trusted.Rustc.V2026_06_01.MirAst.CapturedMir} {s : MachineState}
    {m : AnnealStepState} {allocMap : List AllocMapEntry} {kw : KeyedAllocWorld}
    (h : KeyedStateRelLM3_1 body s m allocMap kw)
    (alloc : Miri.Memory.Allocation AnnealProv Unit)
    (kind : Miri.Memory.MemoryKind Miri.Memory.MiriMemoryKind)
    (maxSize : Miri.ABI.Size)
    (globalKind : Option (Miri.Memory.MemoryKind Miri.Memory.MiriMemoryKind))
    (hnosrc : m.machine.memory.sourceAllocIdWorldActive = false)
    (hfit : ¬ alloc.byteSize.bytes > maxSize.bytes)
    (hnotGlob : globalKind ≠ some kind)
    (extra : Option Miri.TreeBorrows.BorrowTree) (rootPtr : Miri.Memory.Pointer AnnealProv) :
    let mres := Miri.Memory.MemoryLifecycle.insertAllocation m.machine.memory () (fun _ _ => ())
      alloc kind maxSize globalKind
      (fun mem _ _ _ _ _ => ⟨mem, (), .ok extra⟩)
      (fun mem _ _ _ => ⟨mem, (), .ok rootPtr⟩)
    let entry := liveEntryOfMiri annealRowProjection ⟨kind, alloc.withExtra extra⟩
    annealMachineToKeyed { m.machine with memory := mres.memory } = (kw.allocate entry).1 := by
  dsimp only
  rcases h with ⟨_, rfl⟩
  exact (memoryState_insertAllocation_eq_keyed annealRowProjection m.machine.memory ()
    (fun _ _ => ()) alloc kind maxSize globalKind
    (fun mem _ _ _ _ _ => ⟨mem, (), .ok extra⟩)
    (fun mem _ _ _ => ⟨mem, (), .ok rootPtr⟩)
    hnosrc hfit hnotGlob extra rootPtr (fun _ _ _ => ⟨rfl, rfl⟩) (fun _ _ _ => ⟨rfl, rfl⟩)).1

/-- **Deallocation lifting on `KeyedStateRelLM3_1`**: stepping `m.machine.memory` through
`MemoryLifecycle.deallocatePtrWith` for a `PtrRel`-related pointer using `annealResolvePtr`
advances `kw` identically to `KeyedAllocWorld.deallocateWith` (including exact failure order
and detached-state retention). -/
theorem keyedStateRelLM3_1_deallocate_step
    {body : Trusted.Rustc.V2026_06_01.MirAst.CapturedMir} {s : MachineState}
    {m : AnnealStepState} {allocMap : List AllocMapEntry} {kw : KeyedAllocWorld}
    (h : KeyedStateRelLM3_1 body s m allocMap kw)
    {p : Trusted.Rustc.V2026_06_01.MirAst.ProvenancePtr}
    {mptr : Miri.Memory.Pointer AnnealProv} (hptr : PtrRel allocMap p mptr)
    (oldSizeAndAlign : Option (Miri.ABI.Size × Miri.ABI.Align))
    (halignLive : ∀ row ∈ m.machine.memory.live.toList, row.2.allocation.align.pow2 < 256)
    (halignReq : ∀ sz al, oldSizeAndAlign = some (sz, al) → al.pow2 < 256)
    (tb : DeallocHookSpec) :
    ∃ e ∈ allocMap, e.tag = p.tag ∧
      let hooks : Miri.Memory.MemoryDeallocationHooks AnnealProv
          (Option Miri.TreeBorrows.BorrowTree) Miri.Memory.MiriMemoryKind Unit Miri.Memory.BorTag :=
        { synchronizeMemory := fun _ _ => ()
          resolvePointer := fun mem _ ptr sz =>
            match annealResolvePtr m.machine ptr sz with
            | .ok r => ⟨mem, (), .ok (r.allocId, r.offset, r.extra)⟩
            | .error a => ⟨mem, (), .error a⟩
          beforeDeallocation := fun mem _ _ _ _ _ _ _ _ => ⟨mem, (), tb.run⟩ }
      let mres := Miri.Memory.MemoryLifecycle.deallocatePtrWith m.machine.memory ()
        ⟨mptr.offset, some mptr.provenance⟩ oldSizeAndAlign .stack hooks
      let expLayout := oldSizeAndAlign.map fun x => (x.1.bytes, UInt8.ofNat x.2.pow2)
      let kres := kw.deallocate (.provenanced (ofMiriAllocId e.allocId) (UInt64.ofNat p.offsetBytes))
        expLayout .stack tb
      annealMachineToKeyed { m.machine with memory := mres.memory } = kres.world ∧
      mres.detached.map (fun x => (ofMiriAllocId x.1, liveEntryOfMiri annealRowProjection x.2)) =
        kres.detached ∧
      (match mres.outcome, kres.outcome with
       | .ok (), .ok () => True
       | .error me, .error ke => deallocErrOfMiri me = some ke
       | _, _ => False) := by
  rcases h with ⟨hs, rfl⟩
  rcases hs with ⟨_, _, _, _, _, _, _, _, _, _, halloc, _⟩
  have hbase : ∀ e ∈ allocMap, m.machine.lookupBaseAddr e.allocId = some (annealStackBaseAddr e.allocId) :=
    fun e he => (halloc.base_addr_valid e he).2.2
  obtain ⟨e, he, htag, hres⟩ := ptrRel_annealResolvePtr_resolvesAs hptr m.machine hbase
  obtain ⟨borTag, hres0⟩ := hres 0
  refine ⟨e, he, htag, ?_⟩
  have hkindFaithful : ∀ row ∈ m.machine.memory.live.toList,
      (memKindOfMiri annealRowProjection.machineKind row.2.kind ==
          memKindOfMiri annealRowProjection.machineKind .stack) =
        decide (row.2.kind = .stack) := by
    intro row _
    cases hk : row.2.kind with
    | stack => rfl
    | callerLocation => rfl
    | machine mk => cases mk <;> rfl
  exact memoryState_deallocatePtrWith_eq_keyed annealRowProjection m.machine.memory ()
    ⟨mptr.offset, some mptr.provenance⟩ oldSizeAndAlign .stack
    { synchronizeMemory := fun _ _ => ()
      resolvePointer := fun mem _ ptr sz =>
        match annealResolvePtr m.machine ptr sz with
        | .ok r => ⟨mem, (), .ok (r.allocId, r.offset, r.extra)⟩
        | .error a => ⟨mem, (), .error a⟩
      beforeDeallocation := fun mem _ _ _ _ _ _ _ _ => ⟨mem, (), tb.run⟩ }
    (.provenanced (ofMiriAllocId e.allocId) (UInt64.ofNat p.offsetBytes))
    (fun _ _ _ => tb.run)
    (by simp [hres0])
    (by simp [hres0]; exact ⟨rfl, rfl⟩)
    halignLive halignReq hkindFaithful []
    (fun _ _ _ _ _ => ⟨rfl, rfl⟩)

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

/-! ### Closing the Traversal Schedule Fuel Gap & `.SkipChildrenOfAccessed` -/

/-- `ReachesRoot` depth is uniquely determined by the tag (since `findNode?` is deterministic). -/
theorem reachesRoot_unique_depth {nodes : List TreeTagNode} {rootTag d₁ d₂ t : Nat}
    (h₁ : ReachesRoot nodes rootTag d₁ t) (h₂ : ReachesRoot nodes rootTag d₂ t) :
    d₁ = d₂ := by
  induction h₁ generalizing d₂ with
  | root r hr hpar =>
    cases h₂ with
    | root => rfl
    | step _ _ _ n hn hpar' _ =>
      rw [hr] at hn; injection hn with hEq; subst hEq
      rw [hpar] at hpar'; cases hpar'
  | step d t p n hn hpar hprev ih =>
    cases h₂ with
    | root r hr hpar' =>
      rw [hr] at hn; injection hn with hEq; subst hEq
      rw [hpar] at hpar'; cases hpar'
    | step d' _ p' n' hn' hpar' hprev' =>
      rw [hn] at hn'; injection hn' with hEq; subst hEq
      rw [hpar] at hpar'; injection hpar' with hp; subst hp
      exact congrArg Nat.succ (ih hprev')

private theorem mem_childTagsInListOrder_iff {nodes : List TreeTagNode} {t c : Nat} :
    c ∈ childTagsInListOrder nodes t ↔ ∃ n ∈ nodes, n.parentTag = some t ∧ n.tag = c := by
  unfold childTagsInListOrder
  simp only [List.mem_map, List.mem_filter, beq_iff_eq]
  constructor
  · rintro ⟨n, ⟨hn, hp⟩, rfl⟩; exact ⟨n, hn, hp, rfl⟩
  · rintro ⟨n, hn, hp, rfl⟩; exact ⟨n, ⟨hn, hp⟩, rfl⟩

private theorem list_flatMap_congr {α β : Type} {xs : List α} {f g : α → List β}
    (h : ∀ x ∈ xs, f x = g x) : xs.flatMap f = xs.flatMap g := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    simp only [List.flatMap_cons]
    rw [h x List.mem_cons_self, ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]

private theorem mem_of_head?_eq_some {α : Type} {xs : List α} {x : α}
    (h : xs.head? = some x) : x ∈ xs := by
  cases xs with
  | nil => cases h
  | cons a rest =>
    injection h with ha; subst ha
    exact List.mem_cons_self

private theorem ancestorPathTagsAux_head (nodes : List TreeTagNode) (fuel t : Nat) :
    (ancestorPathTagsAux nodes fuel t).head? = some t := by
  cases fuel with
  | zero => rfl
  | succ f =>
    unfold ancestorPathTagsAux
    cases findNode? nodes t with
    | none => rfl
    | some m =>
      rcases m with ⟨_, par, _, _, _, _, _⟩
      cases par <;> rfl

/-- **Foreign postorder fuel invariance on rooted trees**: for any node `t` at depth `d < w.nodes.length`
in a rooted borrow tree `BorrowTreeRootedWF w rootTag`, `foreignPostorderTags` stabilizes at fuel
`w.nodes.length - d` (and in particular at `w.nodes.length = (traversalTreeOfNodes w.nodes).nodes.size`). -/
theorem foreignPostorderTags_fuel_irrel_rooted {w : FnEntryBorrowWorld} {rootTag : Nat}
    (hwf : BorrowTreeRootedWF w rootTag) (skip : Nat → Bool) :
    ∀ (k t d : Nat),
      ReachesRoot w.nodes rootTag d t → d < w.nodes.length → k = w.nodes.length - d →
      ∀ (f₁ f₂ : Nat), k ≤ f₁ → k ≤ f₂ →
        foreignPostorderTags (childTagsInListOrder w.nodes) skip f₁ t =
          foreignPostorderTags (childTagsInListOrder w.nodes) skip f₂ t := by
  intro k
  induction k with
  | zero =>
    intro t d _ hd hk
    omega
  | succ k' ih =>
    intro t d hreach hd hk f₁ f₂ hf₁ hf₂
    obtain ⟨f₁', rfl⟩ : ∃ m, f₁ = m + 1 := ⟨f₁ - 1, by omega⟩
    obtain ⟨f₂', rfl⟩ : ∃ m, f₂ = m + 1 := ⟨f₂ - 1, by omega⟩
    simp only [foreignPostorderTags]
    cases hsk : skip t with
    | true => rfl
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      congr 1
      apply list_flatMap_congr
      intro c hc
      rw [List.mem_reverse] at hc
      rcases mem_childTagsInListOrder_iff.mp hc with ⟨cn, hcn, hpar, rfl⟩
      have hfind : findNode? w.nodes cn.tag = some cn :=
        findNode?_eq_some_of_mem_of_nodup hwf.tagsNodup hcn
      have hreachC : ReachesRoot w.nodes rootTag (d + 1) cn.tag :=
        ReachesRoot.step d cn.tag t cn hfind hpar hreach
      obtain ⟨dc, hdc, hreachC'⟩ := hwf.reachesRoot cn hcn
      have hdEq : dc = d + 1 := reachesRoot_unique_depth hreachC' hreachC
      have hd1Lt : d + 1 < w.nodes.length := by omega
      exact ih cn.tag (d + 1) hreachC hd1Lt (by omega) f₁' f₂' (by omega) (by omega)

/-- **Exact schedule fuel closure**: on any rooted borrow tree, vendored `TraversalTree.traverse`'s
fuel `w.nodes.length` produces the exact same foreign postorder as the theory's `w.nodes.length + 1`. -/
theorem foreignPostorderTags_len_eq_len_succ {w : FnEntryBorrowWorld} {rootTag : Nat}
    (hwf : BorrowTreeRootedWF w rootTag) (skip : Nat → Bool)
    {n : TreeTagNode} (hn : n ∈ w.nodes) :
    foreignPostorderTags (childTagsInListOrder w.nodes) skip w.nodes.length n.tag =
      foreignPostorderTags (childTagsInListOrder w.nodes) skip (w.nodes.length + 1) n.tag := by
  obtain ⟨d, hd, hreach⟩ := hwf.reachesRoot n hn
  exact foreignPostorderTags_fuel_irrel_rooted hwf skip (w.nodes.length - d) n.tag d
    hreach hd rfl w.nodes.length (w.nodes.length + 1) (by omega) (by omega)

private theorem denseTags_getElem?_eq_some_of_mem {nodes : List TreeTagNode}
    (hdense : DenseTags nodes) (hnodup : (nodes.map (·.tag)).Nodup)
    {n : TreeTagNode} (hn : n ∈ nodes) : nodes[n.tag]? = some n := by
  rw [← findNode?_eq_getElem?_of_denseTags hdense n.tag]
  exact findNode?_eq_some_of_mem_of_nodup hnodup hn

theorem traversalChildren_traversalTreeOfNodes_of_mem {nodes : List TreeTagNode}
    (hdense : DenseTags nodes) (hnodup : (nodes.map (·.tag)).Nodup)
    {n : TreeTagNode} (hn : n ∈ nodes) :
    traversalChildren (traversalTreeOfNodes nodes) n.tag = childTagsInListOrder nodes n.tag := by
  unfold traversalChildren traversalTreeOfNodes
  simp only [List.getElem?_toArray, List.getElem?_map,
    denseTags_getElem?_eq_some_of_mem hdense hnodup hn, Option.map_some, Option.getD_some]

private theorem mem_ancestorPathTags_of_reachesRoot {nodes : List TreeTagNode} {rootTag : Nat} :
    ∀ {d t : Nat}, ReachesRoot nodes rootTag d t →
      ∀ (fuel : Nat) (x : Nat), x ∈ ancestorPathTagsAux nodes fuel t →
        ∃ m ∈ nodes, m.tag = x := by
  intro d t hreach
  induction hreach with
  | root r hr hpar =>
    intro fuel x hx
    cases fuel with
    | zero =>
      simp only [ancestorPathTagsAux, List.mem_singleton] at hx
      subst hx; exact ⟨r, (mem_of_findNode?_eq_some hr).1, (mem_of_findNode?_eq_some hr).2⟩
    | succ fuel' =>
      simp only [ancestorPathTagsAux, hr, hpar, List.mem_singleton] at hx
      subst hx; exact ⟨r, (mem_of_findNode?_eq_some hr).1, (mem_of_findNode?_eq_some hr).2⟩
  | step d t p n hn hpar hprev ih =>
    intro fuel x hx
    cases fuel with
    | zero =>
      simp only [ancestorPathTagsAux, List.mem_singleton] at hx
      subst hx; exact ⟨n, (mem_of_findNode?_eq_some hn).1, (mem_of_findNode?_eq_some hn).2⟩
    | succ fuel' =>
      simp only [ancestorPathTagsAux, hn, hpar, List.mem_cons] at hx
      rcases hx with rfl | hx'
      · exact ⟨n, (mem_of_findNode?_eq_some hn).1, (mem_of_findNode?_eq_some hn).2⟩
      · exact ih fuel' x hx'

private theorem initialForeignRootTags_congr {f g : Nat → List Nat} {path : List Nat}
    (hfg : ∀ t ∈ path, f t = g t) (prev : Option Nat) :
    initialForeignRootTags f path prev = initialForeignRootTags g path prev := by
  induction path generalizing prev with
  | nil => rfl
  | cons cur rest ih =>
    simp only [initialForeignRootTags]
    rw [hfg cur List.mem_cons_self, ih (fun t ht => hfg t (List.mem_cons_of_mem _ ht))]

private theorem mem_initialForeignRootTags_child {nodes : List TreeTagNode}
    {path : List Nat} {prev : Option Nat} {r : Nat}
    (hr : r ∈ initialForeignRootTags (childTagsInListOrder nodes) path prev) :
    ∃ cur ∈ path, r ∈ childTagsInListOrder nodes cur := by
  induction path generalizing prev with
  | nil => simp [initialForeignRootTags] at hr
  | cons cur rest ih =>
    simp only [initialForeignRootTags, List.mem_append, List.mem_filter, List.mem_reverse] at hr
    rcases hr with ⟨hrc, _⟩ | hrest
    · exact ⟨cur, List.mem_cons_self, hrc⟩
    · rcases ih hrest with ⟨c, hc, hrc⟩
      exact ⟨c, List.mem_cons_of_mem _ hc, hrc⟩

private theorem foreignPostorderTags_congr_rooted {w : FnEntryBorrowWorld} {rootTag : Nat}
    (hwf : BorrowTreeRootedWF w rootTag) (hdense : DenseTags w.nodes)
    (skip₁ skip₂ : Nat → Bool)
    (hskip : ∀ n ∈ w.nodes, skip₁ n.tag = skip₂ n.tag) :
    ∀ (fuel : Nat) (n : TreeTagNode), n ∈ w.nodes →
      foreignPostorderTags (traversalChildren (traversalTreeOfNodes w.nodes)) skip₁ fuel n.tag =
        foreignPostorderTags (childTagsInListOrder w.nodes) skip₂ fuel n.tag := by
  intro fuel
  induction fuel with
  | zero => intro n _; rfl
  | succ fuel ih =>
    intro n hn
    simp only [foreignPostorderTags, hskip n hn,
      traversalChildren_traversalTreeOfNodes_of_mem hdense hwf.tagsNodup hn]
    cases skip₂ n.tag with
    | true => rfl
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      congr 1
      apply list_flatMap_congr
      intro c hc
      rw [List.mem_reverse] at hc
      rcases mem_childTagsInListOrder_iff.mp hc with ⟨cn, hcn, _, rfl⟩
      exact ih cn hcn

private theorem mem_foreignPostorderTags_mem_nodes {nodes : List TreeTagNode}
    (skip : Nat → Bool) :
    ∀ (fuel t : Nat), (∃ n ∈ nodes, n.tag = t) →
      ∀ x ∈ foreignPostorderTags (childTagsInListOrder nodes) skip fuel t,
        ∃ m ∈ nodes, m.tag = x := by
  intro fuel
  induction fuel with
  | zero => intro t _ x hx; simp [foreignPostorderTags] at hx
  | succ fuel ih =>
    intro t ht x hx
    simp only [foreignPostorderTags] at hx
    cases hsk : skip t with
    | true => simp [hsk] at hx
    | false =>
      simp only [hsk, Bool.false_eq_true, ↓reduceIte, List.mem_append, List.mem_flatMap,
        List.mem_reverse, List.mem_singleton] at hx
      rcases hx with ⟨c, hc, hxc⟩ | rfl
      · rcases mem_childTagsInListOrder_iff.mp hc with ⟨cn, hcn, _, rfl⟩
        exact ih cn.tag ⟨cn, hcn, rfl⟩ x hxc
      · exact ht

private theorem filter_tag_eq_singleton {nodes : List TreeTagNode}
    (hnodup : (nodes.map (·.tag)).Nodup) {n : TreeTagNode} (hn : n ∈ nodes) :
    nodes.filter (fun m => m.tag == n.tag) = [n] := by
  induction nodes with
  | nil => cases hn
  | cons x rest ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnodup
    rcases hnodup with ⟨hnot, hrest⟩
    cases hn with
    | head =>
      simp only [List.filter_cons, beq_self_eq_true, ↓reduceIte]
      congr 1
      have hnil : ∀ (l : List TreeTagNode), (∀ m ∈ l, m.tag ≠ n.tag) →
          l.filter (fun m => m.tag == n.tag) = [] := by
        intro l
        induction l with
        | nil => intro _; rfl
        | cons y ys ihl =>
          intro hall
          have hne : (y.tag == n.tag) = false := beq_false_of_ne (hall y List.mem_cons_self)
          simp only [List.filter_cons, hne, Bool.false_eq_true, ↓reduceIte]
          exact ihl fun m hm => hall m (List.mem_cons_of_mem _ hm)
      exact hnil rest fun m hm hEq => hnot ⟨m, hm, hEq⟩
    | tail _ hmem =>
      have hne : (x.tag == n.tag) = false := by
        apply beq_false_of_ne
        intro heq
        exact hnot ⟨n, hmem, heq.symm⟩
      simp only [List.filter_cons, hne, Bool.false_eq_true, ↓reduceIte]
      exact ih hrest hmem

/-- **End-to-end traversal schedule theorem (closing the `nodes.length + 1` vs `tree.nodes.size`
fuel gap)**: on any rooted, dense-tag borrow tree, vendored `TraversalTree.traverse` under
`.VisitChildrenOfAccessed` with the `foreignNodeSkipsSubtree` skip list produces the EXACT local
path events followed by the EXACT foreign events of the theory's `foreignVisitScheduleNodes`
(eliminating the one-step fuel gap completely). -/
theorem miri_traverse_eq_foreignVisitScheduleNodes {w : FnEntryBorrowWorld} {rootTag : Nat}
    (hwf : BorrowTreeRootedWF w rootTag) (hdense : DenseTags w.nodes)
    {start : TreeTagNode} (hstart : start ∈ w.nodes)
    (isWrite : Bool) (off len : Nat) :
    let skipNodes := (w.nodes.filter fun a => foreignNodeSkipsSubtree isWrite off len a).map (·.tag)
    (Miri.TreeBorrows.Tree.TraversalTree.traverse (traversalTreeOfNodes w.nodes) start.tag
        .VisitChildrenOfAccessed skipNodes).2 =
      (ancestorPathTags w.nodes start.tag).map
          (fun t => (⟨t, .LocalAccess⟩ : Miri.TreeBorrows.Tree.TraversalEvent)) ++
        (foreignVisitScheduleNodes (childTagsInListOrder w.nodes) w start.tag isWrite off len).map
          (fun n => (⟨n.tag, .ForeignAccess⟩ : Miri.TreeBorrows.Tree.TraversalEvent)) := by
  dsimp only
  rw [miri_traverse_eq_schedule, ← ancestorPathTags_eq_miri_ancestorPath hwf hdense start hstart]
  dsimp only
  congr 1
  have hsize : (traversalTreeOfNodes w.nodes).nodes.size = w.nodes.length := by
    unfold traversalTreeOfNodes; rw [List.size_toArray, List.length_map]
  rw [hsize]
  obtain ⟨ds, _, hreachStart⟩ := hwf.reachesRoot start hstart
  have hpathMem : ∀ t ∈ ancestorPathTags w.nodes start.tag, ∃ m ∈ w.nodes, m.tag = t :=
    fun t ht => mem_ancestorPathTags_of_reachesRoot hreachStart (w.nodes.length + 1) t ht
  have hrootsEq :
      initialForeignRootTags (traversalChildren (traversalTreeOfNodes w.nodes))
          (ancestorPathTags w.nodes start.tag) none =
        initialForeignRootTags (childTagsInListOrder w.nodes)
          (ancestorPathTags w.nodes start.tag) none := by
    apply initialForeignRootTags_congr
    intro t ht
    rcases hpathMem t ht with ⟨m, hm, rfl⟩
    exact traversalChildren_traversalTreeOfNodes_of_mem hdense hwf.tagsNodup hm
  rw [hrootsEq]
  let skipNodes := (w.nodes.filter fun a => foreignNodeSkipsSubtree isWrite off len a).map (·.tag)
  let skipTheory : Nat → Bool := fun t =>
    match findNode? w.nodes t with
    | some a => foreignNodeSkipsSubtree isWrite off len a
    | none => false
  have hskipEq : ∀ n ∈ w.nodes, skipNodes.contains n.tag = skipTheory n.tag := by
    intro n hn
    have hfn : findNode? w.nodes n.tag = some n := findNode?_eq_some_of_mem_of_nodup hwf.tagsNodup hn
    apply Bool.eq_iff_iff.mpr
    simp only [skipNodes, skipTheory, hfn, List.contains_eq_mem, decide_eq_true_eq,
      List.mem_map, List.mem_filter]
    constructor
    · rintro ⟨a, ⟨ha, hsk⟩, htag⟩
      have hfa : findNode? w.nodes a.tag = some a := findNode?_eq_some_of_mem_of_nodup hwf.tagsNodup ha
      rw [htag, hfn] at hfa; injection hfa with hEq; subst hEq; exact hsk
    · intro hsk
      exact ⟨n, ⟨hn, hsk⟩, rfl⟩
  have hflat :
      (initialForeignRootTags (childTagsInListOrder w.nodes)
          (ancestorPathTags w.nodes start.tag) none).flatMap
        (foreignPostorderTags (traversalChildren (traversalTreeOfNodes w.nodes))
          (fun t => skipNodes.contains t) w.nodes.length) =
      (initialForeignRootTags (childTagsInListOrder w.nodes)
          (ancestorPathTags w.nodes start.tag) none).flatMap
        (foreignPostorderTags (childTagsInListOrder w.nodes) skipTheory (w.nodes.length + 1)) := by
    apply list_flatMap_congr
    intro r hr
    rcases mem_initialForeignRootTags_child hr with ⟨_, _, hrc⟩
    rcases mem_childTagsInListOrder_iff.mp hrc with ⟨rn, hrn, _, rfl⟩
    rw [foreignPostorderTags_congr_rooted hwf hdense (fun t => skipNodes.contains t) skipTheory
          hskipEq w.nodes.length rn hrn,
        foreignPostorderTags_len_eq_len_succ hwf skipTheory hrn]
  rw [hflat]
  dsimp only [foreignVisitScheduleNodes]
  have htagsMem : ∀ t ∈ (initialForeignRootTags (childTagsInListOrder w.nodes)
      (ancestorPathTags w.nodes start.tag) none).flatMap
      (foreignPostorderTags (childTagsInListOrder w.nodes) skipTheory (w.nodes.length + 1)),
      ∃ m ∈ w.nodes, m.tag = t := by
    intro t ht
    rw [List.mem_flatMap] at ht
    rcases ht with ⟨r, hr, htr⟩
    rcases mem_initialForeignRootTags_child hr with ⟨_, _, hrc⟩
    rcases mem_childTagsInListOrder_iff.mp hrc with ⟨rn, hrn, _, rfl⟩
    exact mem_foreignPostorderTags_mem_nodes skipTheory (w.nodes.length + 1) rn.tag
      ⟨rn, hrn, rfl⟩ t htr
  have hhelper : ∀ (tags : List Nat), (∀ t ∈ tags, ∃ m ∈ w.nodes, m.tag = t) →
      tags.map (fun t => (⟨t, .ForeignAccess⟩ : Miri.TreeBorrows.Tree.TraversalEvent)) =
        (tags.flatMap fun t => w.nodes.filter fun n => n.tag == t).map
          (fun n => (⟨n.tag, .ForeignAccess⟩ : Miri.TreeBorrows.Tree.TraversalEvent)) := by
    intro tags
    induction tags with
    | nil => intro _; rfl
    | cons t rest ih =>
      intro hmem
      rcases hmem t List.mem_cons_self with ⟨m, hm, rfl⟩
      simp only [List.flatMap_cons, filter_tag_eq_singleton hwf.tagsNodup hm, List.cons_append,
        List.nil_append, List.map_cons]
      exact congrArg _ (ih fun x hx => hmem x (List.mem_cons_of_mem _ hx))
  have htrans := hhelper _ htagsMem
  refine htrans.trans ?_
  congr 1

/-- Under `.SkipChildrenOfAccessed` (used by `BorrowTree.releaseProtector`), vendored
`initialForeignRoots.go` emits NO children of the accessed `start` node and starts collecting
siblings at `rest` with `previous = some start`. -/
theorem miri_initialForeignRoots_skipChildren_eq (tree : Miri.TreeBorrows.Tree.TraversalTree)
    (start : Nat) (rest : List Nat) :
    miriInitialForeignRootsGo tree .SkipChildrenOfAccessed (start :: rest) none true =
      initialForeignRootTags (traversalChildren tree) rest (some start) := by
  have hunf : miriInitialForeignRootsGo tree .SkipChildrenOfAccessed (start :: rest) none true =
      miriInitialForeignRootsGo tree .SkipChildrenOfAccessed rest (some start) false := rfl
  rw [hunf]
  have hrest : ∀ (xs : List Nat) (prev : Option Nat),
      miriInitialForeignRootsGo tree .SkipChildrenOfAccessed xs prev false =
        initialForeignRootTags (traversalChildren tree) xs prev := by
    intro xs
    induction xs with
    | nil => intro _; rfl
    | cons cur tl ih =>
      intro prev
      have hstep : miriInitialForeignRootsGo tree .SkipChildrenOfAccessed (cur :: tl) prev false =
          ((traversalChildren tree cur).reverse.filter (fun child => prev != some child)) ++
            miriInitialForeignRootsGo tree .SkipChildrenOfAccessed tl (some cur) false := rfl
      rw [hstep, ih]
      rfl
  exact hrest rest (some start)

/-- **Vendored `TraversalTree.traverse` under `.SkipChildrenOfAccessed`**: local events walk
`ancestorPath tree start`, while foreign events expand ONLY the sibling subtrees strictly above
`start` (`initialForeignRootTags ... path.tail (some start)`), omitting all children of `start`. -/
theorem miri_traverse_skipChildren_eq_schedule (tree : Miri.TreeBorrows.Tree.TraversalTree)
    (start : Nat) (skipNodes : List Nat) :
    let path := Miri.TreeBorrows.Tree.TraversalTree.ancestorPath tree start
    Miri.TreeBorrows.Tree.TraversalTree.traverse tree start .SkipChildrenOfAccessed skipNodes =
      (path.getLast!,
        path.map (fun index => (⟨index, .LocalAccess⟩ : Miri.TreeBorrows.Tree.TraversalEvent)) ++
          ((initialForeignRootTags (traversalChildren tree) path.tail (some start)).flatMap
            (foreignPostorderTags (traversalChildren tree) (fun t => skipNodes.contains t)
              tree.nodes.size)).map
            (fun t => (⟨t, .ForeignAccess⟩ : Miri.TreeBorrows.Tree.TraversalEvent))) := by
  dsimp only
  have hhead := Miri.TreeBorrows.Tree.TraversalTree.ancestorPath_head tree start
  cases hp : Miri.TreeBorrows.Tree.TraversalTree.ancestorPath tree start with
  | nil => rw [hp] at hhead; cases hhead
  | cons hd tl =>
    rw [hp] at hhead; injection hhead with hhd; subst hd
    have hunf : Miri.TreeBorrows.Tree.TraversalTree.traverse tree start .SkipChildrenOfAccessed
          skipNodes =
        ((start :: tl).getLast!,
          (start :: tl).map (fun index => (⟨index, .LocalAccess⟩ : Miri.TreeBorrows.Tree.TraversalEvent)) ++
            (miriInitialForeignRootsGo tree .SkipChildrenOfAccessed (start :: tl) none true).flatMap
              (miriForeignPostorder tree skipNodes tree.nodes.size)) := by
      unfold Miri.TreeBorrows.Tree.TraversalTree.traverse
      rw [hp]; rfl
    rw [hunf, miri_initialForeignRoots_skipChildren_eq,
      show miriForeignPostorder tree skipNodes tree.nodes.size = _ from
        funext (miri_foreignPostorder_eq tree skipNodes tree.nodes.size),
      List.map_flatMap]
    rfl

private theorem reachesRoot_of_mem_ancestorPathAux {nodes : List TreeTagNode} {rootTag : Nat} :
    ∀ {d t : Nat}, ReachesRoot nodes rootTag d t →
      ∀ (fuel x : Nat), x ∈ ancestorPathTagsAux nodes fuel t →
        ∃ dx ≤ d, ReachesRoot nodes rootTag dx x ∧ (x = t ↔ dx = d) := by
  intro d t hreach
  induction hreach with
  | root r hr hpar =>
    intro fuel x hx
    cases fuel with
    | zero =>
      simp only [ancestorPathTagsAux, List.mem_singleton] at hx
      subst x; exact ⟨0, Nat.le_refl 0, ReachesRoot.root r hr hpar, ⟨fun _ => rfl, fun _ => rfl⟩⟩
    | succ f =>
      simp only [ancestorPathTagsAux, hr, hpar, List.mem_singleton] at hx
      subst x; exact ⟨0, Nat.le_refl 0, ReachesRoot.root r hr hpar, ⟨fun _ => rfl, fun _ => rfl⟩⟩
  | step d t p n hn hpar hprev ih =>
    intro fuel x hx
    cases fuel with
    | zero =>
      simp only [ancestorPathTagsAux, List.mem_singleton] at hx
      subst x
      exact ⟨d + 1, Nat.le_refl (d + 1), ReachesRoot.step d t p n hn hpar hprev,
        ⟨fun _ => rfl, fun _ => rfl⟩⟩
    | succ f =>
      simp only [ancestorPathTagsAux, hn, hpar, List.mem_cons] at hx
      rcases hx with hxt | hx'
      · subst hxt
        exact ⟨d + 1, Nat.le_refl (d + 1), ReachesRoot.step d x p n hn hpar hprev,
          ⟨fun _ => rfl, fun _ => rfl⟩⟩
      · rcases ih f x hx' with ⟨dx, hdx, hrX, _⟩
        refine ⟨dx, by omega, hrX, ?_⟩
        constructor
        · intro hxt; subst hxt
          have := reachesRoot_unique_depth hrX (ReachesRoot.step d x p n hn hpar hprev)
          omega
        · intro hdeq; omega

private theorem reachesRoot_unique_at_depth {nodes : List TreeTagNode} {rootTag : Nat} :
    ∀ {d t : Nat}, ReachesRoot nodes rootTag d t →
      ∀ (fuel x y dx : Nat),
        x ∈ ancestorPathTagsAux nodes fuel t → y ∈ ancestorPathTagsAux nodes fuel t →
        ReachesRoot nodes rootTag dx x → ReachesRoot nodes rootTag dx y → x = y := by
  intro d t hreach
  induction hreach with
  | root r hr hpar =>
    intro fuel x y dx hx hy _ _
    cases fuel with
    | zero =>
      simp only [ancestorPathTagsAux, List.mem_singleton] at hx hy; subst hx; subst hy; rfl
    | succ f =>
      simp only [ancestorPathTagsAux, hr, hpar, List.mem_singleton] at hx hy; subst hx; subst hy; rfl
  | step d t p n hn hpar hprev ih =>
    intro fuel x y dx hx hy hrx hry
    cases fuel with
    | zero =>
      simp only [ancestorPathTagsAux, List.mem_singleton] at hx hy; subst hx; subst hy; rfl
    | succ f =>
      simp only [ancestorPathTagsAux, hn, hpar, List.mem_cons] at hx hy
      rcases hx with rfl | hx' <;> rcases hy with rfl | hy'
      · rfl
      · rcases reachesRoot_of_mem_ancestorPathAux hprev f y hy' with ⟨dy, hdy, hry', _⟩
        have h1 := reachesRoot_unique_depth hrx (ReachesRoot.step d x p n hn hpar hprev)
        have h2 := reachesRoot_unique_depth hry hry'
        omega
      · rcases reachesRoot_of_mem_ancestorPathAux hprev f x hx' with ⟨dx', hdx', hrx', _⟩
        have h1 := reachesRoot_unique_depth hry (ReachesRoot.step d y p n hn hpar hprev)
        have h2 := reachesRoot_unique_depth hrx hrx'
        omega
      · exact ih f x y dx hx' hy' hrx hry

private theorem ancestorPathAux_suffix_of_mem {nodes : List TreeTagNode} {rootTag : Nat} :
    ∀ {d t : Nat}, ReachesRoot nodes rootTag d t →
      ∀ (f₁ f₂ : Nat), d ≤ f₁ → d ≤ f₂ →
        ∀ (x : Nat), x ∈ ancestorPathTagsAux nodes f₁ t →
          ∀ (y : Nat), y ∈ ancestorPathTagsAux nodes f₂ x →
            y ∈ ancestorPathTagsAux nodes f₁ t := by
  intro d t hreach
  induction hreach with
  | root r hr hpar =>
    intro f₁ f₂ _ _ x hx y hy
    cases f₁ with
    | zero =>
      simp only [ancestorPathTagsAux, List.mem_singleton] at hx; subst hx
      cases f₂ <;> simp only [ancestorPathTagsAux, hr, hpar, List.mem_singleton] at hy <;>
        (subst hy; simp [ancestorPathTagsAux])
    | succ f₁' =>
      simp only [ancestorPathTagsAux, hr, hpar, List.mem_singleton] at hx; subst hx
      cases f₂ <;> simp only [ancestorPathTagsAux, hr, hpar, List.mem_singleton] at hy <;>
        (subst hy; simp [ancestorPathTagsAux, hr, hpar])
  | step d t p n hn hpar hprev ih =>
    intro f₁ f₂ hf₁ hf₂ x hx y hy
    obtain ⟨f₁', rfl⟩ : ∃ m, f₁ = m + 1 := ⟨f₁ - 1, by omega⟩
    simp only [ancestorPathTagsAux, hn, hpar, List.mem_cons] at hx ⊢
    rcases hx with rfl | hx'
    · have hEq : ancestorPathTagsAux nodes f₂ x = ancestorPathTagsAux nodes (f₁' + 1) x :=
        ancestorPathTagsAux_fuel_irrel (ReachesRoot.step d x p n hn hpar hprev) f₂ (f₁' + 1) hf₂ hf₁
      rw [hEq] at hy
      simp only [ancestorPathTagsAux, hn, hpar, List.mem_cons] at hy
      exact hy
    · exact Or.inr (ih f₁' f₂ (by omega) (by omega) x hx' y hy)

private theorem mem_foreignPostorder_ancestor {w : FnEntryBorrowWorld} {rootTag : Nat}
    (hwf : BorrowTreeRootedWF w rootTag) (skip : Nat → Bool) :
    ∀ (fuel r x : Nat), (∃ rn ∈ w.nodes, rn.tag = r) →
      x ∈ foreignPostorderTags (childTagsInListOrder w.nodes) skip fuel r →
        r ∈ ancestorPathTags w.nodes x := by
  intro fuel
  induction fuel with
  | zero => intro r x _ hx; simp [foreignPostorderTags] at hx
  | succ fuel ih =>
    intro r x hr hx
    simp only [foreignPostorderTags] at hx
    cases hsk : skip r with
    | true => simp [hsk] at hx
    | false =>
      simp only [hsk, Bool.false_eq_true, ↓reduceIte, List.mem_append, List.mem_flatMap,
        List.mem_reverse, List.mem_singleton] at hx
      rcases hx with ⟨c, hc, hxc⟩ | rfl
      · rcases mem_childTagsInListOrder_iff.mp hc with ⟨cn, hcn, hpar, rfl⟩
        have hcin := ih cn.tag x ⟨cn, hcn, rfl⟩ hxc
        obtain ⟨xn, hxn, rfl⟩ := mem_foreignPostorderTags_mem_nodes skip fuel cn.tag ⟨cn, hcn, rfl⟩ x hxc
        obtain ⟨dx, hdx, hreachX⟩ := hwf.reachesRoot xn hxn
        have hfindC : findNode? w.nodes cn.tag = some cn :=
          findNode?_eq_some_of_mem_of_nodup hwf.tagsNodup hcn
        have hrMemC : r ∈ ancestorPathTags w.nodes cn.tag := by
          unfold ancestorPathTags
          simp only [ancestorPathTagsAux, hfindC, hpar, List.mem_cons]
          right
          exact mem_of_head?_eq_some (ancestorPathTagsAux_head w.nodes w.nodes.length r)
        exact ancestorPathAux_suffix_of_mem hreachX (w.nodes.length + 1) (w.nodes.length + 1)
          (Nat.le_succ_of_le (Nat.le_of_lt hdx)) (Nat.le_succ_of_le (Nat.le_of_lt hdx)) cn.tag hcin r hrMemC
      · rcases hr with ⟨rn, hrn, rfl⟩
        unfold ancestorPathTags
        exact mem_of_head?_eq_some (ancestorPathTagsAux_head w.nodes (w.nodes.length + 1) rn.tag)

private theorem initialForeignRootTags_not_mem_path {nodes : List TreeTagNode} {rootTag : Nat}
    (hnodup : (nodes.map (·.tag)).Nodup) :
    ∀ {d t : Nat}, ReachesRoot nodes rootTag d t →
      ∀ (fuel : Nat), d ≤ fuel →
        ∀ (r : Nat),
          r ∈ initialForeignRootTags (childTagsInListOrder nodes)
                (ancestorPathTagsAux nodes fuel t).tail (some t) →
            r ∉ ancestorPathTagsAux nodes fuel t ∧
            ∃ cur ∈ (ancestorPathTagsAux nodes fuel t).tail,
              r ∈ childTagsInListOrder nodes cur := by
  intro d t hreach
  induction hreach with
  | root r0 hr hpar =>
    intro fuel _ r hmem
    cases fuel with
    | zero => simp [ancestorPathTagsAux, initialForeignRootTags] at hmem
    | succ f => simp [ancestorPathTagsAux, hr, hpar, initialForeignRootTags] at hmem
  | step d t p n hn hpar hprev ih =>
    intro fuel hfuel r hmem
    obtain ⟨f, rfl⟩ : ∃ m, fuel = m + 1 := ⟨fuel - 1, by omega⟩
    have hstep : ancestorPathTagsAux nodes (f + 1) t = t :: ancestorPathTagsAux nodes f p := by
      simp [ancestorPathTagsAux, hn, hpar]
    rw [hstep] at hmem ⊢
    simp only [List.tail_cons] at hmem ⊢
    have hheadP := ancestorPathTagsAux_head nodes f p
    cases hap : ancestorPathTagsAux nodes f p with
    | nil => rw [hap] at hheadP; cases hheadP
    | cons p0 rest =>
      rw [hap] at hheadP; injection hheadP with hp0; subst p0
      rw [hap] at hmem
      simp only [initialForeignRootTags, List.mem_append, List.mem_filter, List.mem_reverse] at hmem
      rcases hmem with ⟨hrc, hne⟩ | hrest
      · have hneT : r ≠ t := by
          intro hEq; subst hEq; simp at hne
        refine ⟨?_, p, List.mem_cons_self, hrc⟩
        have hrNotP : r ∉ ancestorPathTagsAux nodes f p := by
          intro hrp
          rcases mem_childTagsInListOrder_iff.mp hrc with ⟨rn, hrn, hrpar, rfl⟩
          have hfindR := findNode?_eq_some_of_mem_of_nodup hnodup hrn
          have hrReach : ReachesRoot nodes rootTag (d + 1) rn.tag :=
            ReachesRoot.step d rn.tag p rn hfindR hrpar hprev
          rcases reachesRoot_of_mem_ancestorPathAux hprev f rn.tag hrp with ⟨dr, hdr, hrReach', _⟩
          have := reachesRoot_unique_depth hrReach hrReach'
          omega
        rw [hap] at hrNotP
        simp only [List.mem_cons, not_or] at hrNotP ⊢
        exact ⟨hneT, hrNotP⟩
      · have hih := ih f (by omega) r (by rw [hap]; exact hrest)
        rcases hih with ⟨hrNotP, cur, hcur, hrc⟩
        have hcurRest : cur ∈ rest := by simpa [hap] using hcur
        refine ⟨?_, cur, List.mem_cons_of_mem _ hcurRest, hrc⟩
        rw [hap] at hrNotP
        simp only [List.mem_cons, not_or] at hrNotP ⊢
        refine ⟨?_, hrNotP⟩
        intro hrEqT; subst hrEqT
        rcases mem_childTagsInListOrder_iff.mp hrc with ⟨rn, hrn, hrpar, htag⟩
        have hfindR := findNode?_eq_some_of_mem_of_nodup hnodup hrn
        rw [htag, hn] at hfindR; injection hfindR with hEq; subst hEq
        rw [hpar] at hrpar; injection hrpar with hcp; subst hcp
        cases hprev with
        | root r0 hr0 hpar0 =>
          cases f with
          | zero => simp [ancestorPathTagsAux] at hap; cases hap; cases hcurRest
          | succ f' => simp [ancestorPathTagsAux, hr0, hpar0] at hap; cases hap; cases hcurRest
        | step d' _ pp np hnp hparp hprevp =>
          cases f with
          | zero => omega
          | succ f' =>
            simp only [ancestorPathTagsAux, hnp, hparp] at hap
            injection hap with _ hrestEq
            rw [← hrestEq] at hcurRest
            rcases reachesRoot_of_mem_ancestorPathAux hprevp f' p hcurRest with ⟨dp2, hdp2, hrp2, _⟩
            have := reachesRoot_unique_depth hrp2 (ReachesRoot.step d' p pp np hnp hparp hprevp)
            omega

/-- **Protector-end `.SkipChildrenOfAccessed` traversal excludes ALL strict descendants**:
for every rooted, dense-tag borrow tree `w`, every accessed tag `start ∈ w.nodes`, every strict
descendant `d ∈ w.nodes` (`isStrictDescendantOf w.nodes start.tag d = true`), and every `skipNodes`,
NO event (neither `.LocalAccess` nor `.ForeignAccess`) emitted by vendored
`TraversalTree.traverse ... .SkipChildrenOfAccessed` visits `d.tag`. This directly connects the
vendored traversal algorithm to `execProtectorEndAccess_descendants_untouched`. -/
theorem miri_traverse_skipChildren_excludes_strictDescendants {w : FnEntryBorrowWorld}
    {rootTag : Nat} (hwf : BorrowTreeRootedWF w rootTag) (hdense : DenseTags w.nodes)
    {start d : TreeTagNode} (hstart : start ∈ w.nodes) (hd : d ∈ w.nodes)
    (hdesc : isStrictDescendantOf w.nodes start.tag d = true)
    (skipNodes : List Nat) :
    ∀ ev ∈ (Miri.TreeBorrows.Tree.TraversalTree.traverse (traversalTreeOfNodes w.nodes)
        start.tag .SkipChildrenOfAccessed skipNodes).2, ev.node ≠ d.tag := by
  rw [miri_traverse_skipChildren_eq_schedule]
  dsimp only
  rw [← ancestorPathTags_eq_miri_ancestorPath hwf hdense start hstart]
  have hsize : (traversalTreeOfNodes w.nodes).nodes.size = w.nodes.length := by
    unfold traversalTreeOfNodes; rw [List.size_toArray, List.length_map]
  rw [hsize]
  obtain ⟨ds, hds, hreachS⟩ := hwf.reachesRoot start hstart
  obtain ⟨dd, hdd, hreachD⟩ := hwf.reachesRoot d hd
  have hstartInD : start.tag ∈ (ancestorPathTags w.nodes d.tag).tail := by
    unfold isStrictDescendantOf at hdesc
    simpa [List.contains_eq_mem] using hdesc
  have hdsLtDd : ds < dd := by
    cases hreachD with
    | root r hr hpar =>
      unfold ancestorPathTags at hstartInD
      simp [ancestorPathTagsAux, hr, hpar] at hstartInD
    | step d' _ p n hn hpar hprev =>
      unfold ancestorPathTags at hstartInD
      simp only [ancestorPathTagsAux, hn, hpar, List.tail_cons] at hstartInD
      rcases reachesRoot_of_mem_ancestorPathAux hprev w.nodes.length start.tag hstartInD with
        ⟨ds', hds', hrS', _⟩
      have := reachesRoot_unique_depth hreachS hrS'
      omega
  have hstartInDFull : start.tag ∈ ancestorPathTags w.nodes d.tag :=
    List.mem_of_mem_tail hstartInD
  intro ev hev hEq
  simp only [List.mem_append, List.mem_map] at hev
  rcases hev with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
  · -- Local event: t ∈ ancestorPathTags w.nodes start.tag implies depth(t) ≤ ds < dd = depth(d)
    dsimp only at hEq; subst hEq
    rcases reachesRoot_of_mem_ancestorPathAux hreachS (w.nodes.length + 1) d.tag ht with
      ⟨dd', hdd', hrD', _⟩
    have := reachesRoot_unique_depth hreachD hrD'
    omega
  · -- Foreign event: d.tag in subtree of a foreign root r strictly above start
    dsimp only at hEq; subst hEq
    have hpathMem : ∀ x ∈ (ancestorPathTags w.nodes start.tag).tail, ∃ m ∈ w.nodes, m.tag = x :=
      fun x hx => mem_ancestorPathTags_of_reachesRoot hreachS (w.nodes.length + 1) x
        (List.mem_of_mem_tail hx)
    have hrootsEq :
        initialForeignRootTags (traversalChildren (traversalTreeOfNodes w.nodes))
            (ancestorPathTags w.nodes start.tag).tail (some start.tag) =
          initialForeignRootTags (childTagsInListOrder w.nodes)
            (ancestorPathTags w.nodes start.tag).tail (some start.tag) := by
      apply initialForeignRootTags_congr
      intro x hx
      rcases hpathMem x hx with ⟨m, hm, rfl⟩
      exact traversalChildren_traversalTreeOfNodes_of_mem hdense hwf.tagsNodup hm
    rw [hrootsEq, List.mem_flatMap] at ht
    rcases ht with ⟨r, hr, hdr⟩
    rcases initialForeignRootTags_not_mem_path hwf.tagsNodup hreachS (w.nodes.length + 1)
      (by omega) r hr with ⟨hrNotS, cur, hcurTail, hrc⟩
    rcases mem_childTagsInListOrder_iff.mp hrc with ⟨rn, hrn, hrpar, rfl⟩
    rw [foreignPostorderTags_congr_rooted hwf hdense (fun t => skipNodes.contains t)
          (fun t => skipNodes.contains t) (fun _ _ => rfl) w.nodes.length rn hrn] at hdr
    have hrInD : rn.tag ∈ ancestorPathTags w.nodes d.tag :=
      mem_foreignPostorder_ancestor hwf (fun t => skipNodes.contains t)
        w.nodes.length rn.tag d.tag ⟨rn, hrn, rfl⟩ hdr
    -- `cur` is on `start`'s strict tail, so depth(cur) < ds; hence depth(rn) = depth(cur) + 1 ≤ ds.
    have hcurInS : cur ∈ ancestorPathTags w.nodes start.tag := List.mem_of_mem_tail hcurTail
    rcases reachesRoot_of_mem_ancestorPathAux hreachS (w.nodes.length + 1) cur hcurInS with
      ⟨dcur, hdcur, hrCur, hcurNe⟩
    have hdcurLt : dcur < ds := by
      cases hreachS with
      | root r0 hr0 hpar0 =>
        simp [ancestorPathTagsAux, hr0, hpar0] at hcurTail
      | step d' _ p n hn hpar hprev =>
        simp only [ancestorPathTagsAux, hn, hpar, List.tail_cons] at hcurTail
        rcases reachesRoot_of_mem_ancestorPathAux hprev w.nodes.length cur hcurTail with
          ⟨dc', hdc', hrc', _⟩
        have := reachesRoot_unique_depth hrCur hrc'
        omega
    have hrReach : ReachesRoot w.nodes rootTag (dcur + 1) rn.tag :=
      ReachesRoot.step dcur rn.tag cur rn
        (findNode?_eq_some_of_mem_of_nodup hwf.tagsNodup hrn) hrpar hrCur
    -- There exists a node `snode` on `start`'s ancestor path at exact depth `dcur + 1 ≤ ds`.
    have hexistsDepth : ∀ {dm tm : Nat}, ReachesRoot w.nodes rootTag dm tm →
        ∀ (f k : Nat), dm ≤ f → k ≤ dm →
          ∃ y ∈ ancestorPathTagsAux w.nodes f tm, ReachesRoot w.nodes rootTag k y := by
      intro dm tm hrM
      induction hrM with
      | root r0 hr0 hpar0 =>
        intro f k _ hk
        have hk0 : k = 0 := by omega
        subst hk0
        refine ⟨rootTag, ?_, ReachesRoot.root r0 hr0 hpar0⟩
        cases f <;> simp [ancestorPathTagsAux, hr0, hpar0]
      | step dm' tm' pm nm hnm hparm hprevm ihm =>
        intro f k hf hk
        obtain ⟨f', rfl⟩ : ∃ m, f = m + 1 := ⟨f - 1, by omega⟩
        simp only [ancestorPathTagsAux, hnm, hparm, List.mem_cons]
        by_cases hkeq : k = dm' + 1
        · subst hkeq
          exact ⟨tm', Or.inl rfl, ReachesRoot.step dm' tm' pm nm hnm hparm hprevm⟩
        · rcases ihm f' k (by omega) (by omega) with ⟨y, hy, hry⟩
          exact ⟨y, Or.inr hy, hry⟩
    rcases hexistsDepth hreachS (w.nodes.length + 1) (dcur + 1) (by omega) (by omega) with
      ⟨y, hyInS, hryReach⟩
    -- Both `y` and `rn.tag` lie on `d`'s ancestor path at the same depth `dcur + 1`!
    have hyInD : y ∈ ancestorPathTags w.nodes d.tag :=
      ancestorPathAux_suffix_of_mem hreachD (w.nodes.length + 1) (w.nodes.length + 1)
        (by omega) (by omega) start.tag hstartInDFull y hyInS
    have hEqY : rn.tag = y :=
      reachesRoot_unique_at_depth hreachD (w.nodes.length + 1) rn.tag y (dcur + 1)
        hrInD hyInD hrReach hryReach
    rw [hEqY] at hrNotS
    exact hrNotS hyInS

/-! ### Vendored `BorrowTree.releaseProtector` & `MachineHooks.beforeStackPopWithEnsure` Bridge -/

private theorem forIn_list_const {α β : Type} (xs : List α) (b : β)
    (f : α → β → Id (ForInStep β)) (hf : ∀ x ∈ xs, f x b = .yield b) :
    forIn (m := Id) xs b f = b := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    rw [List.forIn_cons, hf x List.mem_cons_self]
    exact ih (fun y hy => hf y (List.mem_cons_of_mem _ hy))

/-- **Missing-tag protector release**: when `tag` is absent from a vendored `BorrowTree`,
`BorrowTree.releaseProtector` returns `.MissingTag tag` without mutating the tree, matching
`execProtectorEndAccessFor protectorEndAccessIsWrite? w t = .error (.missingParentTag t)`. -/
theorem miri_releaseProtector_missingTag (tree : Miri.TreeBorrows.BorrowTree)
    (tag : Miri.Memory.BorTag) (protections : Miri.TreeBorrows.ProtectedTags)
    (hmiss : tree.indexOfTag tag = none) :
    tree.releaseProtector tag protections = ⟨tree, .MissingTag tag⟩ := by
  unfold Miri.TreeBorrows.BorrowTree.releaseProtector
  simp [hmiss, Id.run, pure]

/-- **No-access protector release (`accessed = false` or `.Cell` or unmaterialized)**:
generalizing vendored `ZeroProtection.Release.release` from absent permissions to ALL
locations where `protectorEndAccessIsWrite?` is `none` (absent, unaccessed, or `.Cell`),
`BorrowTree.releaseProtector` skips every location without running any tree access and returns
`⟨tree, .Released⟩` (matching `execProtectorEndAccessFor protectorEndAccessIsWrite? w t = .ok w`). -/
theorem miri_releaseProtector_noAccess_preserves_tree (tree : Miri.TreeBorrows.BorrowTree)
    (tag : Miri.Memory.BorTag) (index : Miri.TreeBorrows.UniIndex)
    (node : Miri.TreeBorrows.TreeNode)
    (tagged : tree.indexOfTag tag = some index)
    (present : tree.nodeAt index = some node)
    (unexposed : node.isExposed = false)
    (hnoAccess : ∀ pos (hvalid : pos < tree.locations.entries.size),
      match tree.locations.entries[pos].data.perms.get index with
      | none => True
      | some st => st.accessed = false ∨ st.permission.associatedAccess = none)
    (protections : Miri.TreeBorrows.ProtectedTags) :
    tree.releaseProtector tag protections = ⟨tree, .Released⟩ := by
  have hexposure : tree.updateExposureForProtectorRelease tag = ⟨tree, .ok ()⟩ := by
    unfold Miri.TreeBorrows.BorrowTree.updateExposureForProtectorRelease
    simp [tagged, present, unexposed, Id.run, pure]
  unfold Miri.TreeBorrows.BorrowTree.releaseProtector
  rw [tagged]
  simp only [Id.run, bind, Bind.bind, pure, Pure.pure,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  rw [forIn_list_const]
  · simp only [hexposure]
  · intro pos hpos
    have hvalid : pos < tree.locations.entries.size := by
      rw [← List.range_eq_range', List.mem_range] at hpos
      exact hpos
    have hidx := Miri.TreeBorrows.BorrowTree.ZeroProtection.Release.index_exact
      tree.locations pos hvalid
    have hna := hnoAccess pos hvalid
    cases hget : tree.locations.entries[pos].data.perms.get index with
    | none => simp only [hidx, hget]
    | some st =>
      rw [hget] at hna
      cases hassoc : st.permission.associatedAccess with
      | none => simp only [hidx, hget, hassoc]
      | some kind =>
        rcases hna with hacc | hcontra
        · simp only [hidx, hget, hassoc, hacc, Bool.false_eq_true, ↓reduceIte]
        · rw [hassoc] at hcontra; cases hcontra

/-- Concrete 4-node vendored `BorrowTree` for protector-release simulation:
root `1` (`.Unique`), protected child `2` (`.Unique`, accessed), sibling `3` (`.Unique`, accessed),
and strict descendant `4` below `2` (`.Unique`, accessed). -/
def releaseProtectorSimTree : Miri.TreeBorrows.BorrowTree :=
  let t1 : Miri.Memory.BorTag := ⟨1, by decide⟩
  let t2 : Miri.Memory.BorTag := ⟨2, by decide⟩
  let t3 : Miri.Memory.BorTag := ⟨3, by decide⟩
  let t4 : Miri.Memory.BorTag := ⟨4, by decide⟩
  let n0 : Miri.TreeBorrows.TreeNode :=
    ⟨t1, none, #[⟨1⟩, ⟨2⟩], .Disabled, .None, false, none⟩
  let n1 : Miri.TreeBorrows.TreeNode :=
    ⟨t2, some ⟨0⟩, #[⟨3⟩], .ReservedFrz false, .None, false, none⟩
  let n2 : Miri.TreeBorrows.TreeNode :=
    ⟨t3, some ⟨0⟩, #[], .ReservedFrz false, .None, false, none⟩
  let n3 : Miri.TreeBorrows.TreeNode :=
    ⟨t4, some ⟨1⟩, #[], .ReservedFrz false, .None, false, none⟩
  let loc : Miri.TreeBorrows.LocationTree :=
    { perms := ⟨#[some ⟨.Unique, true, .None⟩,
                  some ⟨.Unique, true, .None⟩,
                  some ⟨.Unique, true, .None⟩,
                  some ⟨.Unique, true, .None⟩]⟩
      exposedCache := {} }
  { tagMapping := { mapping := #[(t1, ⟨0⟩), (t2, ⟨1⟩), (t3, ⟨2⟩), (t4, ⟨3⟩)], deassigned := #[] }
    nodes := ⟨#[some n0, some n1, some n2, some n3]⟩
    locations := Miri.DataStructures.DedupRangeMap.new ⟨4⟩ loc
    roots := #[⟨0⟩] }

local macro "miriPerformTreeAccessAt" : term =>
  `(miri_etm_private% Miri.TreeBorrows.TreeState Miri.TreeBorrows.BorrowTree.performTreeAccessAt)
local macro "miriNormalProjection" : term =>
  `(miri_etm_private% Miri.TreeBorrows.TreeState Miri.TreeBorrows.BorrowTree.normalProjection)
local macro "miriTLAMk" : term =>
  `(miri_etm_private% Miri.TreeBorrows.TreeState Miri.TreeBorrows.BorrowTree.TreeLocationAccessAtResult.mk)
local macro "miriMinExposedChild" : term =>
  `(miri_etm_private% Miri.TreeBorrows.TreeState Miri.TreeBorrows.BorrowTree.minExposedChild)
local macro "miriBorrowAccessError" : term =>
  `(miri_etm_private% Miri.Interpreter.MachineHooks Miri.Interpreter.MachineHooks.borrowAccessError)

private def releaseProtectorSimLoc : Miri.TreeBorrows.LocationTree :=
  { perms := ⟨#[some ⟨.Unique, true, .None⟩,
                some ⟨.Unique, true, .None⟩,
                some ⟨.Unique, true, .None⟩,
                some ⟨.Unique, true, .None⟩]⟩
    exposedCache := {} }

private theorem releaseProtectorSimTree_performTreeAccessAt
    (prot : Miri.TreeBorrows.ProtectedTags)
    (loc' : Miri.TreeBorrows.LocationTree)
    (acc : Miri.TreeBorrows.Tree.NormalAccessResult)
    (hnorm : releaseProtectorSimTree.performNormalAccessAt releaseProtectorSimLoc ⟨1⟩ .Write
      prot .SkipChildrenOfAccessed = ⟨loc', acc, .ok ()⟩)
    (hroot : acc.root = 0) :
    (acc.status = .Completed →
      miriPerformTreeAccessAt releaseProtectorSimTree releaseProtectorSimLoc (some ⟨1⟩) .Write
        prot .SkipChildrenOfAccessed ⟨⟨0⟩, ⟨4⟩⟩ = miriTLAMk loc' (some acc) none) ∧
    (acc.status ≠ .Completed →
      miriPerformTreeAccessAt releaseProtectorSimTree releaseProtectorSimLoc (some ⟨1⟩) .Write
        prot .SkipChildrenOfAccessed ⟨⟨0⟩, ⟨4⟩⟩ =
        miriTLAMk loc' (some acc) (some (.AccessFailure ⟨⟨0⟩, ⟨4⟩⟩ acc.status))) := by
  have hunf : miriPerformTreeAccessAt releaseProtectorSimTree releaseProtectorSimLoc (some ⟨1⟩)
      .Write prot .SkipChildrenOfAccessed ⟨⟨0⟩, ⟨4⟩⟩ =
      (Id.run do
        let mut currentLocation := releaseProtectorSimLoc
        let mut normalAccess : Option Miri.TreeBorrows.Tree.NormalAccessResult := none
        let mut accessedRoot? : Option Miri.TreeBorrows.UniIndex := none
        let mut status : Option Miri.TreeBorrows.BorrowTree.BorrowTreeAccessStatus := none
        let normal := releaseProtectorSimTree.performNormalAccessAt currentLocation ⟨1⟩ .Write
          prot .SkipChildrenOfAccessed
        currentLocation := normal.location
        normalAccess := some normal.access
        match normal.outcome with
        | .error error =>
          return miriTLAMk currentLocation normalAccess (some (.CacheFailure ⟨⟨0⟩, ⟨4⟩⟩ error))
        | .ok () =>
          if normal.access.status != .Completed then
            return miriTLAMk currentLocation normalAccess
              (some (.AccessFailure ⟨⟨0⟩, ⟨4⟩⟩ normal.access.status))
          match Miri.TreeBorrows.UniIndex.ofNat? normal.access.root with
          | none =>
            return miriTLAMk currentLocation normalAccess
              (some (.AccessFailure ⟨⟨0⟩, ⟨4⟩⟩ (.MissingLocationState normal.access.root)))
          | some root => accessedRoot? := some root
        let maxLocalTag := accessedRoot?.bind fun root =>
          (releaseProtectorSimTree.nodes.get root).map Miri.TreeBorrows.TreeNode.tag
        let minExposed := Option.bind (some (⟨1⟩ : Miri.TreeBorrows.UniIndex))
          (miriMinExposedChild releaseProtectorSimTree)
        let mut stopOtherRoots := false
        for rootPosition in [:releaseProtectorSimTree.roots.size] do
          if status.isNone && !stopOtherRoots then
            match releaseProtectorSimTree.roots[rootPosition]? with
            | none => pure ()
            | some root =>
              let rootTag := (releaseProtectorSimTree.nodes.get root).map Miri.TreeBorrows.TreeNode.tag
              let pastMinExposed : Bool := match rootTag, minExposed with
                | some tag, some minimum => decide (tag.value > minimum.value)
                | _, _ => false
              if pastMinExposed then
                stopOtherRoots := true
              else if accessedRoot? != some root then
                let wildcard := releaseProtectorSimTree.performWildcardAccessAt currentLocation root
                  maxLocalTag .Write prot (rootPosition != 0)
                currentLocation := wildcard.location
                if wildcard.status != .Completed then
                  status := some (.WildcardFailure ⟨⟨0⟩, ⟨4⟩⟩ wildcard.status)
        return miriTLAMk currentLocation normalAccess status) := rfl
  constructor
  · intro hcomp
    rw [hunf]
    dsimp only [Id.run, bind, Bind.bind, pure, Pure.pure]
    rw [hnorm]
    have hof0 : Miri.TreeBorrows.UniIndex.ofNat? 0 = some ⟨0⟩ := by decide
    have hroots : releaseProtectorSimTree.roots = #[⟨0⟩] := rfl
    have htag0 : (releaseProtectorSimTree.nodes.get ⟨0⟩).map Miri.TreeBorrows.TreeNode.tag =
        some ⟨1, by decide⟩ := by decide
    simp only [hcomp, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hroot, hof0, hroots,
      Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Array.size_singleton,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, List.range', List.forIn_cons, List.forIn_nil,
      bind, Bind.bind, pure, Pure.pure, Array.getElem?_singleton, Option.isNone_none,
      Bool.not_false, Bool.and_self, htag0]
    cases Option.bind (some (⟨1⟩ : Miri.TreeBorrows.UniIndex))
        (miriMinExposedChild releaseProtectorSimTree) with
    | none => rfl
    | some minimum =>
      by_cases hgt : (⟨1, by decide⟩ : Miri.Memory.BorTag).value > minimum.value
      · simp [hgt]
      · simp [hgt]
  · intro hne
    rw [hunf]
    dsimp only [Id.run, bind, Bind.bind, pure, Pure.pure]
    rw [hnorm]
    have hbne : (acc.status != .Completed) = true := bne_iff_ne.mpr hne
    simp only [hbne, ↓reduceIte]

/-- **Live vendored `BorrowTree.releaseProtector` simulation** matching `execProtectorEndAccess`,
`execProtectorEndAccess_descendants_untouched`, and `execFrameExit_miri_vs_sequential_separation`:
1. Releasing protected tag `2` while its strict descendant `4` is ALSO protected (sibling `3`
   unprotected) returns `.Released`, disables sibling `3`, and leaves strict descendant `4`
   literally untouched (`.Unique`, accessed) via `.SkipChildrenOfAccessed`.
2. Releasing protected tag `2` while sibling `3` is ALSO protected (same exiting frame, Miri order)
   fails with `.AccessFailure` (`ProtectedDisabled`), whereas releasing tag `2` after removing
   sibling `3`'s protector (sequential MiniRust order) returns `.Released`. -/
theorem miri_releaseProtector_skipChildren_and_siblingConflict :
    let t2 : Miri.Memory.BorTag := ⟨2, by decide⟩
    let t3 : Miri.Memory.BorTag := ⟨3, by decide⟩
    let t4 : Miri.Memory.BorTag := ⟨4, by decide⟩
    let protWithDesc : Miri.TreeBorrows.ProtectedTags :=
      ⟨#[(t2, .StrongProtector), (t4, .StrongProtector)]⟩
    let protWithSib : Miri.TreeBorrows.ProtectedTags :=
      ⟨#[(t2, .StrongProtector), (t3, .StrongProtector)]⟩
    let protAfterSibPop : Miri.TreeBorrows.ProtectedTags :=
      ⟨#[(t2, .StrongProtector)]⟩
    let resDesc := releaseProtectorSimTree.releaseProtector t2 protWithDesc
    let resSib := releaseProtectorSimTree.releaseProtector t2 protWithSib
    let resAfterPop := releaseProtectorSimTree.releaseProtector t2 protAfterSibPop
    resDesc.status = .Released ∧
    ((resDesc.tree.locations.entries[0]?.bind fun seg => seg.data.perms.get ⟨2⟩).map
      fun s => (s.permission, s.accessed)) = some (.Disabled, true) ∧
    (resDesc.tree.locations.entries[0]?.bind fun seg => seg.data.perms.get ⟨3⟩) =
      some ⟨.Unique, true, .None⟩ ∧
    (match resSib.status with | .AccessFailure _ _ => true | _ => false) = true ∧
    resAfterPop.status = .Released := by
  intro t2 t3 t4 protWithDesc protWithSib protAfterSibPop resDesc resSib resAfterPop
  have hrun : ∀ (prot : Miri.TreeBorrows.ProtectedTags) (loc' : Miri.TreeBorrows.LocationTree)
      (acc : Miri.TreeBorrows.Tree.NormalAccessResult),
      releaseProtectorSimTree.performNormalAccessAt releaseProtectorSimLoc ⟨1⟩ .Write
        prot .SkipChildrenOfAccessed = ⟨loc', acc, .ok ()⟩ →
      acc.root = 0 →
      (acc.status = .Completed →
        releaseProtectorSimTree.releaseProtector t2 prot =
          ⟨{ releaseProtectorSimTree with
             locations := (releaseProtectorSimTree.locations.setAtPos 0 loc').state }, .Released⟩) ∧
      (acc.status ≠ .Completed →
        releaseProtectorSimTree.releaseProtector t2 prot =
          ⟨{ releaseProtectorSimTree with
             locations := (releaseProtectorSimTree.locations.setAtPos 0 loc').state },
            .AccessFailure ⟨⟨0⟩, ⟨4⟩⟩ (.AccessFailure ⟨⟨0⟩, ⟨4⟩⟩ acc.status)⟩) := by
    intro prot loc' acc hnorm hroot
    have hta := releaseProtectorSimTree_performTreeAccessAt prot loc' acc hnorm hroot
    have hidx : releaseProtectorSimTree.indexOfTag t2 = some ⟨1⟩ := by decide
    have hsetOk : (releaseProtectorSimTree.locations.setAtPos 0 loc').outcome = .ok () := rfl
    have hexp : ({ releaseProtectorSimTree with
        locations := (releaseProtectorSimTree.locations.setAtPos 0 loc').state }).updateExposureForProtectorRelease t2 =
        ⟨{ releaseProtectorSimTree with
           locations := (releaseProtectorSimTree.locations.setAtPos 0 loc').state }, .ok ()⟩ := by
      unfold Miri.TreeBorrows.BorrowTree.updateExposureForProtectorRelease
      have hnode : releaseProtectorSimTree.nodeAt ⟨1⟩ =
          some ⟨t2, some ⟨0⟩, #[⟨3⟩], .ReservedFrz false, .None, false, none⟩ := by decide
      have hidx' : ({ releaseProtectorSimTree with
          locations := (releaseProtectorSimTree.locations.setAtPos 0 loc').state }).indexOfTag t2 =
          some ⟨1⟩ := hidx
      have hnode' : ({ releaseProtectorSimTree with
          locations := (releaseProtectorSimTree.locations.setAtPos 0 loc').state }).nodeAt ⟨1⟩ =
          some ⟨t2, some ⟨0⟩, #[⟨3⟩], .ReservedFrz false, .None, false, none⟩ := hnode
      simp [hidx', hnode', Id.run, pure]
    constructor
    · intro hcomp
      unfold Miri.TreeBorrows.BorrowTree.releaseProtector
      rw [hidx]
      simp only [Id.run, bind, Bind.bind, pure, Pure.pure,
        Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
        Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
      have hsz : releaseProtectorSimTree.locations.entries.size = 1 := by decide
      rw [hsz]
      simp only [List.range', List.forIn_cons, List.forIn_nil, bind, Bind.bind, pure, Pure.pure]
      have hseg : releaseProtectorSimTree.locations.index 0 =
          .ok ⟨⟨⟨0⟩, ⟨4⟩⟩, releaseProtectorSimLoc⟩ := by decide
      rw [hseg]
      have hget : releaseProtectorSimLoc.perms.get ⟨1⟩ = some ⟨.Unique, true, .None⟩ := by decide
      simp only [hget, Miri.TreeBorrows.Permission.associatedAccess, ↓reduceIte]
      rw [hta.1 hcomp]
      simp only [hsetOk, hexp]
    · intro hne
      unfold Miri.TreeBorrows.BorrowTree.releaseProtector
      rw [hidx]
      simp only [Id.run, bind, Bind.bind, pure, Pure.pure,
        Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
        Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
      have hsz : releaseProtectorSimTree.locations.entries.size = 1 := by decide
      rw [hsz]
      simp only [List.range', List.forIn_cons, List.forIn_nil, bind, Bind.bind, pure, Pure.pure]
      have hseg : releaseProtectorSimTree.locations.index 0 =
          .ok ⟨⟨⟨0⟩, ⟨4⟩⟩, releaseProtectorSimLoc⟩ := by decide
      rw [hseg]
      have hget : releaseProtectorSimLoc.perms.get ⟨1⟩ = some ⟨.Unique, true, .None⟩ := by decide
      simp only [hget, Miri.TreeBorrows.Permission.associatedAccess, ↓reduceIte]
      rw [hta.2 hne]
      simp only [hsetOk]
  have hnormEval : ∀ (prot : Miri.TreeBorrows.ProtectedTags)
      (res : Miri.TreeBorrows.Tree.NormalAccessResult)
      (s0 s1 s2 s3 : Miri.TreeBorrows.Tree.LocationState),
      (Miri.TreeBorrows.Tree.NormalTreeState.performAccess
        (miriNormalProjection releaseProtectorSimTree releaseProtectorSimLoc prot)
        1 .Write .SkipChildrenOfAccessed) = res →
      res.visited = [⟨1, .LocalAccess⟩, ⟨0, .LocalAccess⟩, ⟨2, .ForeignAccess⟩] →
      res.tree.locationStates = #[some s0, some s1, some s2, some s3] →
      releaseProtectorSimTree.performNormalAccessAt releaseProtectorSimLoc ⟨1⟩ .Write
        prot .SkipChildrenOfAccessed =
        ⟨{ perms := ⟨#[some s0, some s1, some s2, some s3]⟩
           exposedCache := {} }, res, .ok ()⟩ := by
    intro prot res s0 s1 s2 s3 hpa hvis hls
    unfold Miri.TreeBorrows.BorrowTree.performNormalAccessAt
    change (Id.run do
      let access := Miri.TreeBorrows.Tree.NormalTreeState.performAccess
        (miriNormalProjection releaseProtectorSimTree releaseProtectorSimLoc prot)
        1 .Write .SkipChildrenOfAccessed
      let mut nextLocation := releaseProtectorSimLoc
      for position in [:access.tree.locationStates.size] do
        match access.tree.locationStates[position]? with
        | some (some state) =>
          match Miri.TreeBorrows.UniIndex.ofNat? position with
          | some index =>
            nextLocation := { nextLocation with perms := nextLocation.perms.insert index state }
          | none => pure ()
        | _ => pure ()
      let mut cacheOutcome : Except Miri.TreeBorrows.ExposedCacheError Unit := .ok ()
      for event in access.visited do
        if cacheOutcome matches .ok _ then
          match Miri.TreeBorrows.UniIndex.ofNat? event.node with
          | none => cacheOutcome := .error (.InvalidIndex event.node)
          | some index =>
            match releaseProtectorSimTree.nodeAt index with
            | none => cacheOutcome := .error (.MissingNode index)
            | some node =>
              if node.isExposed &&
                  (miri_etm_private% Miri.TreeBorrows.TreeState Miri.TreeBorrows.BorrowTree.failingNode?)
                    access.status != some event.node then
                match releaseProtectorSimTree.locationStateAt releaseProtectorSimLoc index,
                    access.tree.stateAt event.node with
                | some oldState, some newState =>
                  match Miri.TreeBorrows.performAccessTransition .Write event.relatedness
                      oldState.permission (prot.contains node.tag) with
                  | .Transition transition =>
                    if !transition.isNoop then
                      let oldLevel := oldState.permission.strongestAllowedLocalAccess
                        (prot.contains node.tag)
                      let newLevel := newState.permission.strongestAllowedLocalAccess
                        (prot.contains node.tag)
                      let update := nextLocation.exposedCache.updateExposure
                        releaseProtectorSimTree.nodes index oldLevel newLevel
                      nextLocation := { nextLocation with exposedCache := update.cache }
                      cacheOutcome := update.outcome
                  | .UndefinedBehavior | .ImpossibleProtectedReservedIM => pure ()
                | _, _ => cacheOutcome := .error (.MissingNode index)
      return (⟨nextLocation, access, cacheOutcome⟩ :
        Miri.TreeBorrows.BorrowTree.NormalLocationAccessResult)) = _
    rw [hpa]
    have hof0 : Miri.TreeBorrows.UniIndex.ofNat? 0 = some ⟨0⟩ := by decide
    have hof1 : Miri.TreeBorrows.UniIndex.ofNat? 1 = some ⟨1⟩ := by decide
    have hof2 : Miri.TreeBorrows.UniIndex.ofNat? 2 = some ⟨2⟩ := by decide
    have hof3 : Miri.TreeBorrows.UniIndex.ofNat? 3 = some ⟨3⟩ := by decide
    have hn0 : releaseProtectorSimTree.nodeAt ⟨0⟩ =
        some ⟨⟨1, by decide⟩, none, #[⟨1⟩, ⟨2⟩], .Disabled, .None, false, none⟩ := by decide
    have hn1 : releaseProtectorSimTree.nodeAt ⟨1⟩ =
        some ⟨t2, some ⟨0⟩, #[⟨3⟩], .ReservedFrz false, .None, false, none⟩ := by decide
    have hn2 : releaseProtectorSimTree.nodeAt ⟨2⟩ =
        some ⟨t3, some ⟨0⟩, #[], .ReservedFrz false, .None, false, none⟩ := by decide
    have hsz4 : (#[some s0, some s1, some s2, some s3] :
        Array (Option Miri.TreeBorrows.Tree.LocationState)).size = 4 := rfl
    have hg0 : (#[some s0, some s1, some s2, some s3] :
        Array (Option Miri.TreeBorrows.Tree.LocationState))[0]? = some (some s0) := rfl
    have hg1 : (#[some s0, some s1, some s2, some s3] :
        Array (Option Miri.TreeBorrows.Tree.LocationState))[1]? = some (some s1) := rfl
    have hg2 : (#[some s0, some s1, some s2, some s3] :
        Array (Option Miri.TreeBorrows.Tree.LocationState))[2]? = some (some s2) := rfl
    have hg3 : (#[some s0, some s1, some s2, some s3] :
        Array (Option Miri.TreeBorrows.Tree.LocationState))[3]? = some (some s3) := rfl
    have hins4 : ((((releaseProtectorSimLoc.perms.insert ⟨0⟩ s0).insert ⟨1⟩ s1).insert ⟨2⟩ s2).insert
        ⟨3⟩ s3) = ⟨#[some s0, some s1, some s2, some s3]⟩ := by
      simp [releaseProtectorSimLoc, Miri.TreeBorrows.UniValMap.insert,
        Miri.TreeBorrows.UniValMap.extendTo, Miri.TreeBorrows.UniIndex.toNat,
        Id.run, pure, Pure.pure]
    simp only [hvis, hls, hsz4, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, List.range', List.forIn_cons, List.forIn_nil,
      Id.run, bind, Bind.bind, pure, Pure.pure,
      hg0, hg1, hg2, hg3, hof0, hof1, hof2, hof3, hn0, hn1, hn2, Bool.false_and,
      Bool.false_eq_true, ↓reduceIte, hins4]
    rfl
  let normState (prots : List Nat) : Miri.TreeBorrows.Tree.NormalTreeState :=
    { topology := ⟨#[⟨none, [1, 2]⟩, ⟨some 0, [3]⟩, ⟨some 0, []⟩, ⟨some 1, []⟩]⟩
      defaultStates := #[⟨.Disabled, false, .None⟩, ⟨.ReservedFrz false, false, .None⟩,
        ⟨.ReservedFrz false, false, .None⟩, ⟨.ReservedFrz false, false, .None⟩]
      protectedNodes := prots
      locationStates := #[some ⟨.Unique, true, .None⟩, some ⟨.Unique, true, .None⟩,
        some ⟨.Unique, true, .None⟩, some ⟨.Unique, true, .None⟩] }
  have hprojD : miriNormalProjection releaseProtectorSimTree releaseProtectorSimLoc protWithDesc =
      normState [1, 3] := by decide +kernel
  have hprojS : miriNormalProjection releaseProtectorSimTree releaseProtectorSimLoc protWithSib =
      normState [1, 2] := by decide +kernel
  have hprojP : miriNormalProjection releaseProtectorSimTree releaseProtectorSimLoc protAfterSibPop =
      normState [1] := by decide +kernel
  let accD := (normState [1, 3]).performAccess 1 .Write .SkipChildrenOfAccessed
  let accS := (normState [1, 2]).performAccess 1 .Write .SkipChildrenOfAccessed
  let accP := (normState [1]).performAccess 1 .Write .SkipChildrenOfAccessed
  have hnd := hnormEval protWithDesc accD
    ⟨.Unique, true, .None⟩ ⟨.Unique, true, .None⟩ ⟨.Disabled, true, .Write⟩ ⟨.Unique, true, .None⟩
    (by rw [hprojD]) (by decide) (by decide)
  have hns := hnormEval protWithSib accS
    ⟨.Unique, true, .None⟩ ⟨.Unique, true, .None⟩ ⟨.Disabled, true, .Write⟩ ⟨.Unique, true, .None⟩
    (by rw [hprojS]) (by decide) (by decide)
  have hnp := hnormEval protAfterSibPop accP
    ⟨.Unique, true, .None⟩ ⟨.Unique, true, .None⟩ ⟨.Disabled, true, .Write⟩ ⟨.Unique, true, .None⟩
    (by rw [hprojP]) (by decide) (by decide)
  have hresD := (hrun protWithDesc _ accD hnd (by decide)).1 (by decide)
  have hresS := (hrun protWithSib _ accS hns (by decide)).2 (by decide)
  have hresP := (hrun protAfterSibPop _ accP hnp (by decide)).1 (by decide)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change (releaseProtectorSimTree.releaseProtector t2 protWithDesc).status = .Released
    rw [hresD]
  · change ((releaseProtectorSimTree.releaseProtector t2 protWithDesc).tree.locations.entries[0]?.bind
      fun seg => seg.data.perms.get ⟨2⟩).map (fun s => (s.permission, s.accessed)) =
      some (.Disabled, true)
    rw [hresD]; decide
  · change ((releaseProtectorSimTree.releaseProtector t2 protWithDesc).tree.locations.entries[0]?.bind
      fun seg => seg.data.perms.get ⟨3⟩) = some ⟨.Unique, true, .None⟩
    rw [hresD]; decide
  · change (match (releaseProtectorSimTree.releaseProtector t2 protWithSib).status with
      | .AccessFailure _ _ => true | _ => false) = true
    rw [hresS]
  · change (releaseProtectorSimTree.releaseProtector t2 protAfterSibPop).status = .Released
    rw [hresP]

/-- **`MachineHooks.beforeStackPopWithEnsure` retains ALL frame protectors until `endCall`**
(connecting vendored `MachineHooks.lean:392-429` directly to `execFrameExitMiri` vs
`execFrameExitMiniRust`): for a 2-protector exiting frame `#[(id₁, tag₁), (id₂, tag₂)]` on live
allocations:
1. If the first `releaseProtector` fails with `.AccessFailure`, `beforeStackPopWithEnsure` commits
   the updated borrow tree into `memory`, throws `borrowAccessError`, and leaves
   `borrowTracker.global.protectedTags` UNCHANGED (never calling `endCall`).
2. If the first `releaseProtector` returns `.Released`, the second `releaseProtector` is executed
   with the **EXACT SAME** `tracker.global.protectedTags` (no protector is removed between
   releases!), and `tracker.global.endCall borrowFrame` runs ONLY after both succeed. -/
theorem miri_beforeStackPopWithEnsure_retains_protectors_until_endCall
    {K User : Type} [DecidableEq K]
    (st : Miri.Interpreter.MachineHooks.State K User)
    (tracker : Miri.Interpreter.MachineHooks.BorrowState)
    (frame : Miri.Interpreter.Frame Miri.Memory.Provenance Miri.Interpreter.LocalLayout
      Miri.Interpreter.MachineHooks.FrameExtra)
    (id₁ id₂ : Miri.Memory.AllocId) (tag₁ tag₂ : Miri.Memory.BorTag)
    (entry₁ : Miri.Memory.LocalAllocation Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree K)
    (htracker : st.machine.borrowTracker = some tracker)
    (hframe : st.stack.currentFrame? = some frame)
    (hbf : frame.extra.borrowTracker = some ⟨#[(id₁, tag₁), (id₂, tag₂)]⟩)
    (hlive₁ : st.machine.memory.live.find? (fun e => e.1 == id₁) = some (id₁, entry₁)) :
    let rel₁ := entry₁.allocation.extra.releaseProtector tag₁ tracker.global.protectedTags
    let mem₁ : Miri.Memory.MemoryState Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree K :=
      { st.machine.memory with
        live := (st.machine.memory.live.filter fun row => row.1 != id₁).push
          (id₁, { entry₁ with allocation := entry₁.allocation.setExtra rel₁.tree }) }
    (∀ r status, rel₁.status = .AccessFailure r status →
      ∃ err, Miri.Interpreter.MachineHooks.beforeStackPopWithEnsure (fun _ => pure ()) st =
        .error err { st with machine := { st.machine with memory := mem₁ } }) ∧
    (∀ entry₂,
      rel₁.status = .Released →
      mem₁.live.find? (fun e => e.1 == id₂) = some (id₂, entry₂) →
      let rel₂ := entry₂.allocation.extra.releaseProtector tag₂ tracker.global.protectedTags
      rel₂.status = .Released →
      let mem₂ : Miri.Memory.MemoryState Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree K :=
        { mem₁ with
          live := (mem₁.live.filter fun row => row.1 != id₂).push
            (id₂, { entry₂ with allocation := entry₂.allocation.setExtra rel₂.tree }) }
      Miri.Interpreter.MachineHooks.beforeStackPopWithEnsure (fun _ => pure ()) st =
        .ok () { st with machine := { st.machine with
          memory := mem₂
          borrowTracker := some { tracker with
            global := tracker.global.endCall ⟨#[(id₁, tag₁), (id₂, tag₂)]⟩ } } }) := by
  dsimp only
  let rel₁ := entry₁.allocation.extra.releaseProtector tag₁ tracker.global.protectedTags
  let mem₁ : Miri.Memory.MemoryState Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree K :=
    { st.machine.memory with
      live := (st.machine.memory.live.filter fun row => row.1 != id₁).push
        (id₁, { entry₁ with allocation := entry₁.allocation.setExtra rel₁.tree }) }
  have hinfo₁ : st.machine.memory.getAllocInfo id₁ =
      .ok ⟨entry₁.allocation.byteSize, entry₁.allocation.align, .liveData,
           entry₁.allocation.mutability⟩ := by
    unfold Miri.Memory.MemoryState.getAllocInfo
    simp [hlive₁, pure, Except.pure]
  have hset₁ : st.machine.memory.setLiveAllocation id₁
      (entry₁.allocation.setExtra
        (entry₁.allocation.extra.releaseProtector tag₁ tracker.global.protectedTags).tree) =
      .ok mem₁ :=
    Miri.Memory.MemoryState.setLiveAllocation_of_find st.machine.memory id₁ entry₁ _ hlive₁
  constructor
  · intro r status hfail
    refine ⟨miriBorrowAccessError status, ?_⟩
    unfold Miri.Interpreter.MachineHooks.beforeStackPopWithEnsure
      Miri.Interpreter.MachineHooks.currentFrame
    simp only [htracker, Option.isSome_some, ↓reduceIte, hframe, hbf,
      get, getThe, MonadStateOf.get, EStateM.get,
      modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
      bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure,
      throw, throwThe, MonadExceptOf.throw, EStateM.throw,
      ← Array.forIn_toList, List.forIn_cons,
      hinfo₁, beq_self_eq_true, hlive₁, hset₁, hfail]
    rfl
  · intro entry₂ hok₁ hlive₂ hok₂
    have hlive₂' : mem₁.live.find? (fun e => e.1 == id₂) = some (id₂, entry₂) := hlive₂
    let rel₂ := entry₂.allocation.extra.releaseProtector tag₂ tracker.global.protectedTags
    let mem₂ : Miri.Memory.MemoryState Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree K :=
      { mem₁ with
        live := (mem₁.live.filter fun row => row.1 != id₂).push
          (id₂, { entry₂ with allocation := entry₂.allocation.setExtra rel₂.tree }) }
    have hinfo₂ : mem₁.getAllocInfo id₂ =
        .ok ⟨entry₂.allocation.byteSize, entry₂.allocation.align, .liveData,
             entry₂.allocation.mutability⟩ := by
      unfold Miri.Memory.MemoryState.getAllocInfo
      simp [hlive₂', pure, Except.pure]
    have hset₂ : mem₁.setLiveAllocation id₂
        (entry₂.allocation.setExtra
          (entry₂.allocation.extra.releaseProtector tag₂ tracker.global.protectedTags).tree) =
        .ok mem₂ :=
      Miri.Memory.MemoryState.setLiveAllocation_of_find mem₁ id₂ entry₂ _ hlive₂'
    unfold Miri.Interpreter.MachineHooks.beforeStackPopWithEnsure
      Miri.Interpreter.MachineHooks.currentFrame
    simp only [htracker, Option.isSome_some, ↓reduceIte, hframe, hbf,
      get, getThe, MonadStateOf.get, EStateM.get, set, MonadStateOf.set, EStateM.set,
      modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
      bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure,
      ← Array.forIn_toList, List.forIn_cons, List.forIn_nil,
      hinfo₁, beq_self_eq_true, hlive₁, hset₁, hok₁, hinfo₂, hlive₂', hset₂, hok₂]
    rfl

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

/-! ### Part 2A. General `VTable` Correspondence (`lean-miri#75`): `checkForTypeRead`, `stableKey` Separation, `getPtrVTableTypeRead`, `getSizeAndAlignRead`, Salted `getPointer`, & Upcasting -/

local macro "miriInsertPredicate" : term =>
  `(miri_etm_private% Miri.Interpreter.VTable Miri.Interpreter.VTable.insertPredicate)

/-- Non-auto predicates have injective `stableKey` (matching rustc's total `StableOrd` on
existential predicates, and holding trivially for EVERY principal-less or single-principal
existential `dyn [Principal] + Auto1 + ... + AutoK`). -/
def PredsKeyInjective (preds : List VTablePredSpec) : Prop :=
  ∀ p ∈ preds, ∀ q ∈ preds, p.autoTrait = false → q.autoTrait = false →
    p.stableKey = q.stableKey → p.id = q.id

private theorem predSpecToMiri_filter_nonAuto (preds : List VTablePredSpec) :
    (preds.map predSpecToMiri).filter (fun q => !q.autoTrait) =
      (preds.filter (fun q => !q.autoTrait)).map predSpecToMiri := by
  induction preds with
  | nil => rfl
  | cons p rest ih =>
    simp only [List.map_cons, List.filter_cons, predSpecToMiri]
    cases hp : p.autoTrait <;> simp [ih, predSpecToMiri, hp]

private def insertPredUnique (p : Miri.Interpreter.VTablePredicate) :
    List Miri.Interpreter.VTablePredicate → List Miri.Interpreter.VTablePredicate
  | [] => [p]
  | h :: t =>
    if p.stableKey < h.stableKey then p :: h :: t
    else if p.stableKey == h.stableKey then h :: t
    else h :: insertPredUnique p t

private theorem mem_miriInsertPredicate_iff (p x : Miri.Interpreter.VTablePredicate)
    (ys : List Miri.Interpreter.VTablePredicate) :
    x ∈ miriInsertPredicate p ys ↔ x = p ∨ x ∈ ys := by
  induction ys with
  | nil =>
    have hunf : miriInsertPredicate p [] = [p] := rfl
    rw [hunf]; simp
  | cons h t ih =>
    have hunf : miriInsertPredicate p (h :: t) =
        if p.stableKey ≤ h.stableKey then p :: h :: t else h :: miriInsertPredicate p t := rfl
    rw [hunf]
    by_cases hle : p.stableKey ≤ h.stableKey
    · simp only [hle, ↓reduceIte, List.mem_cons]
    · simp only [hle, ↓reduceIte, List.mem_cons, ih]
      exact ⟨fun h1 => by rcases h1 with rfl | rfl | ht; exact Or.inr (Or.inl rfl); exact Or.inl rfl; exact Or.inr (Or.inr ht),
        fun h2 => by rcases h2 with rfl | rfl | ht; exact Or.inr (Or.inl rfl); exact Or.inl rfl; exact Or.inr (Or.inr ht)⟩

private theorem mem_miriSortPredicates_iff (xs : List Miri.Interpreter.VTablePredicate)
    (x : Miri.Interpreter.VTablePredicate) :
    x ∈ miriSortPredicates xs ↔ x ∈ xs := by
  induction xs with
  | nil =>
    have hunf : miriSortPredicates [] = [] := rfl
    rw [hunf]
  | cons h t ih =>
    have hunf : miriSortPredicates (h :: t) = miriInsertPredicate h (miriSortPredicates t) := rfl
    rw [hunf, mem_miriInsertPredicate_iff, ih, List.mem_cons]

private theorem eraseDups_cons_eq {α : Type} [BEq α] [LawfulBEq α] (a : α) (xs : List α) :
    (a :: xs).eraseDups = a :: (xs.filter (fun x => !(x == a))).eraseDups := by
  have hgo : ∀ (ys seen : List α),
      List.eraseDupsBy.loop (· == ·) ys (seen ++ [a]) =
        a :: List.eraseDupsBy.loop (· == ·) (ys.filter (fun x => !(x == a))) seen := by
    intro ys
    induction ys with
    | nil =>
      intro seen
      simp [List.eraseDupsBy.loop, List.reverse_append]
    | cons y rest ih =>
      intro seen
      cases hbeq : (y == a) with
      | true =>
        have hya : y = a := eq_of_beq hbeq
        subst hya
        have hmem : (seen ++ [y]).any (fun z => y == z) = true := by
          rw [List.any_eq_true]
          exact ⟨y, List.mem_append_right seen List.mem_cons_self, beq_self_eq_true y⟩
        simp only [List.eraseDupsBy.loop, hmem, ↓reduceIte, List.filter_cons,
          beq_self_eq_true, Bool.not_true, Bool.false_eq_true]
        exact ih seen
      | false =>
        have hany : (seen ++ [a]).any (fun z => y == z) = seen.any (fun z => y == z) := by
          simp [List.any_append, hbeq]
        simp only [List.eraseDupsBy.loop, hany, List.filter_cons, hbeq, Bool.not_false, ↓reduceIte]
        cases seen.any (fun z => y == z) with
        | true => exact ih seen
        | false => exact ih (y :: seen)
  unfold List.eraseDups List.eraseDupsBy
  simp only [List.eraseDupsBy.loop, List.any_nil]
  exact hgo xs []

private theorem filter_ne_self_of_not_mem {α : Type} [BEq α] [LawfulBEq α]
    (a : α) (xs : List α) (hnot : a ∉ xs) :
    xs.filter (fun x => !(x == a)) = xs := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    have hne : x ≠ a := fun h => hnot (h ▸ List.mem_cons_self)
    have hb : (x == a) = false := beq_false_of_ne hne
    simp only [List.filter_cons, hb, Bool.not_false, ↓reduceIte,
      ih (fun hm => hnot (List.mem_cons_of_mem _ hm))]

private theorem eraseDups_cons_of_not_mem {α : Type} [BEq α] [LawfulBEq α]
    (a : α) (xs : List α) (hnot : a ∉ xs) :
    (a :: xs).eraseDups = a :: xs.eraseDups := by
  rw [eraseDups_cons_eq, filter_ne_self_of_not_mem a xs hnot]

private theorem eraseDups_cons_dup {α : Type} [BEq α] [LawfulBEq α]
    (a : α) (xs : List α) :
    (a :: a :: xs).eraseDups = (a :: xs).eraseDups := by
  rw [eraseDups_cons_eq, List.filter_cons]
  simp only [beq_self_eq_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [← eraseDups_cons_eq]

private theorem miriInsertPredicate_pairwise (p : Miri.Interpreter.VTablePredicate)
    (ys : List Miri.Interpreter.VTablePredicate)
    (hs : ys.Pairwise (fun a b => a.stableKey ≤ b.stableKey)) :
    (miriInsertPredicate p ys).Pairwise (fun a b => a.stableKey ≤ b.stableKey) := by
  induction ys with
  | nil =>
    have hunf : miriInsertPredicate p [] = [p] := rfl
    rw [hunf]; exact List.pairwise_singleton _ _
  | cons h t ih =>
    rw [List.pairwise_cons] at hs
    have hunf : miriInsertPredicate p (h :: t) =
        if p.stableKey ≤ h.stableKey then p :: h :: t else h :: miriInsertPredicate p t := rfl
    rw [hunf]
    by_cases hle : p.stableKey ≤ h.stableKey
    · simp only [hle, ↓reduceIte, List.pairwise_cons]
      refine ⟨fun x hx => ?_, hs.1, hs.2⟩
      simp only [List.mem_cons] at hx
      rcases hx with rfl | ht
      · exact hle
      · exact Nat.le_trans hle (hs.1 x ht)
    · simp only [hle, ↓reduceIte, List.pairwise_cons]
      refine ⟨fun x hx => ?_, ih hs.2⟩
      rw [mem_miriInsertPredicate_iff] at hx
      rcases hx with rfl | ht
      · omega
      · exact hs.1 x ht

private theorem miriSortPredicates_pairwise (xs : List Miri.Interpreter.VTablePredicate) :
    (miriSortPredicates xs).Pairwise (fun a b => a.stableKey ≤ b.stableKey) := by
  induction xs with
  | nil => exact List.Pairwise.nil
  | cons h t ih =>
    have hunf : miriSortPredicates (h :: t) = miriInsertPredicate h (miriSortPredicates t) := rfl
    rw [hunf]
    exact miriInsertPredicate_pairwise h _ ih

private theorem miriInsertPredicate_filter_ne_comm
    (p h : Miri.Interpreter.VTablePredicate) (hgt : h.stableKey < p.stableKey)
    (l : List Miri.Interpreter.VTablePredicate) :
    (miriInsertPredicate p l).filter (fun x => !(x == h)) =
      miriInsertPredicate p (l.filter (fun x => !(x == h))) := by
  have hpNeH : p ≠ h := fun hEq => by subst hEq; omega
  have hpb : (!(p == h)) = true := by simp [beq_false_of_ne hpNeH]
  induction l with
  | nil =>
    have h1 : miriInsertPredicate p [] = [p] := rfl
    simp [h1, hpb]
  | cons y rest ihr =>
    have h1 : miriInsertPredicate p (y :: rest) =
        if p.stableKey ≤ y.stableKey then p :: y :: rest else y :: miriInsertPredicate p rest := rfl
    rw [h1]
    by_cases hpy : p.stableKey ≤ y.stableKey
    · simp only [hpy, ↓reduceIte, List.filter_cons, hpb]
      cases hyh : !(y == h) with
      | true =>
        simp only [↓reduceIte]
        have h2 : miriInsertPredicate p (y :: rest.filter (fun x => !(x == h))) =
            if p.stableKey ≤ y.stableKey then p :: y :: rest.filter (fun x => !(x == h))
            else y :: miriInsertPredicate p (rest.filter (fun x => !(x == h))) := rfl
        rw [h2]; simp [hpy]
      | false =>
        have hyEqH : y = h := eq_of_beq (by simpa using hyh)
        subst hyEqH; omega
    · simp only [hpy, ↓reduceIte, List.filter_cons]
      cases hyh : !(y == h) with
      | true =>
        simp only [↓reduceIte]
        have h2 : miriInsertPredicate p (y :: rest.filter (fun x => !(x == h))) =
            if p.stableKey ≤ y.stableKey then p :: y :: rest.filter (fun x => !(x == h))
            else y :: miriInsertPredicate p (rest.filter (fun x => !(x == h))) := rfl
        rw [h2]
        simp only [hpy, ↓reduceIte, ihr]
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, ihr]

private theorem miriInsertPredicate_eraseDups_keyInj
    (p : Miri.Interpreter.VTablePredicate) (ys : List Miri.Interpreter.VTablePredicate)
    (hsorted : ys.Pairwise (fun a b => a.stableKey ≤ b.stableKey))
    (hinj : ∀ a ∈ p :: ys, ∀ b ∈ p :: ys, a.stableKey = b.stableKey → a = b) :
    (miriInsertPredicate p ys).eraseDups = insertPredUnique p ys.eraseDups := by
  suffices h : ∀ n (ys : List Miri.Interpreter.VTablePredicate), ys.length ≤ n →
      ys.Pairwise (fun a b => a.stableKey ≤ b.stableKey) →
      (∀ a ∈ p :: ys, ∀ b ∈ p :: ys, a.stableKey = b.stableKey → a = b) →
      (miriInsertPredicate p ys).eraseDups = insertPredUnique p ys.eraseDups from
    h ys.length ys (Nat.le_refl _) hsorted hinj
  intro n
  induction n with
  | zero =>
    intro ys hlen _ _
    cases ys with
    | nil =>
      have hunf : miriInsertPredicate p [] = [p] := rfl
      rw [hunf]; rfl
    | cons _ _ => simp at hlen
  | succ n ih =>
    intro ys hlen hsorted hinj
    cases ys with
    | nil =>
      have hunf : miriInsertPredicate p [] = [p] := rfl
      rw [hunf]; rfl
    | cons h t =>
      rw [List.pairwise_cons] at hsorted
      rcases hsorted with ⟨hleT, hsortedT⟩
      have hunf : miriInsertPredicate p (h :: t) =
          if p.stableKey ≤ h.stableKey then p :: h :: t else h :: miriInsertPredicate p t := rfl
      rw [hunf]
      have heqErase : (h :: t).eraseDups = h :: (t.filter (fun x => !(x == h))).eraseDups :=
        eraseDups_cons_eq h t
      by_cases hlt : p.stableKey < h.stableKey
      · have hle : p.stableKey ≤ h.stableKey := Nat.le_of_lt hlt
        simp only [hle, ↓reduceIte]
        have hpNotMem : p ∉ h :: t := by
          intro hmem
          simp only [List.mem_cons] at hmem
          rcases hmem with rfl | ht
          · omega
          · have := hleT p ht; omega
        rw [eraseDups_cons_of_not_mem p (h :: t) hpNotMem, heqErase]
        simp only [insertPredUnique, hlt, ↓reduceIte]
      · by_cases heqK : p.stableKey = h.stableKey
        · have hle : p.stableKey ≤ h.stableKey := Nat.le_of_eq heqK
          have hpEqH : p = h := hinj p List.mem_cons_self h
            (List.mem_cons_of_mem _ List.mem_cons_self) heqK
          subst hpEqH
          simp only [hle, ↓reduceIte, eraseDups_cons_dup]
          rw [heqErase]
          simp only [insertPredUnique, hlt, ↓reduceIte, beq_self_eq_true]
        · have hgt : ¬ (p.stableKey ≤ h.stableKey) := by omega
          have hneK : (p.stableKey == h.stableKey) = false := beq_false_of_ne heqK
          simp only [hgt, ↓reduceIte]
          rw [eraseDups_cons_eq h (miriInsertPredicate p t), heqErase]
          simp only [insertPredUnique, hlt, hneK, Bool.false_eq_true, ↓reduceIte]
          congr 1
          rw [miriInsertPredicate_filter_ne_comm p h (by omega) t]
          have hsub : ∀ x ∈ t.filter (fun x => !(x == h)), x ∈ t :=
            fun x hx => (List.mem_filter.mp hx).1
          exact ih (t.filter (fun x => !(x == h)))
            (Nat.le_trans (List.length_filter_le _ _) (Nat.le_of_succ_le_succ hlen))
            (hsortedT.filter _)
            (fun a ha b hb => hinj a (by
              simp only [List.mem_cons] at ha ⊢
              rcases ha with rfl | hf
              · exact Or.inl rfl
              · exact Or.inr (Or.inr (hsub a hf)))
              b (by
              simp only [List.mem_cons] at hb ⊢
              rcases hb with rfl | hf
              · exact Or.inl rfl
              · exact Or.inr (Or.inr (hsub b hf))))

private theorem miriSortPredicates_eraseDups_eq_foldr
    (xs : List Miri.Interpreter.VTablePredicate)
    (hinj : ∀ a ∈ xs, ∀ b ∈ xs, a.stableKey = b.stableKey → a = b) :
    (miriSortPredicates xs).eraseDups = xs.foldr insertPredUnique [] := by
  induction xs with
  | nil => rfl
  | cons h t ih =>
    have hunf : miriSortPredicates (h :: t) = miriInsertPredicate h (miriSortPredicates t) := rfl
    rw [hunf, List.foldr_cons, ← ih (fun a ha b hb =>
      hinj a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb))]
    exact miriInsertPredicate_eraseDups_keyInj h (miriSortPredicates t) (miriSortPredicates_pairwise t)
      (fun a ha b hb => by
        have ha' : a ∈ h :: t := by
          simp only [List.mem_cons, mem_miriSortPredicates_iff] at ha ⊢; exact ha
        have hb' : b ∈ h :: t := by
          simp only [List.mem_cons, mem_miriSortPredicates_iff] at hb ⊢; exact hb
        exact hinj a ha' b hb')

private theorem mem_insertPredUnique_iff (p x : Miri.Interpreter.VTablePredicate)
    (ys : List Miri.Interpreter.VTablePredicate) :
    x ∈ insertPredUnique p ys → x = p ∨ x ∈ ys := by
  induction ys with
  | nil =>
    intro hx; simp [insertPredUnique] at hx; exact Or.inl hx
  | cons h t ih =>
    intro hx
    unfold insertPredUnique at hx
    split at hx
    · simp only [List.mem_cons] at hx
      rcases hx with rfl | rfl | hrest
      · exact Or.inl rfl
      · exact Or.inr List.mem_cons_self
      · exact Or.inr (List.mem_cons_of_mem _ hrest)
    · split at hx
      · exact Or.inr hx
      · simp only [List.mem_cons] at hx
        rcases hx with rfl | hrest
        · exact Or.inr List.mem_cons_self
        · rcases ih hrest with rfl | ht
          · exact Or.inl rfl
          · exact Or.inr (List.mem_cons_of_mem _ ht)

private theorem mem_foldr_insertPredUnique (xs : List Miri.Interpreter.VTablePredicate) :
    ∀ x ∈ xs.foldr insertPredUnique [], x ∈ xs := by
  induction xs with
  | nil => intro x hx; cases hx
  | cons h t ih =>
    intro x hx
    rw [List.foldr_cons] at hx
    rcases mem_insertPredUnique_iff h x _ hx with rfl | ht
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih x ht)

private theorem insertPredUnique_map_keyId (p : Miri.Interpreter.VTablePredicate)
    (ys : List Miri.Interpreter.VTablePredicate)
    (hinj : ∀ y ∈ ys, p.stableKey = y.stableKey → p.id = y.id) :
    (insertPredUnique p ys).map (fun q => (q.stableKey, q.id)) =
      insertKeyIdSorted (p.stableKey, p.id) (ys.map (fun q => (q.stableKey, q.id))) := by
  induction ys with
  | nil => rfl
  | cons h t ih =>
    unfold insertPredUnique insertKeyIdSorted
    by_cases hlt : p.stableKey < h.stableKey
    · simp [hlt]
    · by_cases heq : p.stableKey = h.stableKey
      · have hid : p.id = h.id := hinj h List.mem_cons_self heq
        simp [heq, hid]
      · have hne : (p.stableKey == h.stableKey) = false := beq_false_of_ne heq
        simp only [hlt, hne, Bool.false_eq_true, Bool.false_and, Bool.or_false, ↓reduceIte,
          List.map_cons]
        congr 1
        exact ih (fun y hy => hinj y (List.mem_cons_of_mem _ hy))

/-- **General `VTable.sortedPredicates` correspondence (`lean-miri#75`)**: whenever non-auto
predicates have injective `stableKey` (matching rustc's total `StableOrd`, and automatic for every
principal-less or single-principal `dyn [Principal] + Auto*`), the predicate IDs produced by
vendored `VTable.sortedPredicates` equal the theory's `canonicalNonAutoPredIds` verbatim. -/
theorem miri_sortedPredicates_map_id_eq_canonical (preds : List VTablePredSpec)
    (hinj : PredsKeyInjective preds) :
    (miriSortedPredicates (preds.map predSpecToMiri).toArray).map (·.id) =
      canonicalNonAutoPredIds preds := by
  have hunf : miriSortedPredicates (preds.map predSpecToMiri).toArray =
      (miriSortPredicates ((preds.map predSpecToMiri).filter (fun q => !q.autoTrait))).eraseDups := rfl
  rw [hunf, predSpecToMiri_filter_nonAuto]
  let nonAuto := preds.filter (fun q => !q.autoTrait)
  have hnonAutoInj : ∀ a ∈ nonAuto.map predSpecToMiri, ∀ b ∈ nonAuto.map predSpecToMiri,
      a.stableKey = b.stableKey → a = b := by
    intro a ha b hb hkey
    rcases List.mem_map.mp ha with ⟨pa, hpa, rfl⟩
    rcases List.mem_map.mp hb with ⟨pb, hpb, rfl⟩
    rcases List.mem_filter.mp hpa with ⟨hpaMem, hpaAuto⟩
    rcases List.mem_filter.mp hpb with ⟨hpbMem, hpbAuto⟩
    have hpaF : pa.autoTrait = false := by
      cases h : pa.autoTrait
      · rfl
      · rw [h] at hpaAuto; cases hpaAuto
    have hpbF : pb.autoTrait = false := by
      cases h : pb.autoTrait
      · rfl
      · rw [h] at hpbAuto; cases hpbAuto
    have hkey' : pa.stableKey = pb.stableKey := hkey
    have hid : pa.id = pb.id := hinj pa hpaMem pb hpbMem hpaF hpbF hkey'
    show Miri.Interpreter.VTablePredicate.mk pa.id pa.stableKey pa.autoTrait =
      Miri.Interpreter.VTablePredicate.mk pb.id pb.stableKey pb.autoTrait
    simp only [hid, hkey', hpaF, hpbF]
  rw [miriSortPredicates_eraseDups_eq_foldr _ hnonAutoInj]
  have hmapKeyId : ∀ (xs : List Miri.Interpreter.VTablePredicate),
      (∀ a ∈ xs, ∀ b ∈ xs, a.stableKey = b.stableKey → a.id = b.id) →
      (xs.foldr insertPredUnique []).map (fun q => (q.stableKey, q.id)) =
        sortDedupKeyIds (xs.map (fun q => (q.stableKey, q.id))) := by
    intro xs
    induction xs with
    | nil => intro _; rfl
    | cons h t ih =>
      intro hxs
      rw [List.foldr_cons, List.map_cons, sortDedupKeyIds,
        insertPredUnique_map_keyId h _ (fun y hy heq =>
          hxs h List.mem_cons_self y (List.mem_cons_of_mem _ (mem_foldr_insertPredUnique t y hy)) heq),
        ih (fun a ha b hb => hxs a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb))]
  have hpair := hmapKeyId (nonAuto.map predSpecToMiri) (fun a ha b hb hk =>
    congrArg Miri.Interpreter.VTablePredicate.id (hnonAutoInj a ha b hb hk))
  have hmapEq : (nonAuto.map predSpecToMiri).map (fun q => (q.stableKey, q.id)) =
      nonAuto.map (fun p => (p.stableKey, p.id)) := by
    rw [List.map_map]; rfl
  unfold canonicalNonAutoPredIds
  change ((nonAuto.map predSpecToMiri).foldr insertPredUnique []).map (·.id) =
    (sortDedupKeyIds (nonAuto.map fun p => (p.stableKey, p.id))).map Prod.snd
  rw [← hmapEq, ← hpair, List.map_map]
  rfl

private theorem est_bind_ok {ε σ α β : Type} (x : EStateM ε σ α) (f : α → EStateM ε σ β)
    (s s' : σ) (a : α) (hx : x s = .ok a s') :
    (x >>= f) s = f a s' := by
  show EStateM.bind x f s = f a s'
  simp [EStateM.bind, hx]

private theorem est_bind_err {ε σ α β : Type} (x : EStateM ε σ α) (f : α → EStateM ε σ β)
    (s s' : σ) (e : ε) (hx : x s = .error e s') :
    (x >>= f) s = .error e s' := by
  show EStateM.bind x f s = .error e s'
  simp [EStateM.bind, hx]

private theorem ite_f {c : Prop} [Decidable c] {α : Type} {t e : α} (h : ¬ c) :
    (if c then t else e) = e := by
  cases ‹Decidable c› with
  | isTrue hc => exact absurd hc h
  | isFalse _ => rfl

private theorem ite_t {c : Prop} [Decidable c] {α : Type} {t e : α} (h : c) :
    (if c then t else e) = t := by
  cases ‹Decidable c› with
  | isTrue _ => rfl
  | isFalse hnc => exact absurd h hnc

private theorem checkForTypeRead_zip_loop_eq
    (xs ys : List Miri.Interpreter.VTablePredicate) (hlen : xs.length = ys.length) :
    let step := fun (p : Miri.Interpreter.VTablePredicate × Miri.Interpreter.VTablePredicate)
        (_ : Unit) =>
      if p.1.id != p.2.id then
        (throw (.undefinedBehavior "InvalidVTableTrait") :
          Miri.Interpreter.RvalueM Unit (ForInStep Unit))
      else pure (.yield ())
    (forIn (m := Miri.Interpreter.RvalueM Unit) (xs.zip ys) () step) () =
      if xs.map (·.id) == ys.map (·.id) then .ok () ()
      else .error (.undefinedBehavior "InvalidVTableTrait") () := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons _ _ => cases hlen
  | cons x xt ih =>
    cases ys with
    | nil => cases hlen
    | cons y yt =>
      have hlen' : xt.length = yt.length := Nat.succ.inj hlen
      simp only [List.zip_cons_cons, List.forIn_cons, List.map_cons]
      by_cases hid : x.id = y.id
      · have hbne : (x.id != y.id) = false := by simp [hid]
        have hbeq : (x.id :: xt.map (·.id) == y.id :: yt.map (·.id)) =
            (xt.map (·.id) == yt.map (·.id)) := by simp [hid]
        simp only [hbne, Bool.false_eq_true, ↓reduceIte, bind, Bind.bind, EStateM.bind,
          pure, Pure.pure, EStateM.pure, hbeq]
        exact ih yt hlen'
      · have hbne : (x.id != y.id) = true := bne_iff_ne.mpr hid
        have hbeq : (x.id :: xt.map (·.id) == y.id :: yt.map (·.id)) = false := by
          apply beq_false_of_ne
          intro hEq; exact hid (List.cons.inj hEq).1
        simp only [hbne, ↓reduceIte, hbeq, Bool.false_eq_true,
          bind, Bind.bind, EStateM.bind, throw, throwThe, MonadExceptOf.throw, EStateM.throw]

/-- **General `VTable.checkForTypeRead` correspondence (`lean-miri#75`)**: for arbitrary
existentials (both principal-less AND principal-bearing!) whose effective non-auto predicates
satisfy `PredsKeyInjective`, vendored `VTable.checkForTypeRead` returns `.ok () ()` when
`vtableMatchesExpectedSpec` is `true` and `.error (.undefinedBehavior "InvalidVTableTrait") ()`
when `vtableMatchesExpectedSpec` is `false`. -/
theorem miri_checkForTypeRead_eq_vtableMatchesExpectedSpec (P : Type)
    (table : Nat → DynExistentialSpec) (actual expected : Nat)
    (ha : PredsKeyInjective (table actual).effectivePreds)
    (he : PredsKeyInjective (table expected).effectivePreds) :
    Miri.Interpreter.VTable.checkForTypeRead (specReadHooks P table) () actual expected () =
      if vtableMatchesExpectedSpec (table actual) (table expected) then .ok () ()
      else .error (.undefinedBehavior "InvalidVTableTrait") () := by
  let aList := miriSortedPredicates (specPredicates (table actual))
  let eList := miriSortedPredicates (specPredicates (table expected))
  have haId : aList.map (·.id) = canonicalNonAutoPredIds (table actual).effectivePreds :=
    miri_sortedPredicates_map_id_eq_canonical (table actual).effectivePreds ha
  have heId : eList.map (·.id) = canonicalNonAutoPredIds (table expected).effectivePreds :=
    miri_sortedPredicates_map_id_eq_canonical (table expected).effectivePreds he
  have hmatchEq : vtableMatchesExpectedSpec (table actual) (table expected) =
      (aList.map (·.id) == eList.map (·.id)) := by
    unfold vtableMatchesExpectedSpec; rw [haId, heId]
  rw [hmatchEq]
  unfold Miri.Interpreter.VTable.checkForTypeRead
  refine (est_bind_ok _ _ _ _ _ rfl).trans ?_
  refine (est_bind_ok _ _ _ _ _ rfl).trans ?_
  by_cases hlen : aList.length = eList.length
  · have hbne : (aList.length != eList.length) = false := by simp [hlen]
    rw [show (aList.length != eList.length) = false from hbne]
    rw [ite_f (by decide)]
    have hloop := checkForTypeRead_zip_loop_eq aList eList hlen
    dsimp only at hloop
    have hforEq :
        (forIn (m := Miri.Interpreter.RvalueM Unit) (aList.zip eList) () fun x _ =>
          match x with
          | (a, b) => do
            let a ← (specReadHooks P table).normalizePredicate () a
            let b ← (specReadHooks P table).normalizePredicate () b
            if a != b then
              (miri_etm_private% Miri.Interpreter.VTable Miri.Interpreter.VTable.ub) "InvalidVTableTrait"
            pure (.yield ())) () =
        if aList.map (·.id) == eList.map (·.id) then .ok () ()
        else .error (.undefinedBehavior "InvalidVTableTrait") () := by
      have hfn : (fun (x : Miri.Interpreter.VTablePredicate × Miri.Interpreter.VTablePredicate) (_ : Unit) =>
          match x with
          | (a, b) => do
            let a ← (specReadHooks P table).normalizePredicate () a
            let b ← (specReadHooks P table).normalizePredicate () b
            if a != b then
              (miri_etm_private% Miri.Interpreter.VTable Miri.Interpreter.VTable.ub) "InvalidVTableTrait"
            pure (.yield ())) =
          (fun (p : Miri.Interpreter.VTablePredicate × Miri.Interpreter.VTablePredicate) (_ : Unit) =>
            if p.1.id != p.2.id then
              (throw (.undefinedBehavior "InvalidVTableTrait") : Miri.Interpreter.RvalueM Unit (ForInStep Unit))
            else pure (.yield ())) := by
        funext ⟨a, b⟩ u
        funext s
        by_cases hne : a.id = b.id
        · simp [specReadHooks, hne]
        · have hbne : (a.id != b.id) = true := bne_iff_ne.mpr hne
          simp [specReadHooks, hne, hbne]; rfl
      rw [hfn]; exact hloop
    cases heq : (aList.map (·.id) == eList.map (·.id)) with
    | true =>
      rw [heq] at hforEq
      exact (est_bind_ok _ _ _ _ () hforEq).trans rfl
    | false =>
      rw [heq] at hforEq
      exact est_bind_err _ _ _ _ _ hforEq
  · have hbne : (aList.length != eList.length) = true := bne_iff_ne.mpr hlen
    have hbeq : (aList.map (·.id) == eList.map (·.id)) = false := by
      apply beq_false_of_ne
      intro hEq
      have hl := congrArg List.length hEq
      simp at hl
      exact hlen hl
    rw [show (aList.length != eList.length) = true from hbne, hbeq, ite_t (by decide)]
    exact est_bind_err _ _ _ _ _ rfl

/-- Boolean corollary of `miri_checkForTypeRead_eq_vtableMatchesExpectedSpec`. -/
theorem miriVTableTraitCheckOk_eq_vtableMatchesExpectedSpec
    (table : Nat → DynExistentialSpec) (actual expected : Nat)
    (ha : PredsKeyInjective (table actual).effectivePreds)
    (he : PredsKeyInjective (table expected).effectivePreds) :
    miriVTableTraitCheckOk table actual expected =
      vtableMatchesExpectedSpec (table actual) (table expected) := by
  unfold miriVTableTraitCheckOk
  rw [miri_checkForTypeRead_eq_vtableMatchesExpectedSpec Unit table actual expected ha he]
  cases vtableMatchesExpectedSpec (table actual) (table expected) <;> rfl

private theorem predsKeyInjective_of_autoPreds (s : DynExistentialSpec)
    (hauto : ∀ q ∈ s.predicates, q.autoTrait = true) :
    PredsKeyInjective s.effectivePreds := by
  intro a ha b hb haF hbF _
  unfold DynExistentialSpec.effectivePreds at ha hb
  cases hp : s.principal with
  | none =>
    rw [hp] at ha; have := hauto a ha; rw [haF] at this; cases this
  | some p =>
    rw [hp] at ha hb
    simp only [List.mem_cons] at ha hb
    rcases ha with rfl | ha'
    · rcases hb with rfl | hb'
      · rfl
      · have := hauto b hb'; rw [hbF] at this; cases this
    · have := hauto a ha'; rw [haF] at this; cases this

/-- **Unconditional correspondence for all single-principal and principal-less Rust existentials**
(`dyn [Principal] + Auto1 + ... + AutoK`): whenever the extra `predicates` are all auto traits,
`PredsKeyInjective` holds automatically for BOTH `principal = none` and `principal = some p`, so
vendored `VTable.checkForTypeRead` agrees unconditionally with `vtableMatchesExpectedSpec`. -/
theorem miri_checkForTypeRead_principal_auto_eq (P : Type)
    (table : Nat → DynExistentialSpec) (actual expected : Nat)
    (ha : ∀ q ∈ (table actual).predicates, q.autoTrait = true)
    (he : ∀ q ∈ (table expected).predicates, q.autoTrait = true) :
    Miri.Interpreter.VTable.checkForTypeRead (specReadHooks P table) () actual expected () =
      if vtableMatchesExpectedSpec (table actual) (table expected) then .ok () ()
      else .error (.undefinedBehavior "InvalidVTableTrait") () :=
  miri_checkForTypeRead_eq_vtableMatchesExpectedSpec P table actual expected
    (predsKeyInjective_of_autoPreds _ ha) (predsKeyInjective_of_autoPreds _ he)

/-- **Tightness witness (`PredsKeyInjective` separation)**: vendored `VTable.sortPredicates` breaks
`stableKey` ties by input order, whereas the theory's `canonicalNonAutoPredIds` tie-breaks by
`(stableKey, id)` for exact permutation invariance. On two distinct non-auto predicates sharing
`stableKey = 42` in opposite orders, `vtableMatchesExpectedSpec = true` while vendored
`VTable.checkForTypeRead` rejects with `InvalidVTableTrait`. -/
theorem miri_checkForTypeRead_stableKey_collision_separation :
    let table : Nat → DynExistentialSpec
      | 0 => ⟨none, AutoTraitSet.empty, [⟨1, 42, false⟩, ⟨2, 42, false⟩]⟩
      | _ => ⟨none, AutoTraitSet.empty, [⟨2, 42, false⟩, ⟨1, 42, false⟩]⟩
    vtableMatchesExpectedSpec (table 0) (table 1) = true ∧
    Miri.Interpreter.VTable.checkForTypeRead (specReadHooks Unit table) () 0 1 () =
      .error (.undefinedBehavior "InvalidVTableTrait") () := by
  exact ⟨by decide, rfl⟩

/-- World-backed vendored `VTableReadHooks` driven directly by a `KeyedAllocWorld`, a
`VTableRegistry`, a `VTablePtrVal`-matching pointer resolver, and a layout map for concrete types. -/
def worldVTableReadHooks (P : Type) (w : KeyedAllocWorld) (reg : VTableRegistry)
    (resolve : Miri.Memory.Pointer (Option P) → Except Miri.Interpreter.VTablePointerError (Miri.Memory.AllocId × Miri.ABI.Size))
    (dynTable : Nat → DynExistentialSpec) (dynCode : DynExistentialSpec → Nat)
    (layoutOfTy : Miri.MIR.TyId → Miri.Interpreter.RvalueM Unit (Miri.ABI.TyAndLayout Miri.MIR.TyId)) :
    Miri.Interpreter.VTableReadHooks P Unit Unit where
  resolvePointer := fun _ ptr => pure (resolve ptr)
  globalVTable := fun _ id =>
    match w.findGlobal? (ofMiriAllocId id) with
    | some g =>
      if g.kind == .vtable then
        match reg.allocToData.get? (ofMiriAllocId id) with
        | some data => pure (some (data.concreteTyCode, dynCode data.spec))
        | none => pure none
      else pure none
    | none => pure none
  predicates := fun _ n => pure (specPredicates (dynTable n))
  normalizePredicate := fun _ p => pure p.id
  layoutOf := fun _ ty => layoutOfTy ty

/-- **Exact `VTable.getPtrVTableTypeRead` vs `validateVTableHalf` correspondence (`lean-miri#75` &
`lean-miri#82`)**: for any pointer whose resolution matches `vptr : VTablePtrVal`, vendored
`VTable.getPtrVTableTypeRead` accepts with `.ok data.concreteTyCode ()` iff
`validateVTableHalf w reg vptr (dynTable expected) = .ok data`, fails with
`"InvalidVTablePointer"` on null / danglingInt / nonzeroOffset / notGlobalVTable / missingMetadata,
and fails with `"InvalidVTableTrait"` on `.invalidVTableTrait`. -/
theorem miri_getPtrVTableTypeRead_eq_validateVTableHalf (P : Type)
    (w : KeyedAllocWorld) (reg : VTableRegistry)
    (resolve : Miri.Memory.Pointer (Option P) → Except Miri.Interpreter.VTablePointerError (Miri.Memory.AllocId × Miri.ABI.Size))
    (dynTable : Nat → DynExistentialSpec) (dynCode : DynExistentialSpec → Nat)
    (layoutOfTy : Miri.MIR.TyId → Miri.Interpreter.RvalueM Unit (Miri.ABI.TyAndLayout Miri.MIR.TyId))
    (ptr : Miri.Memory.Pointer (Option P)) (vptr : VTablePtrVal) (expected : Nat)
    (hdynRt : ∀ s, dynTable (dynCode s) = s)
    (hres : match vptr with
      | .null => resolve ptr = .error .danglingInteger
      | .danglingInt _ => resolve ptr = .error .danglingInteger
      | .provenanced id off => resolve ptr = .ok (toMiriAllocId id, Miri.ABI.Size.ofBytes off))
    (hinjExp : PredsKeyInjective (dynTable expected).effectivePreds)
    (hinjReg : ∀ id data, reg.allocToData.get? id = some data → PredsKeyInjective data.spec.effectivePreds) :
    Miri.Interpreter.VTable.getPtrVTableTypeRead
        (worldVTableReadHooks P w reg resolve dynTable dynCode layoutOfTy) () ptr (some expected) () =
      match validateVTableHalf w reg vptr (dynTable expected) with
      | .ok data => .ok data.concreteTyCode ()
      | .error (.invalidVTableTrait _ _) => .error (.undefinedBehavior "InvalidVTableTrait") ()
      | .error _ => .error (.undefinedBehavior "InvalidVTablePointer") () := by
  unfold Miri.Interpreter.VTable.getPtrVTableTypeRead validateVTableHalf
  cases vptr with
  | null =>
    refine (est_bind_ok _ _ _ _ _ rfl).trans ?_
    rw [hres]
    exact est_bind_err _ _ _ _ _ rfl
  | danglingInt addr =>
    refine (est_bind_ok _ _ _ _ _ rfl).trans ?_
    rw [hres]
    exact est_bind_err _ _ _ _ _ rfl
  | provenanced id off =>
    refine (est_bind_ok _ _ _ _ _ rfl).trans ?_
    rw [hres]
    refine (est_bind_ok _ _ _ _ _ rfl).trans ?_
    dsimp only
    have hzero : (Miri.ABI.Size.ofBytes off != Miri.ABI.Size.ZERO) = (off != 0) := by
      simp [Miri.ABI.Size.ofBytes, Miri.ABI.Size.ZERO, bne, BEq.beq]
    rw [hzero]
    cases hoff : (off != 0) with
    | true =>
      rw [ite_t (by decide)]
      exact est_bind_err _ _ _ _ _ rfl
    | false =>
      rw [ite_f (by decide)]
      have hgvEq :
          (worldVTableReadHooks P w reg resolve dynTable dynCode layoutOfTy).globalVTable () (toMiriAllocId id) () =
            .ok (match w.findGlobal? id with
              | some g =>
                if g.kind == .vtable then
                  match reg.allocToData.get? id with
                  | some data => some (data.concreteTyCode, dynCode data.spec)
                  | none => none
                else none
              | none => none) () := by
        unfold worldVTableReadHooks
        dsimp only
        rw [ofMiriAllocId_toMiriAllocId]
        cases w.findGlobal? id with
        | none => rfl
        | some g =>
          cases hkind : (g.kind == .vtable) with
          | false => simp only [hkind, Bool.false_eq_true, ↓reduceIte]; rfl
          | true =>
            simp only [hkind, ↓reduceIte]
            cases reg.allocToData.get? id <;> rfl
      refine (est_bind_ok _ _ _ _ _ hgvEq).trans ?_
      cases hg : w.findGlobal? id with
      | none => rfl
      | some g =>
        cases hkind : (g.kind == .vtable) with
        | false =>
          have hne : (g.kind != .vtable) = true := by simp [bne, hkind]
          simp only [hkind, hne, Bool.false_eq_true, ↓reduceIte]; rfl
        | true =>
          have hne : (g.kind != .vtable) = false := by simp [bne, hkind]
          simp only [hkind, hne, Bool.false_eq_true, ↓reduceIte]
          cases hdata : reg.allocToData.get? id with
          | none => rfl
          | some data =>
            dsimp only
            have hchkEq : Miri.Interpreter.VTable.checkForTypeRead
                (worldVTableReadHooks P w reg resolve dynTable dynCode layoutOfTy) ()
                (dynCode data.spec) expected () =
                Miri.Interpreter.VTable.checkForTypeRead (specReadHooks P dynTable) ()
                  (dynCode data.spec) expected () := rfl
            have hchk := miri_checkForTypeRead_eq_vtableMatchesExpectedSpec P dynTable
              (dynCode data.spec) expected (by rw [hdynRt]; exact hinjReg id data hdata) hinjExp
            rw [hdynRt] at hchk
            cases hmatch : vtableMatchesExpectedSpec data.spec (dynTable expected) with
            | true =>
              rw [hmatch] at hchk
              simp only [↓reduceIte] at hchk
              exact (est_bind_ok _ _ _ _ () (hchkEq.trans hchk)).trans rfl
            | false =>
              rw [hmatch] at hchk
              simp only [Bool.false_eq_true, ↓reduceIte] at hchk
              exact est_bind_err _ _ _ _ _ (hchkEq.trans hchk)

/-- **Vendored `VTable.getSizeAndAlignRead` under `VTableData.layoutConsistent` & upcasting**:
whenever `validateVTableHalf w reg vptr (dynTable expected) = .ok data`, `data.layoutConsistent = true`,
and `layoutOfTy data.concreteTyCode` returns the sized layout for `data.concreteTy`, vendored
`VTable.getSizeAndAlignRead` returns `.ok (Size.ofBytes data.sizeBytes, align) ()` with
`align.pow2 = data.alignPow2.toNat` and `align.bytesNat = .ok (2 ^ data.alignPow2.toNat)`. -/
theorem miri_getSizeAndAlignRead_eq_of_layoutConsistent (P : Type)
    (w : KeyedAllocWorld) (reg : VTableRegistry)
    (resolve : Miri.Memory.Pointer (Option P) → Except Miri.Interpreter.VTablePointerError (Miri.Memory.AllocId × Miri.ABI.Size))
    (dynTable : Nat → DynExistentialSpec) (dynCode : DynExistentialSpec → Nat)
    (layoutOfTy : Miri.MIR.TyId → Miri.Interpreter.RvalueM Unit (Miri.ABI.TyAndLayout Miri.MIR.TyId))
    (ptr : Miri.Memory.Pointer (Option P)) (vptr : VTablePtrVal) (expected : Nat)
    (data : VTableData) (tl : Miri.ABI.TyAndLayout Miri.MIR.TyId)
    (hdynRt : ∀ s, dynTable (dynCode s) = s)
    (hres : match vptr with
      | .null => resolve ptr = .error .danglingInteger
      | .danglingInt _ => resolve ptr = .error .danglingInteger
      | .provenanced id off => resolve ptr = .ok (toMiriAllocId id, Miri.ABI.Size.ofBytes off))
    (hinjExp : PredsKeyInjective (dynTable expected).effectivePreds)
    (hinjReg : ∀ id d, reg.allocToData.get? id = some d → PredsKeyInjective d.spec.effectivePreds)
    (hval : validateVTableHalf w reg vptr (dynTable expected) = .ok data)
    (hlc : data.layoutConsistent = true)
    (hlay : layoutOfTy data.concreteTyCode () = .ok tl ())
    (htlSized : tl.layout.isSized = true)
    (htlSize : tl.layout.size = Miri.ABI.Size.ofBytes data.sizeBytes)
    (htlAlign : tl.layout.align.abi.pow2 = data.alignPow2.toNat) :
    ∃ a : Miri.ABI.Align,
      Miri.Interpreter.VTable.getSizeAndAlignRead
        (worldVTableReadHooks P w reg resolve dynTable dynCode layoutOfTy) () ptr (some expected) () =
        .ok (Miri.ABI.Size.ofBytes data.sizeBytes, a) () ∧
      a.pow2 = data.alignPow2.toNat ∧
      a.bytesNat = .ok (2 ^ data.alignPow2.toNat) := by
  have hget := miri_getPtrVTableTypeRead_eq_validateVTableHalf P w reg resolve dynTable dynCode
    layoutOfTy ptr vptr expected hdynRt hres hinjExp hinjReg
  rw [hval] at hget
  refine ⟨tl.layout.align.abi, ?_, htlAlign, ?_⟩
  · unfold Miri.Interpreter.VTable.getSizeAndAlignRead
    refine (est_bind_ok _ _ _ _ _ hget).trans ?_
    refine (est_bind_ok _ _ _ _ _ hlay).trans ?_
    rw [htlSized, Bool.not_true, ite_f (by decide), htlSize]
    rfl
  · have hpow2 : data.alignPow2.toNat ≤ 29 := by
      rcases VTableData.layoutConsistent_spec data hlc with ⟨_, _, _, _, _, hle29, _⟩
      exact hle29
    have hnotge : ¬ (tl.layout.align.abi.pow2 ≥ 64) := by omega
    unfold Miri.ABI.Align.bytesNat Miri.ABI.Align.bytes
    simp only [hnotge, ↓reduceIte, bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure]
    congr 1
    rw [htlAlign]
    have hfin : ∀ k : Fin 30, (UInt64.shiftLeft 1 (UInt64.ofNat k.val)).toNat = 2 ^ k.val := by
      decide
    exact hfin ⟨data.alignPow2.toNat, by omega⟩

/-- **Upcasting to principal-less `dyn AutoTraits` preserves vendored `VTable.getSizeAndAlignRead`**
(`lean-miri#75`): composing `upcastVTableToAutoTraits_preserves_drop_size_align` with
`miri_getSizeAndAlignRead_eq_of_layoutConsistent` proves that upcasting a `VTableWorldWF` vtable
at `srcId` to `dstId` yields a principal-less vtable accepted by `VTable.getSizeAndAlignRead`
with the exact same `dropFnId`, `size`, and `align`. -/
theorem upcastVTableToAutoTraits_preserves_miri_sizeAndAlign (P : Type)
    (reg reg' : VTableRegistry) (w w' : KeyedAllocWorld)
    (srcId dstId : MiriAllocId) (srcData : VTableData) (targetAutoTraits : List AutoTrait)
    (hkwf : VTableRegistry.KeyWF reg)
    (hsrc : reg.allocToData.get? srcId = some srcData)
    (hup : upcastVTableToAutoTraits reg w srcId targetAutoTraits = some (.ok (reg', w', dstId))) :
    ∃ dstData,
      reg'.allocToData.get? dstId = some dstData ∧
      dstData.spec.principal = none ∧
      dstData.dropFnId = srcData.dropFnId ∧
      Miri.ABI.Size.ofBytes dstData.sizeBytes = Miri.ABI.Size.ofBytes srcData.sizeBytes ∧
      dstData.alignPow2 = srcData.alignPow2 ∧
      ∀ (table : Nat → DynExistentialSpec) (expected : Nat),
        table 0 = dstData.spec →
        (∀ q ∈ dstData.spec.predicates, q.autoTrait = true) →
        (table expected).principal = none →
        (∀ q ∈ (table expected).predicates, q.autoTrait = true) →
        Miri.Interpreter.VTable.checkForTypeRead (specReadHooks P table) () 0 expected () = .ok () () := by
  obtain ⟨dstData, hdst, hprinc, hdrop, hsz, hal⟩ :=
    upcastVTableToAutoTraits_preserves_drop_size_align reg reg' w w' srcId dstId srcData
      targetAutoTraits hkwf hsrc hup
  refine ⟨dstData, hdst, hprinc, hdrop, congrArg Miri.ABI.Size.ofBytes hsz, hal, ?_⟩
  intro table expected ht0 hdAuto hePrinc heAuto
  apply miri_checkForTypeRead_autoOnly_ok P table 0 expected
  · intro q hq
    rw [ht0] at hq
    unfold specPredicates DynExistentialSpec.effectivePreds at hq
    rw [hprinc] at hq
    simp only [List.mem_map] at hq
    rcases hq with ⟨p, hp, rfl⟩
    exact hdAuto p hp
  · intro q hq
    unfold specPredicates DynExistentialSpec.effectivePreds at hq
    rw [hePrinc] at hq
    simp only [List.mem_map] at hq
    rcases hq with ⟨p, hp, rfl⟩
    exact heAuto p hp

/-- **Real vendored `VTableMachine.reserve` + `VTableMachine.globalVTable` vs `SaltedVTableRegistry`
(`lean-miri#75`)**: connects Miri's live 32-salt `VTableMachine` registry and `MemoryState`
directly to `SaltedVTableRegistry.internSalted`:
1. On a matching `(ty, dynType, salt)` cache hit, BOTH return the cached `AllocId` without mutating
   memory or the registry.
2. On a cache miss (with `sourceAllocIdWorldActive = false` and `memoryStateToKeyed proj st.machine.memory = w`),
   BOTH reserve the exact same fresh `AllocId` (or fail on ID exhaustion/collision), push a `.vtable`
   global record into `MemoryState`, append `⟨ty, dynType, salt, id⟩` into `VTableMachine.Registry`,
   and make `VTableMachine.globalVTable` resolve `id` to `some (ty, dynType)`.
(Note the explicit modeling delta: `VTableMachine.reserve` records global metadata size `0`
`Size.ZERO` because Miri vtables are purely symbolic and `getSizeAndAlignRead` queries `layoutOf`,
whereas `SaltedVTableRegistry.internSalted` records the 3-word header size `24`.) -/
theorem miri_vtableMachine_reserve_eq_internSalted {K User Other : Type}
    (proj : RowProjection Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree K)
    (h : Miri.Interpreter.VTableMachine.Hooks K User Other)
    (st : Miri.Interpreter.MachineHooks.State K User)
    (sreg : SaltedVTableRegistry) (w : KeyedAllocWorld)
    (sk : SaltedVTableKey) (data : VTableData)
    (ty : Miri.MIR.TyId) (dynType : Nat) (salt : Fin 32)
    (hmemW : memoryStateToKeyed proj st.machine.memory = w)
    (hsrcInactive : st.machine.memory.sourceAllocIdWorldActive = false)
    (hfresh : ∀ e ∈ (h.registry st.machine.user).entries.toList,
      e.allocation.value ≠ st.machine.memory.nextAllocId)
    (hcache : ∀ id,
      ((h.registry st.machine.user).entries.find?
          (fun e => e.typeId == ty && e.dynamicType == dynType && e.salt == salt)).map (·.allocation) =
        some id ↔
      sreg.keyToAlloc.get? (encodeSaltedVTableKeyCode sk) = some (ofMiriAllocId id))
    (hputGet : ∀ u r, h.registry (h.putRegistry u r) = r) :
    (∀ cachedId, sreg.keyToAlloc.get? (encodeSaltedVTableKeyCode sk) = some cachedId →
      Miri.Interpreter.VTableMachine.reserve h ty dynType salt st = .ok (toMiriAllocId cachedId) st ∧
      sreg.internSalted w sk data = .ok (sreg, w, cachedId)) ∧
    (sreg.keyToAlloc.get? (encodeSaltedVTableKeyCode sk) = none →
      match sreg.internSalted w sk data with
      | .error _ =>
        ∃ msg st', Miri.Interpreter.VTableMachine.reserve h ty dynType salt st =
          .error (.resourceExhaustion msg) st'
      | .ok (_, _, newId) =>
        ∃ st',
          Miri.Interpreter.VTableMachine.reserve h ty dynType salt st = .ok (toMiriAllocId newId) st' ∧
          st'.machine.memory.findGlobal? (toMiriAllocId newId) ≠ none ∧
          Miri.Interpreter.VTableMachine.globalVTable h (toMiriAllocId newId) st' =
            .ok (some (ty, dynType)) st') := by
  constructor
  · intro cachedId hget
    have hfind : ∃ e, (h.registry st.machine.user).entries.find?
        (fun e => e.typeId == ty && e.dynamicType == dynType && e.salt == salt) = some e ∧
        e.allocation = toMiriAllocId cachedId := by
      have hm := (hcache (toMiriAllocId cachedId)).mpr (by rw [ofMiriAllocId_toMiriAllocId]; exact hget)
      cases hf : (h.registry st.machine.user).entries.find?
          (fun e => e.typeId == ty && e.dynamicType == dynType && e.salt == salt) with
      | none => simp [hf] at hm
      | some e =>
        simp [hf] at hm
        exact ⟨e, rfl, hm⟩
    rcases hfind with ⟨e, hfe, halloc⟩
    refine ⟨?_, ?_⟩
    · unfold Miri.Interpreter.VTableMachine.reserve
      simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind,
        pure, Pure.pure, EStateM.pure, hfe, halloc]
    · unfold SaltedVTableRegistry.internSalted
      simp only [hget]
  · intro hnone
    have hfindNone : (h.registry st.machine.user).entries.find?
        (fun e => e.typeId == ty && e.dynamicType == dynType && e.salt == salt) = none := by
      cases hf : (h.registry st.machine.user).entries.find?
          (fun e => e.typeId == ty && e.dynamicType == dynType && e.salt == salt) with
      | none => rfl
      | some e =>
        have hsome := (hcache e.allocation).mp (by simp [hf])
        rw [hnone] at hsome; cases hsome
    unfold SaltedVTableRegistry.internSalted
    simp only [hnone]
    have hresBridge := memoryState_reserveAllocId_eq_keyed proj st.machine.memory hsrcInactive
    rw [hmemW] at hresBridge
    cases hwr : w.reserveAllocId with
    | mk w1 ores =>
      cases hmr : st.machine.memory.reserveAllocId with
      | mk mem1 mres =>
        rw [hmr, hwr] at hresBridge
        have hresEq := hresBridge.2
        cases ores with
        | error e =>
          cases mres with
          | ok _ => simp [Except.map, Except.mapError] at hresEq
          | error me =>
            refine ⟨s!"vtable allocation ID: {reprStr me}",
              { st with machine := { st.machine with memory := mem1 } }, ?_⟩
            unfold Miri.Interpreter.VTableMachine.reserve
            simp only [get, getThe, MonadStateOf.get, EStateM.get, set, MonadStateOf.set, EStateM.set,
              bind, Bind.bind, EStateM.bind, pure, Pure.pure,
              throw, throwThe, MonadExceptOf.throw, EStateM.throw,
              hfindNone, hsrcInactive, Bool.false_eq_true, ↓reduceIte, hmr]
        | ok newId =>
          cases mres with
          | error _ => simp [Except.map, Except.mapError] at hresEq
          | ok mId =>
            simp only [Except.map, Except.mapError] at hresEq
            injection hresEq with hidEq
            have hmIdEq : mId = toMiriAllocId newId := by
              rw [← hidEq, toMiriAllocId_ofMiriAllocId]
            subst hmIdEq
            have hvalEq : (toMiriAllocId newId).value = st.machine.memory.nextAllocId := by
              unfold Miri.Memory.MemoryState.reserveAllocId at hmr
              rw [hsrcInactive] at hmr
              cases hex : st.machine.memory.idSupplyExhausted with
              | true => simp [hex, Id.run, pure] at hmr
              | false =>
                rw [hex] at hmr
                simp only [Bool.false_and, Bool.false_or, Bool.false_eq_true, ↓reduceIte, Id.run, pure] at hmr
                cases hmk : Miri.Memory.AllocId.ofUInt64 st.machine.memory.nextAllocId with
                | none => rw [hmk] at hmr; simp at hmr
                | some id0 =>
                  rw [hmk] at hmr
                  simp only at hmr
                  split at hmr
                  · simp at hmr
                  · have h2 := (Prod.mk.inj hmr).2
                    injection h2 with hid0
                    subst hid0
                    unfold Miri.Memory.AllocId.ofUInt64 at hmk
                    split at hmk
                    · cases hmk
                    · injection hmk with hmkEq; rw [← hmkEq]
            let align := h.target.defaultAddressSpacePointerSpec.pointerAlign
            let g : Miri.Memory.GlobalAllocation := ⟨toMiriAllocId newId, .vtable, .ZERO, align, .Not, some .vtable⟩
            let mem2 := Miri.Memory.MemoryState.pushGlobal mem1 g
            let entry : Miri.Interpreter.VTableMachine.Entry := ⟨ty, dynType, salt, toMiriAllocId newId⟩
            let reg2 : Miri.Interpreter.VTableMachine.Registry :=
              { entries := (h.registry st.machine.user).entries.push entry }
            let st' : Miri.Interpreter.MachineHooks.State K User :=
              { st with machine := { st.machine with memory := mem2, user := h.putRegistry st.machine.user reg2 } }
            refine ⟨st', ?_, ?_, ?_⟩
            · unfold Miri.Interpreter.VTableMachine.reserve
              simp only [get, getThe, MonadStateOf.get, EStateM.get, set, MonadStateOf.set, EStateM.set,
                modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
                bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure,
                hfindNone, hsrcInactive, Bool.false_eq_true, ↓reduceIte, hmr]
              rfl
            · intro hfgNone
              have hlist := memoryState_findGlobal?_eq_list_find? mem2 (toMiriAllocId newId)
              rw [hfgNone] at hlist
              have hmem : g ∈ mem2.globals.toList := by
                have hgl : mem2.globals = mem1.globals.push g := rfl
                rw [hgl, Array.toList_push]
                exact List.mem_append_right _ List.mem_cons_self
              have hne := List.find?_eq_none.mp hlist.symm g hmem
              exact hne (beq_self_eq_true _)
            · unfold Miri.Interpreter.VTableMachine.globalVTable
              simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind,
                pure, Pure.pure]
              have hreg' : h.registry st'.machine.user = reg2 := hputGet st.machine.user reg2
              rw [hreg']
              have hfind2 : reg2.entries.find? (fun e => e.allocation == toMiriAllocId newId) = some entry := by
                rw [← Array.find?_toList]
                change ((h.registry st.machine.user).entries.push entry).toList.find?
                  (fun e => e.allocation == toMiriAllocId newId) = some entry
                rw [Array.toList_push, List.find?_append]
                have hnoneOld : (h.registry st.machine.user).entries.toList.find?
                    (fun e => e.allocation == toMiriAllocId newId) = none := by
                  rw [List.find?_eq_none]
                  intro e he hbeq
                  have heq : e.allocation = toMiriAllocId newId := eq_of_beq hbeq
                  exact hfresh e he (by rw [heq, hvalEq])
                rw [hnoneOld]
                simp [entry]
              rw [hfind2]; rfl

/-- **Salted `VTable.getPointer` separation (`lean-miri#75`)**: calling vendored
`VTable.getPointer (VTableMachine.hooks h base)` from an empty `MemoryState` and empty
`VTableMachine.Registry` with two distinct salts `s₁ ≠ s₂ : Fin 32` for the SAME `(ty, dynType)`
allocates two distinct `AllocId`s `id₁ = 1 ≠ id₂ = 2`, returns their root pointers, and
`VTableMachine.globalVTable` resolves BOTH to `some (ty, dynType)` (matching
`saltedVTable_distinct_salts_distinct_allocIds_both_valid`). -/
theorem miri_vtable_getPointer_salted_distinct_allocIds {K User Other C ABI : Type}
    (h : Miri.Interpreter.VTableMachine.Hooks K User Other)
    (base : Miri.Interpreter.VTableHooks Miri.Memory.Provenance (Miri.Interpreter.MachineHooks.State K User) C Miri.Interpreter.CallInstance ABI)
    (choice : C) (ty : Miri.MIR.TyId) (dynType : Nat)
    (s₁ s₂ : Fin 32) (hneSalt : s₁ ≠ s₂)
    (st₀ : Miri.Interpreter.MachineHooks.State K User)
    (hmem0 : st₀.machine.memory = Miri.Memory.MemoryState.empty)
    (hreg0 : h.registry st₀.machine.user = Miri.Interpreter.VTableMachine.Registry.empty)
    (hputGet : ∀ u r, h.registry (h.putRegistry u r) = r)
    (herase : ∀ st, base.eraseAndAnonymize choice ty dynType st = .ok (ty, dynType) st)
    (hmonoT : ∀ st, base.ensureMonomorphicType choice ty st = .ok () st)
    (hmonoD : ∀ st, base.ensureMonomorphicDyn choice dynType st = .ok () st)
    (p₁ p₂ : Miri.Memory.Pointer Miri.Memory.Provenance) :
    let id₁ : Miri.Memory.AllocId := ⟨1, by decide⟩
    let id₂ : Miri.Memory.AllocId := ⟨2, by decide⟩
    id₁ ≠ id₂ ∧
    ∃ st₁ st₂,
      Miri.Interpreter.VTableMachine.reserve h ty dynType s₁ st₀ = .ok id₁ st₁ ∧
      Miri.Interpreter.VTableMachine.reserve h ty dynType s₂ st₁ = .ok id₂ st₂ ∧
      (h.functions.chooseSalt st₀ = .ok s₁ st₀ →
        Miri.Interpreter.FunctionPointers.rootPointer h.functions id₁ st₁ = .ok p₁ st₁ →
        Miri.Interpreter.VTable.getPointer (Miri.Interpreter.VTableMachine.hooks h base) choice ty dynType st₀ =
          .ok p₁.withOptionalProvenance st₁) ∧
      (h.functions.chooseSalt st₁ = .ok s₂ st₁ →
        Miri.Interpreter.FunctionPointers.rootPointer h.functions id₂ st₂ = .ok p₂ st₂ →
        Miri.Interpreter.VTable.getPointer (Miri.Interpreter.VTableMachine.hooks h base) choice ty dynType st₁ =
          .ok p₂.withOptionalProvenance st₂) ∧
      Miri.Interpreter.VTableMachine.globalVTable h id₁ st₂ = .ok (some (ty, dynType)) st₂ ∧
      Miri.Interpreter.VTableMachine.globalVTable h id₂ st₂ = .ok (some (ty, dynType)) st₂ := by
  dsimp only
  refine ⟨by decide, ?_⟩
  let id₁ : Miri.Memory.AllocId := ⟨1, by decide⟩
  let id₂ : Miri.Memory.AllocId := ⟨2, by decide⟩
  let align := h.target.defaultAddressSpacePointerSpec.pointerAlign
  let dummyProj : RowProjection Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree K :=
    ⟨fun _ => .heap, fun _ => [], fun _ => []⟩
  let mem0 : Miri.Memory.MemoryState Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree K :=
    Miri.Memory.MemoryState.empty
  let mem1a := mem0.reserveAllocId.1
  have hmem0Keyed : memoryStateToKeyed dummyProj mem0 = KeyedAllocWorld.empty := by
    apply KeyedAllocWorld.ext
    · rfl
    · rfl
    · intro id; rfl
    · intro id; rfl
    · intro id; rfl
    · intro id; rfl
    · intro id; rfl
  have hres1Bridge := memoryState_reserveAllocId_eq_keyed dummyProj mem0 rfl
  have hres1 : st₀.machine.memory.reserveAllocId = (mem1a, .ok id₁) := by
    rw [hmem0]
    have h2 : mem0.reserveAllocId.2 = .ok id₁ := by
      have hk : ((mem0.reserveAllocId.2).map ofMiriAllocId).mapError allocIdErrOfMiri =
          (memoryStateToKeyed dummyProj mem0).reserveAllocId.2 := hres1Bridge.2
      rw [hmem0Keyed] at hk
      have hkEq : KeyedAllocWorld.empty.reserveAllocId.2 = .ok (ofMiriAllocId id₁) := rfl
      rw [hkEq] at hk
      cases hm : mem0.reserveAllocId.2 with
      | error e => rw [hm] at hk; cases hk
      | ok a =>
        rw [hm] at hk
        simp only [Except.map, Except.mapError] at hk
        injection hk with ha
        exact congrArg Except.ok (ofMiriAllocId_injective ha)
    exact Prod.ext rfl h2
  have hmem1aSrc : mem1a.sourceAllocIdWorldActive = false := by
    change mem0.reserveAllocId.1.sourceAllocIdWorldActive = false
    unfold Miri.Memory.MemoryState.reserveAllocId
    have hs : mem0.sourceAllocIdWorldActive = false := rfl
    have he : mem0.idSupplyExhausted = false := rfl
    have hn : mem0.nextAllocId = 1 := rfl
    rw [hs, he, hn]
    simp only [Id.run, pure, Pure.pure, Bool.false_and, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
    cases Miri.Memory.AllocId.ofUInt64 1 with
    | none => rfl
    | some a =>
      dsimp only
      split <;> rfl
  let g1 : Miri.Memory.GlobalAllocation := ⟨id₁, .vtable, .ZERO, align, .Not, some .vtable⟩
  let mem1 := Miri.Memory.MemoryState.pushGlobal mem1a g1
  have hmem1Src : mem1.sourceAllocIdWorldActive = false := hmem1aSrc
  have hmem1Keyed : memoryStateToKeyed dummyProj mem1 =
      (KeyedAllocWorld.empty.reserveAllocId.1).registerGlobal (ofMiriAllocId id₁)
        ⟨.vtable, 0, UInt8.ofNat align.pow2, .not, []⟩ := by
    have h1a : memoryStateToKeyed dummyProj mem1a = KeyedAllocWorld.empty.reserveAllocId.1 := by
      have h := hres1Bridge.1
      rw [hmem0Keyed] at h
      exact h
    have hgl : mem1.globals = mem1a.globals.push g1 := rfl
    have hmem1aGl : mem1a.globals = #[] := by
      change mem0.reserveAllocId.1.globals = #[]
      unfold Miri.Memory.MemoryState.reserveAllocId
      have hs : mem0.sourceAllocIdWorldActive = false := rfl
      have he : mem0.idSupplyExhausted = false := rfl
      have hn : mem0.nextAllocId = 1 := rfl
      rw [hs, he, hn]
      simp only [Id.run, pure, Pure.pure, Bool.false_and, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
      cases Miri.Memory.AllocId.ofUInt64 1 with
      | none => rfl
      | some a =>
        dsimp only
        split <;> rfl
    apply KeyedAllocWorld.ext
    · change mem1a.nextAllocId = _; rw [← h1a]; rfl
    · change mem1a.idSupplyExhausted = _; rw [← h1a]; rfl
    · intro id
      change (memoryStateToKeyed dummyProj mem1a).hasIssued id = _
      rw [h1a]
      unfold KeyedAllocWorld.registerGlobal KeyedAllocWorld.hasIssued
      dsimp only
      rw [ExtTreeMap0.contains_eq_isSome_get?, ExtTreeMap0.contains_eq_isSome_get?]
      have his : (KeyedAllocWorld.empty.reserveAllocId.1).issued.get? (ofMiriAllocId id₁) = some () := by decide
      by_cases heq : id = ofMiriAllocId id₁
      · subst heq; rw [his, ExtTreeMap0.get?_insert_self]
      · rw [ExtTreeMap0.get?_insert_ne _ _ heq]
    · intro id
      have hfg : (memoryStateToKeyed dummyProj mem1).findGlobal? id =
          ((memoryStateToRows mem1).globals.toList.find? (fun g => g.allocId == toMiriAllocId id)).map
            (globalEntryOfMiri dummyProj) := by
        have h0 := toKeyed_findGlobal? dummyProj (memoryStateToRows mem1) (toMiriAllocId id)
        rw [ofMiriAllocId_toMiriAllocId] at h0
        exact h0
      rw [hfg]
      have hlist : (memoryStateToRows mem1).globals.toList = [g1] := by
        change mem1.globals.toList = [g1]
        rw [hgl, hmem1aGl]; rfl
      rw [hlist]
      unfold KeyedAllocWorld.registerGlobal KeyedAllocWorld.findGlobal?
      dsimp only
      by_cases heq : id = ofMiriAllocId id₁
      · subst heq
        rw [ExtTreeMap0.get?_insert_self, toMiriAllocId_ofMiriAllocId]
        simp [g1, globalEntryOfMiri, globalKindOfMiri, mutabilityOfMiri, Miri.ABI.Size.ZERO, dummyProj]
      · have hneM : id₁ ≠ toMiriAllocId id := by
          intro h; apply heq; rw [← ofMiriAllocId_toMiriAllocId id, ← h]
        have hneB : (id₁ == toMiriAllocId id) = false := beq_false_of_ne hneM
        rw [ExtTreeMap0.get?_insert_ne _ _ heq]
        have hgl1a : (KeyedAllocWorld.empty.reserveAllocId.1).globals.get? id = none := by
          change (KeyedAllocWorld.empty.reserveAllocId.1).findGlobal? id = none
          rw [← h1a]
          have h0 := toKeyed_findGlobal? dummyProj (memoryStateToRows mem1a) (toMiriAllocId id)
          rw [ofMiriAllocId_toMiriAllocId] at h0
          change (memoryStateToKeyed dummyProj mem1a).findGlobal? id = _ at h0
          rw [h0]
          change Option.map (globalEntryOfMiri dummyProj)
            (mem1a.globals.toList.find? (fun g => g.allocId == toMiriAllocId id)) = none
          rw [hmem1aGl]; rfl
        simp [g1, hneB, hgl1a]
    · intro id
      change (memoryStateToKeyed dummyProj mem1a).findLive? id = _
      rw [h1a]; rfl
    · intro id
      change (memoryStateToKeyed dummyProj mem1a).findDead? id = _
      rw [h1a]; rfl
    · intro id
      change (memoryStateToKeyed dummyProj mem1a).findRace? id = _
      rw [h1a]; rfl
  let reg1 : Miri.Interpreter.VTableMachine.Registry := ⟨#[⟨ty, dynType, s₁, id₁⟩]⟩
  let st₁ : Miri.Interpreter.MachineHooks.State K User :=
    { st₀ with machine := { st₀.machine with memory := mem1, user := h.putRegistry st₀.machine.user reg1 } }
  let mem2a := mem1.reserveAllocId.1
  have hres2 : st₁.machine.memory.reserveAllocId = (mem2a, .ok id₂) := by
    change mem1.reserveAllocId = (mem1.reserveAllocId.1, .ok id₂)
    have h2 : mem1.reserveAllocId.2 = .ok id₂ := by
      have hk : ((mem1.reserveAllocId.2).map ofMiriAllocId).mapError allocIdErrOfMiri =
          (memoryStateToKeyed dummyProj mem1).reserveAllocId.2 :=
        (memoryState_reserveAllocId_eq_keyed dummyProj mem1 hmem1Src).2
      rw [hmem1Keyed] at hk
      have hkEq : ((KeyedAllocWorld.empty.reserveAllocId.1).registerGlobal (ofMiriAllocId id₁)
          ⟨.vtable, 0, UInt8.ofNat align.pow2, .not, []⟩).reserveAllocId.2 = .ok (ofMiriAllocId id₂) := by
        unfold KeyedAllocWorld.reserveAllocId KeyedAllocWorld.registerGlobal KeyedAllocWorld.empty
        have h2ne1 : ofMiriAllocId id₂ ≠ ofMiriAllocId id₁ := by decide
        have hnot2 : (((ExtTreeMap0.empty (α := MiriAllocId) (β := Unit) (cmp := compare)).insert
            (ofMiriAllocId id₁) ()).insert (ofMiriAllocId id₁) ()).contains (ofMiriAllocId id₂) = false := by
          rw [ExtTreeMap0.contains_eq_isSome_get?, ExtTreeMap0.get?_insert_ne _ _ h2ne1,
            ExtTreeMap0.get?_insert_ne _ _ h2ne1, ExtTreeMap0.get?_empty]; rfl
        have hnotG2 : ((ExtTreeMap0.empty (α := MiriAllocId) (β := GlobalAllocEntry) (cmp := compare)).insert
            (ofMiriAllocId id₁) ⟨.vtable, 0, UInt8.ofNat align.pow2, .not, []⟩).contains (ofMiriAllocId id₂) = false := by
          rw [ExtTreeMap0.contains_eq_isSome_get?, ExtTreeMap0.get?_insert_ne _ _ h2ne1,
            ExtTreeMap0.get?_empty]; rfl
        change (if ((((ExtTreeMap0.empty (α := MiriAllocId) (β := Unit) (cmp := compare)).insert
            (ofMiriAllocId id₁) ()).insert (ofMiriAllocId id₁) ()).contains (ofMiriAllocId id₂) ||
            (ExtTreeMap0.empty (α := MiriAllocId) (β := LiveAllocEntry) (cmp := compare)).contains (ofMiriAllocId id₂) ||
            (ExtTreeMap0.empty (α := MiriAllocId) (β := DeadAllocEntry) (cmp := compare)).contains (ofMiriAllocId id₂) ||
            ((ExtTreeMap0.empty (α := MiriAllocId) (β := GlobalAllocEntry) (cmp := compare)).insert
              (ofMiriAllocId id₁) ⟨.vtable, 0, UInt8.ofNat align.pow2, .not, []⟩).contains (ofMiriAllocId id₂)) = true
          then Except.error (AllocIdErr.alreadyIssued (ofMiriAllocId id₂)) else Except.ok (ofMiriAllocId id₂)) = _
        rw [hnot2, hnotG2]; rfl
      rw [hkEq] at hk
      cases hm : mem1.reserveAllocId.2 with
      | error e => rw [hm] at hk; cases hk
      | ok a =>
        rw [hm] at hk
        simp only [Except.map, Except.mapError] at hk
        injection hk with ha
        exact congrArg Except.ok (ofMiriAllocId_injective ha)
    exact Prod.ext rfl h2
  let mem2 := Miri.Memory.MemoryState.pushGlobal mem2a ⟨id₂, .vtable, .ZERO, align, .Not, some .vtable⟩
  let reg2 : Miri.Interpreter.VTableMachine.Registry :=
    ⟨#[⟨ty, dynType, s₁, id₁⟩, ⟨ty, dynType, s₂, id₂⟩]⟩
  let st₂ : Miri.Interpreter.MachineHooks.State K User :=
    { st₁ with machine := { st₁.machine with memory := mem2, user := h.putRegistry st₁.machine.user reg2 } }
  have hneS : (s₁ == s₂) = false := beq_false_of_ne hneSalt
  have hfind1 : (reg1.entries.find? (fun e => e.typeId == ty && e.dynamicType == dynType && e.salt == s₂)) = none := by
    simp [reg1, hneS]
  have hfindG1 : reg2.entries.find? (fun e => e.allocation == id₁) = some ⟨ty, dynType, s₁, id₁⟩ := by
    simp [reg2]
  have hfindG2 : reg2.entries.find? (fun e => e.allocation == id₂) = some ⟨ty, dynType, s₂, id₂⟩ := by
    have hneId : (id₁ == id₂) = false := by decide
    simp [reg2, hneId]
  have hr1 : Miri.Interpreter.VTableMachine.reserve h ty dynType s₁ st₀ = .ok id₁ st₁ := by
    unfold Miri.Interpreter.VTableMachine.reserve
    refine (est_bind_ok _ _ _ _ _ rfl).trans ?_
    rw [hreg0]
    have hfind0 : (Miri.Interpreter.VTableMachine.Registry.empty.entries.find?
        (fun e => e.typeId == ty && e.dynamicType == dynType && e.salt == s₁)) = none := rfl
    rw [hfind0]
    have hsrc0 : st₀.machine.memory.sourceAllocIdWorldActive = false := by rw [hmem0]; rfl
    rw [hsrc0, ite_f (by decide), hres1]
    rfl
  have hr2 : Miri.Interpreter.VTableMachine.reserve h ty dynType s₂ st₁ = .ok id₂ st₂ := by
    unfold Miri.Interpreter.VTableMachine.reserve
    refine (est_bind_ok _ _ _ _ _ rfl).trans ?_
    have hreg1 : h.registry st₁.machine.user = reg1 := hputGet st₀.machine.user reg1
    rw [hreg1, hfind1]
    have hsrc1 : st₁.machine.memory.sourceAllocIdWorldActive = false := hmem1Src
    rw [hsrc1, ite_f (by decide), hres2]
    rfl
  refine ⟨st₁, st₂, hr1, hr2, ?_, ?_, ?_, ?_⟩
  · intro hcs hroot
    unfold Miri.Interpreter.VTable.getPointer Miri.Interpreter.VTableMachine.hooks
      Miri.Interpreter.FunctionPointers.vtableHooks
    refine (est_bind_ok _ _ _ _ _ (herase st₀)).trans ?_
    refine (est_bind_ok _ _ _ _ _ (hmonoT st₀)).trans ?_
    refine (est_bind_ok _ _ _ _ _ (hmonoD st₀)).trans ?_
    refine (est_bind_ok _ _ _ _ s₁.val (by exact (est_bind_ok _ _ _ _ _ hcs).trans rfl)).trans ?_
    refine (est_bind_ok _ _ _ _ id₁ (by simp only [s₁.isLt, ↓reduceDIte, Fin.eta]; exact hr1)).trans ?_
    exact (est_bind_ok _ _ _ _ _ hroot).trans rfl
  · intro hcs hroot
    unfold Miri.Interpreter.VTable.getPointer Miri.Interpreter.VTableMachine.hooks
      Miri.Interpreter.FunctionPointers.vtableHooks
    refine (est_bind_ok _ _ _ _ _ (herase st₁)).trans ?_
    refine (est_bind_ok _ _ _ _ _ (hmonoT st₁)).trans ?_
    refine (est_bind_ok _ _ _ _ _ (hmonoD st₁)).trans ?_
    refine (est_bind_ok _ _ _ _ s₂.val (by exact (est_bind_ok _ _ _ _ _ hcs).trans rfl)).trans ?_
    refine (est_bind_ok _ _ _ _ id₂ (by simp only [s₂.isLt, ↓reduceDIte, Fin.eta]; exact hr2)).trans ?_
    exact (est_bind_ok _ _ _ _ _ hroot).trans rfl
  · unfold Miri.Interpreter.VTableMachine.globalVTable
    refine (est_bind_ok _ _ _ _ _ rfl).trans ?_
    have hreg2 : h.registry st₂.machine.user = reg2 := hputGet st₁.machine.user reg2
    rw [hreg2, hfindG1]; rfl
  · unfold Miri.Interpreter.VTableMachine.globalVTable
    refine (est_bind_ok _ _ _ _ _ rfl).trans ?_
    have hreg2 : h.registry st₂.machine.user = reg2 := hputGet st₁.machine.user reg2
    rw [hreg2, hfindG2]; rfl

/-! ### Part 2B. `Sized` Raw-Pointer Fast-Path & `validateSafeThinRef` (`lean-miri#79`) -/

private theorem checkMetadata_foreign_ok {P S C E F A Pad : Type}
    [Miri.Memory.PointerProvenance P]
    (h : Miri.Interpreter.ValidityVisitor.Hooks P S C E F A Pad) (c : C)
    (target : Miri.Interpreter.MPlaceTy P) (st : S)
    (hmt : h.metadataTail c target.layout.ty st = .ok .foreign st) :
    (miri_etm_private% Miri.Interpreter.ValidityVisitor Miri.Interpreter.ValidityVisitor.checkMetadata)
      h c target st = .ok () st := by
  with_unfolding_all
    exact (est_bind_ok _ _ _ _ _ hmt).trans rfl

private theorem checkMetadata_sliceOrStr_ok {P S C E F A Pad : Type}
    [Miri.Memory.PointerProvenance P]
    (h : Miri.Interpreter.ValidityVisitor.Hooks P S C E F A Pad) (c : C)
    (target : Miri.Interpreter.MPlaceTy P) (st : S)
    (metaScalar : Miri.Memory.Scalar P) (len : UInt64)
    (hmt : h.metadataTail c target.layout.ty st = .ok .sliceOrStr st)
    (hunwrap : target.mplace.metadata.unwrapMeta = .ok metaScalar)
    (hto : metaScalar.toTargetUsize h.target.pointerSize = .ok len) :
    (miri_etm_private% Miri.Interpreter.ValidityVisitor Miri.Interpreter.ValidityVisitor.checkMetadata)
      h c target st = .ok () st := by
  with_unfolding_all
    refine (est_bind_ok _ _ _ _ _ hmt).trans ?_
    refine (est_bind_ok _ _ _ _ metaScalar (by rw [hunwrap]; rfl)).trans ?_
    exact (est_bind_ok _ _ _ _ len (by rw [hto]; rfl)).trans rfl

private theorem checkMetadata_dynamic_eq {P S C E F A Pad : Type}
    [Miri.Memory.PointerProvenance P]
    (h : Miri.Interpreter.ValidityVisitor.Hooks P S C E F A Pad) (c : C)
    (target : Miri.Interpreter.MPlaceTy P) (st : S)
    (expected : Nat) (metaScalar : Miri.Memory.Scalar P) (vtPtr : Miri.Memory.Pointer (Option P))
    (hmt : h.metadataTail c target.layout.ty st = .ok (.dynamic expected) st)
    (hunwrap : target.mplace.metadata.unwrapMeta = .ok metaScalar)
    (htoptr : metaScalar.toPointer h.target.base = .ok vtPtr) :
    (miri_etm_private% Miri.Interpreter.ValidityVisitor Miri.Interpreter.ValidityVisitor.checkMetadata)
      h c target st =
      match Miri.Interpreter.VTable.getPtrVTableType h.vtable c vtPtr (some expected) st with
      | .ok _ st' => .ok () st'
      | .error err st' => .error err st' := by
  with_unfolding_all
    refine (est_bind_ok _ _ _ _ _ hmt).trans ?_
    refine (est_bind_ok _ _ _ _ metaScalar (by rw [hunwrap]; rfl)).trans ?_
    refine (est_bind_ok _ _ _ _ vtPtr (by rw [htoptr]; rfl)).trans ?_
    cases hvt : Miri.Interpreter.VTable.getPtrVTableType h.vtable c vtPtr (some expected) st with
    | ok ty st' => exact (est_bind_ok _ _ _ _ ty hvt).trans rfl
    | error err st' => exact est_bind_err _ _ _ _ err hvt

/-- **`lean-miri#79` `[T; N]` `Sized` fast-path on vendored `ValidityVisitor.visit`**:
when `h.classify` reports `.rawPointer pointeeTyId (isSyntacticallySized pointee)` and
`isSyntacticallySized pointee = true`, `ValidityVisitor.visit` reads the raw-pointer immediate
and returns `.ok session st` WITHOUT calling `ptrToPlace`, `metadataTail`, `sizeAndAlign`, or
`vtable` (matching `validateRawPtrFastPath` / `validateRawPtrFull` skipping layout on
`*const [u8; usize::MAX]`). -/
theorem visit_rawPointer_sized_fastPath {P S C E F A Pad : Type}
    [Miri.Memory.PointerProvenance P] [DecidableEq P]
    (h : Miri.Interpreter.ValidityVisitor.Hooks P S C E F A Pad) (c : C)
    (fuel : Nat) (session : Miri.Interpreter.ValidityVisitor.Session P)
    (place : Miri.Interpreter.RuntimePlace P) (st : S)
    (pointee : ProtoTy) (pointeeTyId : Miri.MIR.TyId)
    (ptrImm : Miri.Interpreter.RvalueImmTy P)
    (hsized : isSyntacticallySized pointee = true)
    (hreset : session.flags.resetProvenanceAndPadding = false)
    (hcl : h.classify c place.layout.ty st =
      .ok (.rawPointer pointeeTyId (isSyntacticallySized pointee)) st)
    (hrd : h.readImmediate c place .rawPointer st = .ok ptrImm st) :
    Miri.Interpreter.ValidityVisitor.visit h c (fuel + 1) session place st = .ok session st := by
  unfold Miri.Interpreter.ValidityVisitor.visit
  refine (est_bind_ok _ _ _ _ _ hcl).trans ?_
  have hprim : (miri_etm_private% Miri.Interpreter.ValidityVisitor Miri.Interpreter.ValidityVisitor.primitive)
      h c session place (.rawPointer pointeeTyId (isSyntacticallySized pointee)) st = .ok (some session) st := by
    with_unfolding_all
      refine (est_bind_ok _ _ _ _ _ hrd).trans ?_
      rw [hreset, ite_f (by decide)]
      dsimp only
      rw [hsized, Bool.not_true, ite_f (by decide)]
      rfl
  exact (est_bind_ok _ _ _ _ (some session) hprim).trans rfl

/-- **Unsized raw-pointer metadata check for `.foreign` and `.sliceOrStr`** (`lean-miri#79`):
complements `visit_rawPointer_unsized_dyn_vtable_only` to cover all three `MetadataTail` variants:
- `.foreign`: accepts without inspecting metadata (`unsizedMetadataTail` returns `.foreign`).
- `.sliceOrStr`: validates the slice/str length via `Scalar.toTargetUsize` (`unsizedMetadataTail`
  returns `.sliceLen`). -/
theorem visit_rawPointer_unsized_foreign_and_slice {P S C E F A Pad : Type}
    [Miri.Memory.PointerProvenance P] [DecidableEq P]
    (h : Miri.Interpreter.ValidityVisitor.Hooks P S C E F A Pad) (c : C)
    (fuel : Nat) (session : Miri.Interpreter.ValidityVisitor.Session P)
    (place : Miri.Interpreter.RuntimePlace P) (st : S)
    (pointee : ProtoTy) (pointeeTyId : Miri.MIR.TyId)
    (ptrImm : Miri.Interpreter.RvalueImmTy P) (target : Miri.Interpreter.MPlaceTy P)
    (hunsized : isSyntacticallySized pointee = false)
    (hreset : session.flags.resetProvenanceAndPadding = false)
    (hcl : h.classify c place.layout.ty st =
      .ok (.rawPointer pointeeTyId (isSyntacticallySized pointee)) st)
    (hrd : h.readImmediate c place .rawPointer st = .ok ptrImm st)
    (hpt : h.ptrToPlace c ptrImm st = .ok target st)
    (htuns : target.layout.layout.isSized = false) :
    (h.metadataTail c target.layout.ty st = .ok .foreign st →
      Miri.Interpreter.ValidityVisitor.visit h c (fuel + 1) session place st = .ok session st) ∧
    (∀ metaScalar len,
      h.metadataTail c target.layout.ty st = .ok .sliceOrStr st →
      target.mplace.metadata.unwrapMeta = .ok metaScalar →
      metaScalar.toTargetUsize h.target.pointerSize = .ok len →
      Miri.Interpreter.ValidityVisitor.visit h c (fuel + 1) session place st = .ok session st) := by
  have hstep :
      Miri.Interpreter.ValidityVisitor.visit h c (fuel + 1) session place st =
        match (miri_etm_private% Miri.Interpreter.ValidityVisitor Miri.Interpreter.ValidityVisitor.checkMetadata)
            h c target st with
        | .ok () st' => .ok session st'
        | .error err st' => .error err st' := by
    unfold Miri.Interpreter.ValidityVisitor.visit
    refine (est_bind_ok _ _ _ _ _ hcl).trans ?_
    have hprim : (miri_etm_private% Miri.Interpreter.ValidityVisitor Miri.Interpreter.ValidityVisitor.primitive)
        h c session place (.rawPointer pointeeTyId (isSyntacticallySized pointee)) st =
        match (miri_etm_private% Miri.Interpreter.ValidityVisitor Miri.Interpreter.ValidityVisitor.checkMetadata)
            h c target st with
        | .ok () st' => .ok (some session) st'
        | .error err st' => .error err st' := by
      with_unfolding_all
        refine (est_bind_ok _ _ _ _ _ hrd).trans ?_
        rw [hreset, ite_f (by decide)]
        dsimp only
        rw [hunsized, Bool.not_false, ite_t (by decide)]
        refine (est_bind_ok _ _ _ _ _ hpt).trans ?_
        rw [htuns, ite_f (by decide)]
        cases hcm : (miri_etm_private% Miri.Interpreter.ValidityVisitor Miri.Interpreter.ValidityVisitor.checkMetadata)
            h c target st with
        | ok u st' => cases u; exact (est_bind_ok _ _ _ _ () hcm).trans rfl
        | error err st' => exact est_bind_err _ _ _ _ err hcm
    cases hcm : (miri_etm_private% Miri.Interpreter.ValidityVisitor Miri.Interpreter.ValidityVisitor.checkMetadata)
        h c target st with
    | ok u st' =>
      cases u; rw [hcm] at hprim
      exact (est_bind_ok _ _ _ _ (some session) hprim).trans rfl
    | error err st' =>
      rw [hcm] at hprim
      exact est_bind_err _ _ _ _ err hprim
  constructor
  · intro hfor
    rw [hstep, checkMetadata_foreign_ok h c target st hfor]
  · intro metaScalar len hsl hunwrap hto
    rw [hstep, checkMetadata_sliceOrStr_ok h c target st metaScalar len hsl hunwrap hto]

/-- **Unsized raw-pointer metadata check on vendored `ValidityVisitor.visit`** (`lean-miri#79` &
`lean-miri#82`): when `isSyntacticallySized pointee = false`, `ValidityVisitor.visit` calls
`ptrToPlace`, verifies `!target.layout.layout.isSized`, and runs `checkMetadata`:
- `.foreign`: accepts thin pointer with no metadata check.
- `.sliceOrStr`: validates the length metadata via `toTargetUsize`.
- `.dynamic expected`: validates the vtable pointer via `VTable.getPtrVTableType` (leaving the raw
  data pointer completely unchecked, matching `validateRawWideDynPtrMeta` / `validateRawPtrFull`). -/
theorem visit_rawPointer_unsized_dyn_vtable_only {P S C E F A Pad : Type}
    [Miri.Memory.PointerProvenance P] [DecidableEq P]
    (h : Miri.Interpreter.ValidityVisitor.Hooks P S C E F A Pad) (c : C)
    (fuel : Nat) (session : Miri.Interpreter.ValidityVisitor.Session P)
    (place : Miri.Interpreter.RuntimePlace P) (st : S)
    (pointee : ProtoTy) (pointeeTyId : Miri.MIR.TyId) (expected : Nat)
    (ptrImm : Miri.Interpreter.RvalueImmTy P) (target : Miri.Interpreter.MPlaceTy P)
    (metaScalar : Miri.Memory.Scalar P) (vtPtr : Miri.Memory.Pointer (Option P))
    (hunsized : isSyntacticallySized pointee = false)
    (hreset : session.flags.resetProvenanceAndPadding = false)
    (hcl : h.classify c place.layout.ty st =
      .ok (.rawPointer pointeeTyId (isSyntacticallySized pointee)) st)
    (hrd : h.readImmediate c place .rawPointer st = .ok ptrImm st)
    (hpt : h.ptrToPlace c ptrImm st = .ok target st)
    (htuns : target.layout.layout.isSized = false)
    (hmt : h.metadataTail c target.layout.ty st = .ok (.dynamic expected) st)
    (hunwrap : target.mplace.metadata.unwrapMeta = .ok metaScalar)
    (htoptr : metaScalar.toPointer h.target.base = .ok vtPtr) :
    (∀ ty, Miri.Interpreter.VTable.getPtrVTableType h.vtable c vtPtr (some expected) st = .ok ty st →
      Miri.Interpreter.ValidityVisitor.visit h c (fuel + 1) session place st = .ok session st) ∧
    (∀ err st', Miri.Interpreter.VTable.getPtrVTableType h.vtable c vtPtr (some expected) st = .error err st' →
      Miri.Interpreter.ValidityVisitor.visit h c (fuel + 1) session place st = .error err st') := by
  have hcm := checkMetadata_dynamic_eq h c target st expected metaScalar vtPtr hmt hunwrap htoptr
  have hstep :
      Miri.Interpreter.ValidityVisitor.visit h c (fuel + 1) session place st =
        match Miri.Interpreter.VTable.getPtrVTableType h.vtable c vtPtr (some expected) st with
        | .ok _ st' => .ok session st'
        | .error err st' => .error err st' := by
    unfold Miri.Interpreter.ValidityVisitor.visit
    refine (est_bind_ok _ _ _ _ _ hcl).trans ?_
    have hprim : (miri_etm_private% Miri.Interpreter.ValidityVisitor Miri.Interpreter.ValidityVisitor.primitive)
        h c session place (.rawPointer pointeeTyId (isSyntacticallySized pointee)) st =
        match Miri.Interpreter.VTable.getPtrVTableType h.vtable c vtPtr (some expected) st with
        | .ok _ st' => .ok (some session) st'
        | .error err st' => .error err st' := by
      with_unfolding_all
        refine (est_bind_ok _ _ _ _ _ hrd).trans ?_
        rw [hreset, ite_f (by decide)]
        dsimp only
        rw [hunsized, Bool.not_false, ite_t (by decide)]
        refine (est_bind_ok _ _ _ _ _ hpt).trans ?_
        rw [htuns, ite_f (by decide)]
        cases hvt : Miri.Interpreter.VTable.getPtrVTableType h.vtable c vtPtr (some expected) st with
        | ok ty st' =>
          rw [hvt] at hcm
          exact (est_bind_ok _ _ _ _ () hcm).trans rfl
        | error err st' =>
          rw [hvt] at hcm
          exact est_bind_err _ _ _ _ err hcm
    cases hvt : Miri.Interpreter.VTable.getPtrVTableType h.vtable c vtPtr (some expected) st with
    | ok ty st' =>
      rw [hvt] at hprim
      exact (est_bind_ok _ _ _ _ (some session) hprim).trans rfl
    | error err st' =>
      rw [hvt] at hprim
      exact est_bind_err _ _ _ _ err hprim
  refine ⟨fun ty hok => by rw [hstep, hok], fun err st' herr => by rw [hstep, herr]⟩

private theorem scalarInt_tryFromUInt64_eq (u : UInt64) :
    Miri.Memory.ScalarInt.tryFromUInt (BitVec.ofNat 128 u.toNat) (Miri.ABI.Size.ofBytes 8) =
      .ok (some (Miri.Memory.ScalarInt.ofUInt64 u)) := by
  have hlt : u.toNat < 2 ^ 64 := u.toBitVec.isLt
  have hlt128 : u.toNat < 2 ^ 128 := Nat.lt_trans hlt (by decide : 2 ^ 64 < 2 ^ 128)
  have htr : (Miri.ABI.Size.ofBytes 8).truncate (BitVec.ofNat 128 u.toNat) =
      .ok (BitVec.ofNat 128 u.toNat) := by
    with_unfolding_all
      have hiw : (miri_etm_private% Miri.ABI.Size Miri.ABI.Size.integerWidth)
          (Miri.ABI.Size.ofBytes 8) = .ok 64 := rfl
      show (do
        let width ← (miri_etm_private% Miri.ABI.Size Miri.ABI.Size.integerWidth) (Miri.ABI.Size.ofBytes 8)
        if width == 0 then pure 0
        else pure (BitVec.zeroExtend 128 (BitVec.extractLsb (width - 1) 0 (BitVec.ofNat 128 u.toNat)))) = _
      rw [hiw]
      show Except.ok (BitVec.zeroExtend 128 (BitVec.extractLsb 63 0 (BitVec.ofNat 128 u.toNat))) = _
      congr 1
      have hze := zeroExtend_extractLsb_eq_ofNat 64 (by decide) (by decide) (BitVec.ofNat 128 u.toNat)
      rw [hze]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt128, Nat.mod_eq_of_lt hlt]
  have htrd : (miri_etm_private% Miri.Memory.ScalarInt Miri.Memory.ScalarInt.truncated)
      (BitVec.ofNat 128 u.toNat) (Miri.ABI.Size.ofBytes 8) =
      .ok (Miri.Memory.ScalarInt.ofUInt64 u, false) := by
    have hbind : ∀ {ε α β : Type} (ma : Except ε α) (f : α → Except ε β) (a : α),
        ma = .ok a → (ma >>= f) = f a := fun _ _ _ h => by rw [h]; rfl
    with_unfolding_all
      have hcw : (miri_etm_private% Miri.Memory.ScalarInt Miri.Memory.ScalarInt.checkedWidth)
          (Miri.ABI.Size.ofBytes 8) = .ok 64 := rfl
      refine (hbind _ _ 64 hcw).trans ?_
      refine (hbind _ _ (BitVec.ofNat 128 u.toNat) (by rw [htr]; rfl)).trans ?_
      simp [Miri.Memory.ScalarInt.ofUInt64, pure, Pure.pure, Except.pure]
  unfold Miri.Memory.ScalarInt.tryFromUInt
  simp only [bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure, htrd,
    Bool.false_eq_true, ↓reduceIte]

private theorem scalarInt_ofUInt64_isNull (u : UInt64) :
    (Miri.Memory.ScalarInt.ofUInt64 u).isNull = (u == 0) := by
  have hlt : u.toNat < 2 ^ 64 := u.toBitVec.isLt
  unfold Miri.Memory.ScalarInt.isNull Miri.Memory.ScalarInt.ofUInt64
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  constructor
  · intro h
    have h0 : (BitVec.ofNat 128 u.toNat).toNat = 0 := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans hlt (by decide : 2 ^ 64 < 2 ^ 128))] at h0
    exact UInt64.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq h0)
  · intro h; subst h; rfl

private theorem scalar_fromMaybePointer_tryToScalarInt
    (ptr : Miri.Memory.Pointer (Option Miri.Memory.Provenance)) :
    ∃ sc,
      Miri.Memory.Scalar.fromMaybePointer annealTargetDataLayout ptr = .ok sc ∧
      sc.tryToScalarInt = .ok (.integer (Miri.Memory.ScalarInt.ofUInt64 ptr.offset.bytes)) := by
  cases hprov : ptr.provenance with
  | none =>
    refine ⟨Miri.Memory.Scalar.fromScalarInt (Miri.Memory.ScalarInt.ofUInt64 ptr.offset.bytes), ?_, rfl⟩
    unfold Miri.Memory.Scalar.fromMaybePointer
    rw [hprov]
    with_unfolding_all
      have hps : (miri_etm_private% Miri.Memory.Scalar Miri.Memory.Scalar.targetPointerSize)
          annealTargetDataLayout = Miri.ABI.Size.ofBytes 8 := rfl
      simp only [hps, scalarInt_tryFromUInt64_eq ptr.offset.bytes, Except.mapError,
        bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure]
  | some p =>
    refine ⟨Miri.Memory.Scalar.fromPointer annealTargetDataLayout ⟨ptr.offset, p⟩, ?_, ?_⟩
    · unfold Miri.Memory.Scalar.fromMaybePointer
      rw [hprov]; rfl
    · unfold Miri.Memory.Scalar.tryToScalarInt Miri.Memory.Scalar.fromPointer
      have hoff : Miri.Memory.PointerProvenance.offsetIsAddr (Prov := Miri.Memory.Provenance) = true := rfl
      simp only [hoff, ↓reduceIte]
      with_unfolding_all
        have hps : (miri_etm_private% Miri.Memory.Scalar Miri.Memory.Scalar.targetPointerSize)
            annealTargetDataLayout = Miri.ABI.Size.ofBytes 8 := rfl
        simp only [hps, scalarInt_tryFromUInt64_eq ptr.offset.bytes, Except.mapError,
          bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure]

/-- **Provenance-agnostic `ValidityMachine.scalarMayBeNull`**: on 64-bit Miri pointers (where
`PointerProvenance.offsetIsAddr = true`), `Scalar.fromMaybePointer` always produces a 64-bit
scalar whose `ValidityMachine.scalarMayBeNull` equals `ptr.offset.bytes == 0` for BOTH
provenance-free integers (`none`) and provenanced pointers (`some prov`). -/
theorem validityMachine_scalarMayBeNull_eq {K User : Type}
    (ptr : Miri.Memory.Pointer (Option Miri.Memory.Provenance))
    (st : Miri.Interpreter.ValidityMachine.State K User) :
    ∃ sc,
      Miri.Memory.Scalar.fromMaybePointer annealTargetDataLayout ptr = .ok sc ∧
      Miri.Interpreter.ValidityMachine.scalarMayBeNull sc st = .ok (ptr.offset.bytes == 0) st := by
  obtain ⟨sc, hfrom, htry⟩ := scalar_fromMaybePointer_tryToScalarInt ptr
  refine ⟨sc, hfrom, ?_⟩
  unfold Miri.Interpreter.ValidityMachine.scalarMayBeNull
  rw [htry]
  exact congrArg (fun b => EStateM.Result.ok b st) (scalarInt_ofUInt64_isNull ptr.offset.bytes)

/-- **`ValidityMachine.checkPointerAccessResult` against real `MemoryState` and `KeyedAllocWorld`**
(unconditional on `size` — handles BOTH `size < 2^63` and the `size ≥ 2^63` `isize::MAX` gate!):
when `state.machine.memory` satisfies `MemoryStateCoreDomain`, `MemoryStateGlobalsDistinct`, and
`MemoryStateAlignFit`, the machine-level pointer access check returns `.ok res st` with
`res.isOk = (memoryStateToKeyed proj state.machine.memory).checkPtrAccess prov size.bytes.toNat`. -/
theorem validityMachine_checkPointerAccessResult_eq_keyed {K User : Type}
    (proj : RowProjection Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree K)
    (access : Miri.Interpreter.ValidityMachine.Access K User)
    (ptr : Miri.Memory.Pointer (Option Miri.Memory.Provenance))
    (size : Miri.ABI.Size)
    (st : Miri.Interpreter.ValidityMachine.State K User)
    (prov : Option (MiriAllocId × UInt64))
    (hcore : MemoryStateCoreDomain st.machine.memory)
    (hglobNd : MemoryStateGlobalsDistinct st.machine.memory)
    (halign : MemoryStateAlignFit st.machine.memory)
    (hres : ∀ sgn : Int,
      ∃ r, access.resolvePointer st.machine.memory ptr sgn st.machine = .ok r st.machine ∧
        (match r, prov with
         | .error _, none => True
         | .ok rp, some (id, off) => ofMiriAllocId rp.allocId = id ∧ rp.offset.bytes = off
         | _, _ => False)) :
    ∃ res,
      Miri.Interpreter.ValidityMachine.checkPointerAccessResult access ptr size st = .ok res st ∧
      res.isOk = (memoryStateToKeyed proj st.machine.memory).checkPtrAccess prov size.bytes.toNat := by
  by_cases hbig : 9223372036854775808 ≤ size.bytes.toNat
  · have hsgn : Miri.Memory.sizeAsI64 size = .error (.sizeDoesNotFitI64 size) := by
      unfold Miri.Memory.sizeAsI64; simp [hbig]
    refine ⟨.error (.sizeDoesNotFitI64 size), ?_, ?_⟩
    · unfold Miri.Interpreter.ValidityMachine.checkPointerAccessResult
      rw [hsgn]; rfl
    · unfold KeyedAllocWorld.checkPtrAccess
      simp [hbig]; rfl
  · have hsgn : Miri.Memory.sizeAsI64 size = .ok (Int.ofNat size.bytes.toNat) := by
      unfold Miri.Memory.sizeAsI64; simp [hbig]
    unfold Miri.Interpreter.ValidityMachine.checkPointerAccessResult
    rw [hsgn]
    by_cases hz : size.bytes.toNat = 0
    · have hbz : (Int.ofNat size.bytes.toNat == 0) = true := by simp [hz]
      refine ⟨.ok (), ?_, ?_⟩
      · refine (est_bind_ok _ _ _ _ (Int.ofNat size.bytes.toNat) rfl).trans ?_
        rw [hbz, ite_t (by decide)]; rfl
      · unfold KeyedAllocWorld.checkPtrAccess
        simp [hz]; rfl
    · have hbz : (Int.ofNat size.bytes.toNat == 0) = false := by
        apply beq_false_of_ne
        intro hEq
        exact hz (Int.ofNat.inj hEq)
      obtain ⟨r, hrEq, hrMatch⟩ := hres (Int.ofNat size.bytes.toNat)
      have hresolve :
          (miri_etm_private% Miri.Interpreter.ValidityMachine Miri.Interpreter.ValidityMachine.resolve)
            access ptr (Int.ofNat size.bytes.toNat) st = .ok r st := by
        with_unfolding_all
          refine (est_bind_ok _ _ _ _ _ rfl).trans ?_
          rw [hrEq]; rfl
      refine ⟨Miri.Memory.checkPtrAccess ⟨access.runtime.pointerSize⟩ ptr size
          (.dereferenceable "pointer") (fun _ _ => r) st.machine.memory.getAllocInfo, ?_, ?_⟩
      · refine (est_bind_ok _ _ _ _ (Int.ofNat size.bytes.toNat) rfl).trans ?_
        rw [hbz, ite_f (by decide)]
        refine (est_bind_ok _ _ _ _ r hresolve).trans ?_
        refine (est_bind_ok get _ st st st rfl).trans ?_
        cases Miri.Memory.checkPtrAccess ⟨access.runtime.pointerSize⟩ ptr size
            (.dereferenceable "pointer") (fun _ _ => r) st.machine.memory.getAllocInfo <;> rfl
      · exact memoryState_checkPtrAccess_isOk_eq_keyed proj st.machine.memory hcore hglobNd halign
          ⟨access.runtime.pointerSize⟩ ptr size (.dereferenceable "pointer") (fun _ _ => r) prov
          (by
            cases hp : prov with
            | none =>
              intro _
              cases hr : r with
              | error addr => exact ⟨addr, rfl⟩
              | ok _ => simp [hr, hp] at hrMatch
            | some pair =>
              rcases pair with ⟨id, off⟩
              intro _
              cases hr : r with
              | error _ => simp [hr, hp] at hrMatch
              | ok rp =>
                simp only [hr, hp] at hrMatch
                refine ⟨rp.extra, ?_⟩
                cases rp with
                | mk aid roff rextra =>
                  cases roff with
                  | mk rb =>
                    dsimp only at hrMatch
                    have haEq : aid = toMiriAllocId id := by
                      rw [← hrMatch.1, toMiriAllocId_ofMiriAllocId]
                    subst haEq
                    have hbEq : rb = off := hrMatch.2
                    subst hbEq
                    rfl) []

private theorem checkAndDerefPtr_isOk_of_lookup_eq {Prov ProvExtra : Type}
    (target : Miri.Memory.PointerArithmetic) (ptr : Miri.Memory.Pointer (Option Prov))
    (signedSize : Int) (msg : Miri.Memory.CheckInAllocMsg)
    (resolve : Miri.Memory.PointerResolver Prov ProvExtra)
    (l1 l2 : Miri.Memory.LiveAllocationLookup)
    (heq : ∀ id,
      (match l1 id with
       | .ok info => if info.kind == Miri.Memory.AllocationKind.dead then none else some info.size
       | .error _ => none) =
      (match l2 id with
       | .ok info => if info.kind == Miri.Memory.AllocationKind.dead then none else some info.size
       | .error _ => none)) :
    (Miri.Memory.checkAndDerefPtr target ptr signedSize msg resolve l1).isOk =
      (Miri.Memory.checkAndDerefPtr target ptr signedSize msg resolve l2).isOk := by
  unfold Miri.Memory.checkAndDerefPtr
  cases (miri_etm_private% Miri.Memory.Access Miri.Memory.fitsI64) signedSize with
  | false => rfl
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, bind, Bind.bind, Except.bind,
      pure, Pure.pure, Except.pure]
    cases (signedSize == 0) with
    | true => rfl
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      cases resolve ptr signedSize with
      | error _ => rfl
      | ok rp =>
        simp only
        have hlk := heq rp.allocId
        cases ha1 : l1 rp.allocId with
        | error e1 =>
          rw [ha1] at hlk
          cases hk1 : l2 rp.allocId with
          | error e2 => cases e1 <;> cases e2 <;> rfl
          | ok i2 =>
            rw [hk1] at hlk; dsimp only at hlk ⊢
            cases hd2 : (i2.kind == Miri.Memory.AllocationKind.dead) with
            | false => rw [hd2] at hlk; simp at hlk
            | true =>
              cases e1 <;>
                simp only [↓reduceIte, throw, MonadExcept.throw, throwThe, MonadExceptOf.throw, Except.isOk, Except.toBool]
        | ok i1 =>
          rw [ha1] at hlk
          cases hk1 : l2 rp.allocId with
          | error e2 =>
            rw [hk1] at hlk; dsimp only at hlk ⊢
            cases hd1 : (i1.kind == Miri.Memory.AllocationKind.dead) with
            | false => rw [hd1] at hlk; simp at hlk
            | true =>
              cases e2 <;>
                simp only [↓reduceIte, throw, MonadExcept.throw, throwThe, MonadExceptOf.throw, Except.isOk, Except.toBool]
          | ok i2 =>
            rw [hk1] at hlk; dsimp only at hlk ⊢
            cases hd1 : (i1.kind == Miri.Memory.AllocationKind.dead) with
            | true =>
              rw [hd1] at hlk
              cases hd2 : (i2.kind == Miri.Memory.AllocationKind.dead) with
              | false => rw [hd2] at hlk; simp at hlk
              | true =>
                simp only [↓reduceIte, throw, MonadExcept.throw, throwThe, MonadExceptOf.throw, Except.isOk]
            | false =>
              rw [hd1] at hlk
              cases hd2 : (i2.kind == Miri.Memory.AllocationKind.dead) with
              | true => rw [hd2] at hlk; simp at hlk
              | false =>
                rw [hd2] at hlk
                simp only [Bool.false_eq_true, ↓reduceIte] at hlk ⊢
                injection hlk with hszEq
                rw [hszEq]
                cases Miri.Memory.checkedBounds target rp.allocId i2.size rp.offset signedSize msg <;> rfl

/-- **`validateSafeThinRef` against `RefLM3_2.annealValidityHooks` & `ValidityVisitor.validatePlace`
under `KeyedStateRelLM3_2`**: for a `KeyedStateRelLM3_2`-related stack-only machine state
(`m.machine.memory.globals = #[]`, capturing the exact boundary between `annealLookupAlloc`'s
live-only lookup and full `MemoryState.getAllocInfo`) and a sized `ProtoTy` pointee
(`computeTyLayout pointee = .ok lay`, `lay.sizeBytes < 2^63`) whose Anneal
layout/inhabitedness/alignment agree with `lay`, non-recursive `ValidityVisitor.validatePlace`
through `annealValidityHooks` agrees with `validateSafeThinRef kw pointee` on acceptance AND UB
rejection in exact source precedence order (access → null → inhabitedness → alignment). -/
theorem validateSafeThinRef_eq_annealValidityHooks_validatePlace
    {body : Trusted.Rustc.V2026_06_01.MirAst.CapturedMir} {s : MachineState}
    {m : AnnealStepState} {allocMap : List AllocMapEntry} {kw : KeyedAllocWorld}
    (hstate : KeyedStateRelLM3_2 body s m allocMap kw)
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf])
    {refIdx : Nat} (hlt : refIdx < tf.locals.size)
    {p : Trusted.Rustc.V2026_06_01.MirAst.ProvenancePtr}
    {mptr : Miri.Memory.Pointer AnnealProv} (hptr : PtrRel allocMap p mptr)
    {refTy : Trusted.Rustc.V2026_06_01.MirAst.Ty} {mutBool : Bool}
    (hval : (tf.locals[refIdx]'hlt).value =
      .live (.immediate (.scalar (.fromPointer annealTargetDataLayout mptr))))
    (pointee : ProtoTy) (lay : ProtoLayout)
    (hlay : computeTyLayout pointee = .ok lay)
    (hsized : lay.isSized = true)
    (hfit : lay.sizeBytes < 9223372036854775808)
    (ptLay : Miri.Interpreter.LocalLayout)
    (hcl : (annealValidityHooks body.layouts).classify refTy
      (translateTy refTy body.layouts).ty m = .ok (.reference mutBool) m)
    (hpt : (annealValidityHooks body.layouts).ptrToPlace refTy
      ⟨.scalar (.fromPointer annealTargetDataLayout mptr), translateTy refTy body.layouts⟩ m =
      .ok ⟨⟨mptr.withOptionalProvenance, .none, none⟩, ptLay⟩ m)
    (hptSized : ptLay.layout.isSized = true)
    (hptSize : ptLay.layout.size = Miri.ABI.Size.ofBytes (UInt64.ofNat lay.sizeBytes))
    (hptInhab : (annealValidityHooks body.layouts).opsemInhabited refTy ptLay.ty m =
      .ok lay.isInhabited m)
    (hptAlign :
      (lay.alignBytes > 0 ∧
        (mptr.offset.bytes.toNat % lay.alignBytes = 0 →
          (annealValidityHooks body.layouts).checkPointerAlignResult refTy
            mptr.withOptionalProvenance ptLay.layout.align.abi m = .ok (.ok ()) m) ∧
        (mptr.offset.bytes.toNat % lay.alignBytes ≠ 0 →
          ∃ mis, (annealValidityHooks body.layouts).checkPointerAlignResult refTy
            mptr.withOptionalProvenance ptLay.layout.align.abi m = .ok (.error mis) m)))
    (hnoGlob : m.machine.memory.globals = #[])
    (fuel : Nat) :
    ∃ e ∈ allocMap, e.tag = p.tag ∧
      let place : Miri.Interpreter.RuntimePlace AnnealProv :=
        ⟨.local 0 refIdx none tf.localsIdentity, translateTy refTy body.layouts⟩
      let thin : ThinPtrVal := ⟨mptr.offset.bytes, some (ofMiriAllocId e.allocId, UInt64.ofNat p.offsetBytes)⟩
      ((validateSafeThinRef kw pointee thin = .ok ()) ↔
        Miri.Interpreter.ValidityVisitor.validatePlace (annealValidityHooks body.layouts) refTy
          (fuel + 1) place false false m = .ok () m) := by
  rcases hstate with ⟨hs2, rfl⟩
  rcases hs2 with ⟨tf₀, hframes₀, _, _, _, _, _, _, _, _, halloc, _⟩
  have hbase : ∀ e ∈ allocMap, m.machine.lookupBaseAddr e.allocId = some (annealStackBaseAddr e.allocId) :=
    fun e he => (halloc.base_addr_valid e he).2.2
  obtain ⟨e, he, htag, hcheck⟩ := ptrRel_annealResolvePtr_checkPtrAccess_isOk_eq_keyed hptr m.machine hbase
    annealPointerArithmetic (Miri.ABI.Size.ofBytes (UInt64.ofNat lay.sizeBytes))
    (.dereferenceable "pointer") (annealMachineToKeyed m.machine)
  refine ⟨e, he, htag, ?_⟩
  dsimp only
  let place : Miri.Interpreter.RuntimePlace AnnealProv :=
    ⟨.local 0 refIdx none tf.localsIdentity, translateTy refTy body.layouts⟩
  let initSession : Miri.Interpreter.ValidityVisitor.Session AnnealProv :=
    { path := ⟨"", #[]⟩, flags := ⟨false, false⟩, ctfeMode := none, refTracking := none, dataBytes := none }
  have hvp := validatePlace_annealValidityHooks_nonrecursive_eq body.layouts refTy (fuel + 1) place m
  have hrd : (annealValidityHooks body.layouts).readImmediate refTy place .reference m =
      .ok ⟨.scalar (.fromPointer annealTargetDataLayout mptr), translateTy refTy body.layouts⟩ m :=
    annealValidityHooks_readImmediate_local body.layouts refTy hframes hlt hval
      (translateTy refTy body.layouts) .reference
  have hsa : (annealValidityHooks body.layouts).sizeAndAlign refTy
      ⟨⟨mptr.withOptionalProvenance, .none, none⟩, ptLay⟩ m =
      .ok (some (ptLay.layout.size, ptLay.layout.align.abi)) m := by
    simp [annealValidityHooks, hptSized, pure, EStateM.pure]
  have hvref := visit_reference_cases (annealValidityHooks body.layouts) refTy fuel initSession
    place m mutBool hcl rfl rfl rfl
  have hptCases := hvref.2 _ _ hrd hpt hptSized hsa
  have hszNat : (UInt64.ofNat lay.sizeBytes).toNat = lay.sizeBytes := by
    change (BitVec.ofNat 64 lay.sizeBytes).toNat = lay.sizeBytes
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans hfit (by decide : 9223372036854775808 < 2 ^ 64))]
  have hlookupIsOk : ∀ (id : Miri.Memory.AllocId),
      (match annealLookupAlloc m.machine id with
       | .ok info => if info.kind == Miri.Memory.AllocationKind.dead then none else some info.size
       | .error _ => none) =
      (match keyedLookup (annealMachineToKeyed m.machine) id with
       | .ok info => if info.kind == Miri.Memory.AllocationKind.dead then none else some info.size
       | .error _ => none) := by
    intro id
    unfold annealLookupAlloc keyedLookup KeyedAllocWorld.getAllocInfo
    have hfg : (annealMachineToKeyed m.machine).findGlobal? (ofMiriAllocId id) = none := by
      have h0 := toKeyed_findGlobal? annealRowProjection (memoryStateToRows m.machine.memory) id
      change (annealMachineToKeyed m.machine).findGlobal? (ofMiriAllocId id) = _ at h0
      rw [h0]
      have hgl : (memoryStateToRows m.machine.memory).globals = #[] := hnoGlob
      rw [hgl]; rfl
    have hfl : (annealMachineToKeyed m.machine).findLive? (ofMiriAllocId id) =
        ((m.machine.memory.live.toList.find? (fun e => e.1 == id)).map
          (fun e => liveEntryOfMiri annealRowProjection e.2)) :=
      toKeyed_findLive? annealRowProjection (memoryStateToRows m.machine.memory) id
    rw [hfg, hfl, ← Array.find?_toList]
    cases hfd : m.machine.memory.live.toList.find? (fun entry => entry.1 == id) with
    | some pair =>
      simp only [Option.map_some, liveEntryOfMiri]
      rfl
    | none =>
      simp only [Option.map_none]
      cases (annealMachineToKeyed m.machine).findDead? (ofMiriAllocId id) <;> rfl
  have haccEq :
      (annealValidityAccessCheck m.machine mptr.withOptionalProvenance ptLay.layout.size).isOk =
        (annealMachineToKeyed m.machine).checkPtrAccess
          (some (ofMiriAllocId e.allocId, UInt64.ofNat p.offsetBytes)) lay.sizeBytes := by
    rw [hptSize]
    have hchk2 :
        (annealValidityAccessCheck m.machine mptr.withOptionalProvenance
            (Miri.ABI.Size.ofBytes (UInt64.ofNat lay.sizeBytes))).isOk =
        (Miri.Memory.checkPtrAccess annealPointerArithmetic ⟨mptr.offset, some mptr.provenance⟩
            (Miri.ABI.Size.ofBytes (UInt64.ofNat lay.sizeBytes)) (.dereferenceable "pointer")
            (annealResolvePtr m.machine) (keyedLookup (annealMachineToKeyed m.machine))).isOk := by
      unfold annealValidityAccessCheck Miri.Memory.checkPtrAccess
      have hptrEq : mptr.withOptionalProvenance = ⟨mptr.offset, some mptr.provenance⟩ := by
        cases mptr; rfl
      rw [hptrEq]
      cases Miri.Memory.sizeAsI64 (Miri.ABI.Size.ofBytes (UInt64.ofNat lay.sizeBytes)) with
      | error _ => rfl
      | ok signedSize =>
        have hcad := checkAndDerefPtr_isOk_of_lookup_eq annealPointerArithmetic
          ⟨mptr.offset, some mptr.provenance⟩ signedSize (.dereferenceable "pointer")
          (annealResolvePtr m.machine) (annealLookupAlloc m.machine)
          (keyedLookup (annealMachineToKeyed m.machine)) hlookupIsOk
        dsimp only [bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure]
        cases h1 : Miri.Memory.checkAndDerefPtr annealPointerArithmetic ⟨mptr.offset, some mptr.provenance⟩
            signedSize (.dereferenceable "pointer") (annealResolvePtr m.machine) (annealLookupAlloc m.machine) <;>
          cases h2 : Miri.Memory.checkAndDerefPtr annealPointerArithmetic ⟨mptr.offset, some mptr.provenance⟩
            signedSize (.dereferenceable "pointer") (annealResolvePtr m.machine)
            (keyedLookup (annealMachineToKeyed m.machine)) <;>
          simp [h1, h2, Except.isOk, Except.toBool] at hcad ⊢
    rw [hchk2, hcheck]
    change (annealMachineToKeyed m.machine).checkPtrAccess
      (some (ofMiriAllocId e.allocId, UInt64.ofNat p.offsetBytes)) (UInt64.ofNat lay.sizeBytes).toNat = _
    rw [hszNat]
  have hscNull :
      Miri.Memory.Scalar.fromMaybePointer (annealValidityHooks body.layouts).target.base
        mptr.withOptionalProvenance =
        .ok (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr) ∧
      (annealValidityHooks body.layouts).scalarMayBeNull refTy
        (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr) m =
        .ok (mptr.offset.bytes == 0) m := by
    obtain ⟨sc, hscFrom, hscTry⟩ := scalar_fromMaybePointer_tryToScalarInt mptr.withOptionalProvenance
    have h1 : Miri.Memory.Scalar.fromMaybePointer annealTargetDataLayout mptr.withOptionalProvenance =
        .ok (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr) := by
      cases mptr; rfl
    rw [h1] at hscFrom; injection hscFrom with hscEq; subst hscEq
    refine ⟨by cases mptr; rfl, ?_⟩
    unfold annealValidityHooks
    simp only [hscTry, scalarInt_ofUInt64_isNull, pure, Pure.pure, EStateM.pure]
    rfl
  cases hacc : annealValidityAccessCheck m.machine mptr.withOptionalProvenance ptLay.layout.size with
  | error accErr =>
    have haccHook : (annealValidityHooks body.layouts).checkPointerAccess refTy
        mptr.withOptionalProvenance ptLay.layout.size m = .ok (.error accErr) m := by
      show EStateM.Result.ok (annealValidityAccessCheck m.machine mptr.withOptionalProvenance ptLay.layout.size) m = _
      rw [hacc]
    have hvErr := hptCases.1 accErr haccHook
    rw [hvp.2 _ _ hvErr]
    rw [hacc] at haccEq
    have haccFalse : (annealMachineToKeyed m.machine).checkPtrAccess
        (some (ofMiriAllocId e.allocId, UInt64.ofNat p.offsetBytes)) lay.sizeBytes = false := haccEq.symm
    have hLHS : validateSafeThinRef (annealMachineToKeyed m.machine) pointee
        ⟨mptr.offset.bytes, some (ofMiriAllocId e.allocId, UInt64.ofNat p.offsetBytes)⟩ ≠ .ok () := by
      unfold validateSafeThinRef
      rw [hlay]
      simp [hsized, haccFalse]
    exact ⟨fun h => absurd h hLHS, fun h => nomatch h⟩
  | ok u =>
    cases u
    rw [hacc] at haccEq
    have haccTrue : (annealMachineToKeyed m.machine).checkPtrAccess
        (some (ofMiriAllocId e.allocId, UInt64.ofNat p.offsetBytes)) lay.sizeBytes = true := haccEq.symm
    have haccHook : (annealValidityHooks body.layouts).checkPointerAccess refTy
        mptr.withOptionalProvenance ptLay.layout.size m = .ok (.ok ()) m := by
      show EStateM.Result.ok (annealValidityAccessCheck m.machine mptr.withOptionalProvenance ptLay.layout.size) m = _
      rw [hacc]
    have hscCases := hptCases.2 _ haccHook hscNull.1
    cases hnull : (mptr.offset.bytes == 0) with
    | true =>
      rw [hnull] at hscNull
      have hvErr := hscCases.1 hscNull.2
      rw [hvp.2 _ _ hvErr]
      have hLHS : validateSafeThinRef (annealMachineToKeyed m.machine) pointee
          ⟨mptr.offset.bytes, some (ofMiriAllocId e.allocId, UInt64.ofNat p.offsetBytes)⟩ ≠ .ok () := by
        unfold validateSafeThinRef; rw [hlay]; simp [hsized, haccTrue, hnull]
      exact ⟨fun h => absurd h hLHS, fun h => nomatch h⟩
    | false =>
      rw [hnull] at hscNull
      have hinhCases := hscCases.2 hscNull.2
      cases hinh : lay.isInhabited with
      | false =>
        rw [hinh] at hptInhab
        have hvErr := hinhCases.1 hptInhab
        rw [hvp.2 _ _ hvErr]
        have hLHS : validateSafeThinRef (annealMachineToKeyed m.machine) pointee
            ⟨mptr.offset.bytes, some (ofMiriAllocId e.allocId, UInt64.ofNat p.offsetBytes)⟩ ≠ .ok () := by
          unfold validateSafeThinRef; rw [hlay]; simp [hsized, haccTrue, hnull, hinh]
        exact ⟨fun h => absurd h hLHS, fun h => nomatch h⟩
      | true =>
        rw [hinh] at hptInhab
        have halCases := hinhCases.2 hptInhab
        by_cases halMod : mptr.offset.bytes.toNat % lay.alignBytes = 0
        · have hvOk := halCases.2 (hptAlign.2.1 halMod)
          rw [hvp.1 _ _ hvOk rfl]
          have hLHS : validateSafeThinRef (annealMachineToKeyed m.machine) pointee
              ⟨mptr.offset.bytes, some (ofMiriAllocId e.allocId, UInt64.ofNat p.offsetBytes)⟩ = .ok () := by
            unfold validateSafeThinRef; rw [hlay]; simp [hsized, haccTrue, hnull, hinh, halMod]
          exact ⟨fun _ => rfl, fun _ => hLHS⟩
        · obtain ⟨mis, hmis⟩ := hptAlign.2.2 halMod
          have hvErr := halCases.1 mis hmis
          rw [hvp.2 _ _ hvErr]
          have hbne : (mptr.offset.bytes.toNat % lay.alignBytes != 0) = true := bne_iff_ne.mpr halMod
          have hLHS : validateSafeThinRef (annealMachineToKeyed m.machine) pointee
              ⟨mptr.offset.bytes, some (ofMiriAllocId e.allocId, UInt64.ofNat p.offsetBytes)⟩ ≠ .ok () := by
            unfold validateSafeThinRef; rw [hlay]; simp [hsized, haccTrue, hnull, hinh, hbne]
          exact ⟨fun h => absurd h hLHS, fun h => nomatch h⟩

/-! ### Part 2C. Wide-`dyn` Precedence & Recursive `childSession` Visitor (`lean-miri#82`) -/

/-- **Wide-`dyn` vtable-before-data-UB precedence on vendored `ValidityVisitor.visit`**
(`lean-miri#82`): for ANY safe reference whose pointee is unsized with `.dynamic expected`
metadata (including double-null `&dyn Send` with `data = 0, vtable = 0`), `checkSafe` line 202
validates `checkMetadata` → `VTable.getPtrVTableType` **BEFORE** `sizeAndAlign`,
`checkPointerAccess`, `mayDangle` `addressTooClose`, `scalarMayBeNull`, `opsemInhabited`, and
`checkPointerAlignResult`. Thus every vtable failure short-circuits all data-pointer UB, matching
`wideDyn_invalidVTable_precedes_all_data_ub` and `wideDyn_doubleNull_separation`. -/
theorem visit_wideDyn_checkSafe_vtableBeforeDataUB {P S C E F A Pad : Type}
    [Miri.Memory.PointerProvenance P] [DecidableEq P]
    (h : Miri.Interpreter.ValidityVisitor.Hooks P S C E F A Pad) (c : C)
    (fuel : Nat) (session : Miri.Interpreter.ValidityVisitor.Session P)
    (place : Miri.Interpreter.RuntimePlace P) (st : S)
    (mutBool : Bool) (expected : Nat)
    (ptrImm : Miri.Interpreter.RvalueImmTy P) (target : Miri.Interpreter.MPlaceTy P)
    (metaScalar : Miri.Memory.Scalar P) (vtPtr : Miri.Memory.Pointer (Option P))
    (err : Miri.Interpreter.StepError) (st' : S)
    (hreset : session.flags.resetProvenanceAndPadding = false)
    (hcl : h.classify c place.layout.ty st = .ok (.reference mutBool) st)
    (hrd : h.readImmediate c place .reference st = .ok ptrImm st)
    (hpt : h.ptrToPlace c ptrImm st = .ok target st)
    (htuns : target.layout.layout.isSized = false)
    (hmt : h.metadataTail c target.layout.ty st = .ok (.dynamic expected) st)
    (hunwrap : target.mplace.metadata.unwrapMeta = .ok metaScalar)
    (htoptr : metaScalar.toPointer h.target.base = .ok vtPtr)
    (hvtErr : Miri.Interpreter.VTable.getPtrVTableType h.vtable c vtPtr (some expected) st = .error err st') :
    Miri.Interpreter.ValidityVisitor.visit h c (fuel + 1) session place st = .error err st' := by
  have hcm := checkMetadata_dynamic_eq h c target st expected metaScalar vtPtr hmt hunwrap htoptr
  rw [hvtErr] at hcm
  unfold Miri.Interpreter.ValidityVisitor.visit
  refine (est_bind_ok _ _ _ _ _ hcl).trans ?_
  refine est_bind_err _ _ _ _ _ ?_
  with_unfolding_all
    refine est_bind_err _ _ _ _ _ ?_
    refine (est_bind_ok _ _ _ _ _ hrd).trans ?_
    rw [hreset, ite_f (by decide)]
    dsimp only
    refine (est_bind_ok _ _ _ _ _ hpt).trans ?_
    rw [htuns, Bool.not_false, ite_t (by decide)]
    exact est_bind_err _ _ _ _ _ hcm

/-- **Vendored `ValidityVisitor.checkSafe` under `mayDangle = true` (`childSession`, `lean-miri#82`)**:
for BOTH sized AND unsized (wide-`dyn` / slice) safe references when `session.flags.mayDangle = true`,
`checkSafe`:
1. Skips `h.checkPointerAccess` completely (dangling pointers never fail liveness!).
2. Checks `addr + size ≥ 2^pointerWidth - 1` (`"safe pointer too close to address-space end"`)
   FIRST on the absolute address (for BOTH integer `none` AND provenanced `some prov` Miri pointers!).
3. Checks `scalarMayBeNull` → `opsemInhabited` → `checkPointerAlignResult` in exact order,
   without re-tracking into `refTracking`.
Directly connects vendored `ValidityVisitor.visit` to `validateWideDynSafePtr (mayDangle := true)`
and `checkNestedSafeRefWord` / `checkNestedWideSafeRefChildSession`. -/
theorem visit_checkSafe_mayDangle_precedence {S C E F A Pad : Type}
    (h : Miri.Interpreter.ValidityVisitor.Hooks Miri.Memory.Provenance S C E F A Pad) (c : C)
    (fuel : Nat) (session : Miri.Interpreter.ValidityVisitor.Session Miri.Memory.Provenance)
    (place : Miri.Interpreter.RuntimePlace Miri.Memory.Provenance) (st : S)
    (mutBool : Bool)
    (ptrImm : Miri.Interpreter.RvalueImmTy Miri.Memory.Provenance)
    (target : Miri.Interpreter.MPlaceTy Miri.Memory.Provenance)
    (size : Miri.ABI.Size) (align : Miri.ABI.Align)
    (sc : Miri.Memory.Scalar Miri.Memory.Provenance)
    (intVal : Miri.Memory.ScalarInt) (addr : UInt64)
    (hreset : session.flags.resetProvenanceAndPadding = false)
    (hmd : session.flags.mayDangle = true)
    (hcl : h.classify c place.layout.ty st = .ok (.reference mutBool) st)
    (hrd : h.readImmediate c place .reference st = .ok ptrImm st)
    (hpt : h.ptrToPlace c ptrImm st = .ok target st)
    (hmetaOk : target.layout.layout.isSized = true ∨
      (miri_etm_private% Miri.Interpreter.ValidityVisitor Miri.Interpreter.ValidityVisitor.checkMetadata)
        h c target st = .ok () st)
    (hsa : h.sizeAndAlign c target st = .ok (some (size, align)) st)
    (hfrom : Miri.Memory.Scalar.fromMaybePointer h.target.base target.mplace.ptr = .ok sc)
    (htry : sc.tryToScalarInt = .ok (.integer intVal))
    (haddr : intVal.toTargetUsize h.target.pointerSize = .ok addr) :
    let maximum : Nat := 2 ^ h.target.base.pointerWidth.bits.toNat - 1
    (addr.toNat + size.bytes.toNat ≥ maximum →
      Miri.Interpreter.ValidityVisitor.visit h c (fuel + 1) session place st =
        .error (.undefinedBehavior
          s!"validation{session.path.render}: safe pointer too close to address-space end") st) ∧
    (addr.toNat + size.bytes.toNat < maximum →
      (h.scalarMayBeNull c sc st = .ok true st →
        Miri.Interpreter.ValidityVisitor.visit h c (fuel + 1) session place st =
          .error (.undefinedBehavior
            s!"validation{session.path.render}: null or maybe-null safe pointer") st) ∧
      (h.scalarMayBeNull c sc st = .ok false st →
        (h.opsemInhabited c target.layout.ty st = .ok false st →
          Miri.Interpreter.ValidityVisitor.visit h c (fuel + 1) session place st =
            .error (.undefinedBehavior
              s!"validation{session.path.render}: safe pointer to uninhabited type") st) ∧
        (h.opsemInhabited c target.layout.ty st = .ok true st →
          (∀ mis, h.checkPointerAlignResult c target.mplace.ptr align st = .ok (.error mis) st →
            Miri.Interpreter.ValidityVisitor.visit h c (fuel + 1) session place st =
              .error (Miri.Interpreter.ValidityVisitor.classifyPointerAlignmentError
                session.path (.reference mutBool) mis) st) ∧
          (h.checkPointerAlignResult c target.mplace.ptr align st = .ok (.ok ()) st →
            Miri.Interpreter.ValidityVisitor.visit h c (fuel + 1) session place st =
              .ok session st)))) := by
  dsimp only
  have hstep :
      (miri_etm_private% Miri.Interpreter.ValidityVisitor Miri.Interpreter.ValidityVisitor.checkSafe)
        h c session place place.layout.ty (.reference mutBool) st =
      if addr.toNat + size.bytes.toNat ≥ 2 ^ h.target.base.pointerWidth.bits.toNat - 1 then
        .error (.undefinedBehavior
          s!"validation{session.path.render}: safe pointer too close to address-space end") st
      else
        match h.scalarMayBeNull c sc st with
        | .error e st1 => .error e st1
        | .ok true st1 =>
          .error (.undefinedBehavior
            s!"validation{session.path.render}: null or maybe-null safe pointer") st1
        | .ok false st1 =>
          match h.opsemInhabited c target.layout.ty st1 with
          | .error e st2 => .error e st2
          | .ok false st2 =>
            .error (.undefinedBehavior
              s!"validation{session.path.render}: safe pointer to uninhabited type") st2
          | .ok true st2 =>
            match h.checkPointerAlignResult c target.mplace.ptr align st2 with
            | .error e st3 => .error e st3
            | .ok (.error mis) st3 =>
              .error (Miri.Interpreter.ValidityVisitor.classifyPointerAlignmentError
                session.path (.reference mutBool) mis) st3
            | .ok (.ok ()) st3 => .ok session st3 := by
    with_unfolding_all
      refine (est_bind_ok _ _ _ _ _ hrd).trans ?_
      rw [hreset, ite_f (by decide)]
      dsimp only
      refine (est_bind_ok _ _ _ _ _ hpt).trans ?_
      have hskipMeta : ∀ (k : Unit → Miri.Interpreter.ValidityVisitor.M S (Miri.Interpreter.ValidityVisitor.Session Miri.Memory.Provenance)),
          (if !target.layout.layout.isSized then
            (miri_etm_private% Miri.Interpreter.ValidityVisitor Miri.Interpreter.ValidityVisitor.checkMetadata) h c target >>= k
          else k ()) st = k () st := by
        intro k
        rcases hmetaOk with hs | hm
        · rw [hs, Bool.not_true, ite_f (by decide)]
        · cases hb : target.layout.layout.isSized with
          | true => rw [Bool.not_true, ite_f (by decide)]
          | false => rw [Bool.not_false, ite_t (by decide)]; exact est_bind_ok _ _ _ _ () hm
      rw [hskipMeta]
      refine (est_bind_ok _ _ _ _ _ hsa).trans ?_
      rw [Option.getD_some, hmd, Bool.not_true, ite_f (by decide)]
      refine (est_bind_ok _ _ _ _ sc (by rw [hfrom]; rfl)).trans ?_
      rw [htry]
      refine (est_bind_ok _ _ _ _ addr (by rw [haddr]; rfl)).trans ?_
      have hfail : ∀ {A : Type} (msg : String) (st0 : S),
          ((miri_etm_private% Miri.Interpreter.ValidityVisitor Miri.Interpreter.ValidityVisitor.failure)
              session msg st0 : EStateM.Result Miri.Interpreter.StepError S A) =
            EStateM.Result.error (Miri.Interpreter.StepError.undefinedBehavior
              (toString "validation" ++ toString session.path.render ++ toString (": " ++ msg))) st0 := by
        intro A msg st0
        change EStateM.Result.error (Miri.Interpreter.StepError.undefinedBehavior
          (toString "validation" ++ toString session.path.render ++ toString ": " ++ toString msg)) st0 = _
        simp only [toString, String.append_assoc]
      by_cases hclose : addr.toNat + size.bytes.toNat ≥ 2 ^ h.target.base.pointerWidth.bits.toNat - 1
      · rw [ite_t hclose, ite_t hclose]
        exact est_bind_err _ _ _ _ _ (hfail "safe pointer too close to address-space end" st)
      · rw [ite_f hclose, ite_f hclose]
        dsimp only
        refine (est_bind_ok _ _ _ _ none rfl).trans ?_
        dsimp only
        rw [hreset, ite_f (by decide)]
        refine (est_bind_ok _ _ _ _ sc (by rw [hfrom]; rfl)).trans ?_
        cases hnull : h.scalarMayBeNull c sc st with
        | error e st1 => exact est_bind_err _ _ _ _ e hnull
        | ok b st1 =>
          refine (est_bind_ok _ _ _ _ b hnull).trans ?_
          cases b with
          | true => exact est_bind_err _ _ _ _ _ (hfail "null or maybe-null safe pointer" st1)
          | false =>
            dsimp only
            cases hinh : h.opsemInhabited c target.layout.ty st1 with
            | error e st2 => exact est_bind_err _ _ _ _ e hinh
            | ok inh st2 =>
              refine (est_bind_ok _ _ _ _ inh hinh).trans ?_
              cases inh with
              | false => exact est_bind_err _ _ _ _ _ (hfail "safe pointer to uninhabited type" st2)
              | true =>
                dsimp only
                cases hal : h.checkPointerAlignResult c target.mplace.ptr align st2 with
                | error e st3 => exact est_bind_err _ _ _ _ e (by simp [Miri.Interpreter.ValidityVisitor.mapPointerAlignmentOutcome, hal])
                | ok r st3 =>
                  cases r with
                  | error mis =>
                    exact est_bind_err _ _ _ _ _ (by simp [Miri.Interpreter.ValidityVisitor.mapPointerAlignmentOutcome, hal])
                  | ok u =>
                    cases u
                    refine (est_bind_ok _ _ st2 st3 () (by simp [Miri.Interpreter.ValidityVisitor.mapPointerAlignmentOutcome, hal])).trans ?_
                    cases session.refTracking <;> rfl
  have hvisEq : ∀ res,
      (miri_etm_private% Miri.Interpreter.ValidityVisitor Miri.Interpreter.ValidityVisitor.checkSafe)
        h c session place place.layout.ty (.reference mutBool) st = res →
      Miri.Interpreter.ValidityVisitor.visit h c (fuel + 1) session place st = res := by
    intro res hcs
    unfold Miri.Interpreter.ValidityVisitor.visit
    refine (est_bind_ok _ _ _ _ _ hcl).trans ?_
    cases res with
    | ok s1 st1 =>
      have hprim : (miri_etm_private% Miri.Interpreter.ValidityVisitor Miri.Interpreter.ValidityVisitor.primitive)
          h c session place (.reference mutBool) st = .ok (some s1) st1 := by
        with_unfolding_all
          exact (est_bind_ok _ _ _ _ s1 hcs).trans rfl
      exact (est_bind_ok _ _ _ _ (some s1) hprim).trans rfl
    | error e st1 =>
      have hprim : (miri_etm_private% Miri.Interpreter.ValidityVisitor Miri.Interpreter.ValidityVisitor.primitive)
          h c session place (.reference mutBool) st = .error e st1 := by
        with_unfolding_all
          exact est_bind_err _ _ _ _ e hcs
      exact est_bind_err _ _ _ _ e hprim
  refine ⟨fun hge => hvisEq _ (by rw [hstep, ite_t hge]), fun hlt => ?_⟩
  have hnge : ¬ (addr.toNat + size.bytes.toNat ≥ 2 ^ h.target.base.pointerWidth.bits.toNat - 1) :=
    Nat.not_le.mpr hlt
  refine ⟨fun hnull => hvisEq _ (by simp only [hstep, ite_f hnge, hnull]), fun hnn => ⟨
    fun hun => hvisEq _ (by simp only [hstep, ite_f hnge, hnn, hun]),
    fun hinh => ⟨
      fun mis hmis => hvisEq _ (by simp only [hstep, ite_f hnge, hnn, hinh, hmis]),
      fun halOk => hvisEq _ (by simp only [hstep, ite_f hnge, hnn, hinh, halOk])⟩⟩⟩

/-- **Exact character validity bijection (`lean-miri#82`)**: the theory's `isUnicodeScalarValue cp`
is literally `(Miri.Memory.ScalarInt.ofUInt32 cp).toChar.isOk` for EVERY 32-bit code point `cp`
(rejecting UTF-16 surrogates `0xD800..=0xDFFF` and values `> 0x10FFFF`). -/
theorem isUnicodeScalarValue_eq_scalarInt_toChar_isOk (cp : UInt32) :
    isUnicodeScalarValue cp = (Miri.Memory.ScalarInt.ofUInt32 cp).toChar.isOk := by
  have hlt : cp.toNat < 2 ^ 32 := cp.toBitVec.isLt
  have hto32 : (Miri.Memory.ScalarInt.ofUInt32 cp).toUInt32 = .ok cp := by
    unfold Miri.Memory.ScalarInt.toUInt32 Miri.Memory.ScalarInt.toUInt
      Miri.Memory.ScalarInt.toBits Miri.Memory.ScalarInt.ofUInt32
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, bind, Except.bind,
      pure, Except.pure, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (Nat.lt_trans hlt (by decide : 2 ^ 32 < 2 ^ 128))]
    congr 1
    exact UInt32.ofNat_toNat
  unfold Miri.Memory.ScalarInt.toChar
  rw [hto32]
  simp only [bind, Except.bind, pure, Except.pure]
  have his : (miri_etm_private% Miri.Memory.ScalarInt Miri.Memory.ScalarInt.isUnicodeScalar) cp.toNat =
      isUnicodeScalarValue cp := by
    change (decide (cp.toNat ≤ 0x10ffff) && !(decide (0xd800 ≤ cp.toNat) && decide (cp.toNat ≤ 0xdfff))) =
      (decide (cp.toNat ≤ 0xD7FF) || (decide (0xE000 ≤ cp.toNat) && decide (cp.toNat ≤ 0x10FFFF)))
    cases h1 : decide (cp.toNat ≤ 0xD7FF) with
    | true =>
      have h1' : cp.toNat ≤ 0xD7FF := of_decide_eq_true h1
      have hA : decide (cp.toNat ≤ 0x10ffff) = true := decide_eq_true (Nat.le_trans h1' (by decide))
      have hB : decide (0xd800 ≤ cp.toNat) = false := decide_eq_false (by omega)
      simp only [hA, hB, Bool.false_and, Bool.not_false, Bool.and_true, Bool.true_or]
    | false =>
      have h1' : ¬ (cp.toNat ≤ 0xD7FF) := of_decide_eq_false h1
      have hB : decide (0xd800 ≤ cp.toNat) = true := decide_eq_true (by omega)
      cases h2 : decide (0xE000 ≤ cp.toNat) with
      | false =>
        have h2' : ¬ (0xE000 ≤ cp.toNat) := of_decide_eq_false h2
        have hC : decide (cp.toNat ≤ 0xdfff) = true := decide_eq_true (by omega)
        simp only [hB, hC, Bool.and_true, Bool.not_true, Bool.and_false, Bool.false_and, Bool.false_or]
      | true =>
        have h2' : 0xE000 ≤ cp.toNat := of_decide_eq_true h2
        have hC : decide (cp.toNat ≤ 0xdfff) = false := decide_eq_false (by omega)
        simp only [hB, hC, Bool.and_false, Bool.not_false, Bool.and_true, Bool.true_and, Bool.false_or]
  change isUnicodeScalarValue cp =
    (if !(miri_etm_private% Miri.Memory.ScalarInt Miri.Memory.ScalarInt.isUnicodeScalar) cp.toNat
     then Except.error (Miri.Memory.ScalarIntError.invalidChar cp)
     else Except.ok (Char.ofNat cp.toNat)).isOk
  rw [his]
  cases isUnicodeScalarValue cp <;> rfl

/-- **Child-session pointee visitor theorems on vendored `ValidityVisitor.visit`** (`lean-miri#82`):
1. **Fail-closed fuel exhaustion**: `visit h c 0 session place st` ALWAYS fails with
   `.resourceExhaustion "validity traversal fuel"` (matching `visitConcreteValue 0 = .error .traversalFuelExhausted`).
2. **Provenance-agnostic zero `fn()` in `childSession`**: when `session.refTracking = none` (the
   `childSession` configuration), `visit` on `.functionPointer` consults `scalarMayBeNull` (not
   `VTable.getPtrFn`) and rejects zero-address function pointers with validation UB regardless of
   provenance.
3. **Field-before-inhabited on `(bool, !)` / `(u32, !)`**: on `.Arbitrary offsets #[0, 1]`, if
   visiting field `0` fails with `err`, `visit` returns `.error err` BEFORE visiting field `1` or
   reaching line 471 `opsemInhabited`.
4. **`O(1)` ZST-array `[(); usize::MAX]` fast-path**: on `.sequence elem` when
   `elemLayout.layout.isZst = true`, `visit` skips the element loop completely for `len = 0` and
   visits index `0` ONCE for ANY `len > 0` (including `len = usize::MAX`), matching
   `visitConcreteValue`. -/
theorem visit_childSession_pointee_correspondence {P S C E F A Pad : Type}
    [Miri.Memory.PointerProvenance P] [DecidableEq P]
    (h : Miri.Interpreter.ValidityVisitor.Hooks P S C E F A Pad) (c : C)
    (fuel : Nat) (session : Miri.Interpreter.ValidityVisitor.Session P)
    (place : Miri.Interpreter.RuntimePlace P) (st : S)
    (hctfe : session.ctfeMode = none)
    (hdebug : h.debugAssertions = false) :
    -- (1) Fail-closed fuel exhaustion
    (Miri.Interpreter.ValidityVisitor.visit h c 0 session place st =
      .error (.resourceExhaustion "validity traversal fuel") st) ∧
    -- (2) Provenance-agnostic zero `fn()` under `refTracking = none` (`childSession`)
    (session.refTracking = none →
      h.classify c place.layout.ty st = .ok .functionPointer st →
      ∀ sc, h.readImmediate c place .functionPointer st = .ok ⟨.scalar sc, place.layout⟩ st →
      h.scalarMayBeNull c sc st = .ok true st →
      Miri.Interpreter.ValidityVisitor.visit h c (fuel + 1) session place st =
        .error (.undefinedBehavior
          s!"validation{session.path.render}: null or maybe-null function pointer") st) ∧
    -- (3) Field-before-inhabited on 2-field `.Arbitrary offsets #[0, 1]` (e.g. `(bool, !)` / `(u32, !)`)
    (∀ offsets child0 path0 err st',
      h.classify c place.layout.ty st = .ok (.aggregate false false false) st →
      place.layout.layout.fields = .Arbitrary offsets #[0, 1] →
      Miri.Interpreter.PlaceDynamic.field h.projection c place 0 st = .ok child0 st →
      h.fieldPath c place.layout 0 child0.layout.ty st = .ok path0 st →
      Miri.Interpreter.ValidityVisitor.visit h c fuel
        { session with path := session.path.push path0 } child0 st = .error err st' →
      Miri.Interpreter.ValidityVisitor.visit h c (fuel + 1) session place st = .error err st') ∧
    -- (4) `O(1)` ZST-array `[(); usize::MAX]`: 0 visits for `len = 0`, 1 visit at index `0` for ANY `len > 0`
    (∀ elem elemKind elemLayout (len : UInt64),
      h.classify c place.layout.ty st = .ok (.sequence elem) st →
      h.classify c elem st = .ok elemKind st →
      elemKind ≠ .integer → elemKind ≠ .float →
      h.projection.layoutOf c elem st = .ok elemLayout st →
      elemLayout.layout.isZst = true →
      Miri.Interpreter.PlaceDynamic.length h.projection c place st = .ok len st →
      h.opsemInhabited c place.layout.ty st = .ok true st →
      (len = 0 →
        Miri.Interpreter.ValidityVisitor.visit h c (fuel + 1) session place st = .ok session st) ∧
      (len > 0 →
        ∀ child0,
          Miri.Interpreter.PlaceDynamic.index h.projection c place 0 st = .ok child0 st →
          Miri.Interpreter.ValidityVisitor.visit h c fuel
            { session with path := session.path.push (.arrayElem 0) } child0 st =
              .ok { session with path := session.path.push (.arrayElem 0) } st →
          Miri.Interpreter.ValidityVisitor.visit h c (fuel + 1) session place st = .ok session st)) := by
  cases session with | mk sp sfl sctfe srt sdb =>
  dsimp only at hctfe
  subst hctfe
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro hrt hcl sc hrd hnull
    dsimp only at hrt
    subst hrt
    unfold Miri.Interpreter.ValidityVisitor.visit
    refine (est_bind_ok _ _ _ _ _ hcl).trans ?_
    refine est_bind_err _ _ _ _ _ ?_
    with_unfolding_all
      refine (est_bind_ok _ _ _ _ _ hrd).trans ?_
      refine (est_bind_ok _ _ _ _ sc rfl).trans ?_
      rw [ite_f (by simp)]
      refine (est_bind_ok _ _ _ _ true hnull).trans ?_
      exact est_bind_err _ _ _ _ _ (by
        have hlit : (": " ++ "null or maybe-null function pointer") = ": null or maybe-null function pointer" := rfl
        change EStateM.Result.error (Miri.Interpreter.StepError.undefinedBehavior
          (toString "validation" ++ toString sp.render ++ toString ": " ++
            toString "null or maybe-null function pointer")) st = _
        simp only [toString, String.append_assoc, hlit])
  · intro offsets child0 path0 err st' hcl hfields hfld0 hfp0 hvis0
    have hsame :
        ({ path := sp.push path0,
           flags := { sfl with mayDangle := sfl.mayDangle || false },
           ctfeMode := none, refTracking := srt, dataBytes := sdb } :
          Miri.Interpreter.ValidityVisitor.Session P) =
        { path := sp.push path0, flags := sfl, ctfeMode := none, refTracking := srt, dataBytes := sdb } := by
      cases sfl; simp only [Bool.or_false]
    unfold Miri.Interpreter.ValidityVisitor.visit
    refine (est_bind_ok _ _ _ _ _ hcl).trans ?_
    have hprimNone : (miri_etm_private% Miri.Interpreter.ValidityVisitor Miri.Interpreter.ValidityVisitor.primitive)
        h c { path := sp, flags := sfl, ctfeMode := none, refTracking := srt, dataBytes := sdb }
        place (.aggregate false false false) st = .ok none st := rfl
    refine (est_bind_ok _ _ _ _ none hprimNone).trans ?_
    dsimp only
    rw [hfields]
    refine est_bind_err _ _ _ _ _ ?_
    have hfor0 :
        (forIn (m := Miri.Interpreter.RvalueM S) (#[0, 1] : Array Nat)
          ({ path := sp, flags := { sfl with mayDangle := sfl.mayDangle || false },
             ctfeMode := none, refTracking := srt, dataBytes := sdb } :
             Miri.Interpreter.ValidityVisitor.Session P)
          (fun index s => do
            let child ← Miri.Interpreter.PlaceDynamic.field h.projection c place index
            let path := s.path
            let s ← Miri.Interpreter.ValidityVisitor.visit h c fuel
              { s with path := path.push (← h.fieldPath c place.layout index child.layout.ty) } child
            pure (.yield { s with path }))) st = .error err st' := by
      rw [← Array.forIn_toList]
      change (forIn (m := Miri.Interpreter.RvalueM S) [0, 1] _ _) st = _
      rw [List.forIn_cons]
      refine est_bind_err _ _ _ _ _ ?_
      refine (est_bind_ok _ _ _ _ child0 hfld0).trans ?_
      refine (est_bind_ok _ _ _ _ path0 hfp0).trans ?_
      refine est_bind_err _ _ _ _ _ ?_
      rw [hsame]; exact hvis0
    exact hfor0
  · intro elem elemKind elemLayout len hcl hel hneInt hneFlt helLay hzst hlen hinh
    have hnotNum : (elemKind == .integer || elemKind == .float) = false := by
      simp [beq_false_of_ne hneInt, beq_false_of_ne hneFlt]
    constructor
    · intro hlen0
      subst hlen0
      unfold Miri.Interpreter.ValidityVisitor.visit
      refine (est_bind_ok _ _ _ _ _ hcl).trans ?_
      have hprimNone : (miri_etm_private% Miri.Interpreter.ValidityVisitor Miri.Interpreter.ValidityVisitor.primitive)
          h c { path := sp, flags := sfl, ctfeMode := none, refTracking := srt, dataBytes := sdb }
          place (.sequence elem) st = .ok none st := rfl
      refine (est_bind_ok _ _ _ _ none hprimNone).trans ?_
      dsimp only
      refine (est_bind_ok _ _ _ _ elemKind hel).trans ?_
      rw [hnotNum, ite_f (by decide)]
      refine (est_bind_ok _ _ _ _ elemLayout helLay).trans ?_
      rw [hzst, ite_t (by decide)]
      refine (est_bind_ok _ _ _ _ 0 hlen).trans ?_
      rw [ite_f (by decide)]
      refine (est_bind_ok _ _ _ _ true hinh).trans ?_
      rw [ite_t (by decide), hdebug, ite_f (by decide)]
      rfl
    · intro hlenPos child0 hidx0 hvis0
      unfold Miri.Interpreter.ValidityVisitor.visit
      refine (est_bind_ok _ _ _ _ _ hcl).trans ?_
      have hprimNone : (miri_etm_private% Miri.Interpreter.ValidityVisitor Miri.Interpreter.ValidityVisitor.primitive)
          h c { path := sp, flags := sfl, ctfeMode := none, refTracking := srt, dataBytes := sdb }
          place (.sequence elem) st = .ok none st := rfl
      refine (est_bind_ok _ _ _ _ none hprimNone).trans ?_
      dsimp only
      refine (est_bind_ok _ _ _ _ elemKind hel).trans ?_
      rw [hnotNum, ite_f (by decide)]
      refine (est_bind_ok _ _ _ _ elemLayout helLay).trans ?_
      rw [hzst, ite_t (by decide)]
      refine (est_bind_ok _ _ _ _ len hlen).trans ?_
      rw [ite_t hlenPos]
      refine (est_bind_ok _ _ _ _ child0 hidx0).trans ?_
      refine (est_bind_ok _ _ _ _ _ hvis0).trans ?_
      dsimp only
      refine (est_bind_ok _ _ _ _ true hinh).trans ?_
      rw [ite_t (by decide), hdebug, ite_f (by decide)]
      rfl

/-- **Root-to-`childSession` tracking handoff for recursive wide-`dyn` / thin safe references**
(`lean-miri#82`): when root `ValidityVisitor.visit` runs with `refTracking = some .empty`,
`mayDangle = false`, `ctfeMode = none`, and a safe reference passes `checkMetadata` (vtable/slice),
`checkPointerAccess`, `scalarMayBeNull`, `opsemInhabited`, and `checkPointerAlignResult`, root
`visit` records the pointee `key := ⟨target.mplace, target.layout⟩` at `path := session.path.push .deref`,
and `RefTracking.next` pops `((key, session.path.push .deref), ⟨#[key], #[]⟩)` for `childSession :=
{ path := session.path.push .deref, flags := ⟨false, true⟩, ctfeMode := none, refTracking := none,
dataBytes := none }`. -/
theorem visit_root_tracks_pointee_for_childSession {P S C E F A Pad : Type}
    [Miri.Memory.PointerProvenance P] [DecidableEq P]
    (h : Miri.Interpreter.ValidityVisitor.Hooks P S C E F A Pad) (c : C)
    (fuel : Nat) (path : Miri.Memory.ValidationPath)
    (place : Miri.Interpreter.RuntimePlace P) (st : S)
    (mutBool : Bool)
    (ptrImm : Miri.Interpreter.RvalueImmTy P) (target : Miri.Interpreter.MPlaceTy P)
    (size : Miri.ABI.Size) (align : Miri.ABI.Align) (sc : Miri.Memory.Scalar P)
    (hcl : h.classify c place.layout.ty st = .ok (.reference mutBool) st)
    (hrd : h.readImmediate c place .reference st = .ok ptrImm st)
    (hpt : h.ptrToPlace c ptrImm st = .ok target st)
    (hmetaOk : target.layout.layout.isSized = true ∨
      (miri_etm_private% Miri.Interpreter.ValidityVisitor Miri.Interpreter.ValidityVisitor.checkMetadata)
        h c target st = .ok () st)
    (hsa : h.sizeAndAlign c target st = .ok (some (size, align)) st)
    (hacc : h.checkPointerAccess c target.mplace.ptr size st = .ok (.ok ()) st)
    (hfrom : Miri.Memory.Scalar.fromMaybePointer h.target.base target.mplace.ptr = .ok sc)
    (hnn : h.scalarMayBeNull c sc st = .ok false st)
    (hinh : h.opsemInhabited c target.layout.ty st = .ok true st)
    (hal : h.checkPointerAlignResult c target.mplace.ptr align st = .ok (.ok ()) st) :
    let rootSession : Miri.Interpreter.ValidityVisitor.Session P :=
      { path, flags := ⟨false, false⟩, ctfeMode := none, refTracking := some .empty, dataBytes := none }
    let ptKey : Miri.Interpreter.ValidityVisitor.Key P := ⟨target.mplace, target.layout⟩
    let tracked : Miri.Memory.Validity.RefTracking
        (Miri.Interpreter.ValidityVisitor.Key P) Miri.Memory.ValidationPath :=
      ⟨#[ptKey], #[(ptKey, path.push .deref)]⟩
    Miri.Interpreter.ValidityVisitor.visit h c (fuel + 1) rootSession place st =
      .ok { rootSession with refTracking := some tracked } st ∧
    tracked.next = some ((ptKey, path.push .deref), ⟨#[ptKey], #[]⟩) := by
  dsimp only
  refine ⟨?_, rfl⟩
  let rootSession : Miri.Interpreter.ValidityVisitor.Session P :=
    { path, flags := ⟨false, false⟩, ctfeMode := none, refTracking := some .empty, dataBytes := none }
  let ptKey : Miri.Interpreter.ValidityVisitor.Key P := ⟨target.mplace, target.layout⟩
  let tracked : Miri.Memory.Validity.RefTracking
      (Miri.Interpreter.ValidityVisitor.Key P) Miri.Memory.ValidationPath :=
    ⟨#[ptKey], #[(ptKey, path.push .deref)]⟩
  have hcs : (miri_etm_private% Miri.Interpreter.ValidityVisitor Miri.Interpreter.ValidityVisitor.checkSafe)
      h c rootSession place place.layout.ty (.reference mutBool) st =
      .ok { rootSession with refTracking := some tracked } st := by
    with_unfolding_all
      refine (est_bind_ok _ _ _ _ _ hrd).trans ?_
      rw [ite_f (by simp [rootSession])]
      dsimp only
      refine (est_bind_ok _ _ _ _ _ hpt).trans ?_
      have hskipMeta : ∀ (k : Unit → Miri.Interpreter.ValidityVisitor.M S (Miri.Interpreter.ValidityVisitor.Session P)),
          (if !target.layout.layout.isSized then
            (miri_etm_private% Miri.Interpreter.ValidityVisitor Miri.Interpreter.ValidityVisitor.checkMetadata) h c target >>= k
          else k ()) st = k () st := by
        intro k
        rcases hmetaOk with hs | hm
        · rw [hs, Bool.not_true, ite_f (by decide)]
        · cases hb : target.layout.layout.isSized with
          | true => rw [Bool.not_true, ite_f (by decide)]
          | false => rw [Bool.not_false, ite_t (by decide)]; exact est_bind_ok _ _ _ _ () hm
      rw [hskipMeta]
      refine (est_bind_ok _ _ _ _ _ hsa).trans ?_
      rw [Option.getD_some, ite_t (by simp [rootSession])]
      refine (est_bind_ok _ _ _ _ (.ok ()) hacc).trans ?_
      dsimp only
      rw [ite_f (by simp [rootSession])]
      refine (est_bind_ok _ _ _ _ none rfl).trans ?_
      dsimp only
      rw [ite_f (by simp [rootSession])]
      refine (est_bind_ok _ _ _ _ sc (by rw [hfrom]; rfl)).trans ?_
      refine (est_bind_ok _ _ _ _ false hnn).trans ?_
      refine (est_bind_ok _ _ _ _ true hinh).trans ?_
      refine (est_bind_ok _ _ st st () (by simp [Miri.Interpreter.ValidityVisitor.mapPointerAlignmentOutcome, hal])).trans ?_
      rfl
  unfold Miri.Interpreter.ValidityVisitor.visit
  refine (est_bind_ok _ _ _ _ _ hcl).trans ?_
  have hprim : (miri_etm_private% Miri.Interpreter.ValidityVisitor Miri.Interpreter.ValidityVisitor.primitive)
      h c rootSession place (.reference mutBool) st =
      .ok (some { rootSession with refTracking := some tracked }) st := by
    with_unfolding_all
      exact (est_bind_ok _ _ _ _ _ hcs).trans rfl
  exact (est_bind_ok _ _ _ _ _ hprim).trans rfl

/-- **16-byte nested wide `&dyn Trait` inside `childSession` (`lean-miri#82`)**: combines
`visit_wideDyn_checkSafe_vtableBeforeDataUB` and `visit_checkSafe_mayDangle_precedence` at the
exact `childSession := { path := path.push .deref, flags := ⟨false, true⟩, ctfeMode := none,
refTracking := none, dataBytes := none }` popped from `RefTracking`:
1. An invalid vtable metadata word fails BEFORE any data-pointer check (matching
   `checkNestedWideSafeRefChildSession` / `worldNestedDynOracle`).
2. A valid vtable proceeds under `mayDangle = true` (`addressTooClose` → `null` → `uninhabited` →
   `align`), skipping `checkPointerAccess` and returning `childSession` unchanged without further
   recursive tracking. -/
theorem visit_nested_wideSafeRef_childSession {S C E F A Pad : Type}
    (h : Miri.Interpreter.ValidityVisitor.Hooks Miri.Memory.Provenance S C E F A Pad) (c : C)
    (fuel : Nat) (path : Miri.Memory.ValidationPath)
    (place : Miri.Interpreter.RuntimePlace Miri.Memory.Provenance) (st : S)
    (mutBool : Bool) (expected : Nat)
    (ptrImm : Miri.Interpreter.RvalueImmTy Miri.Memory.Provenance)
    (target : Miri.Interpreter.MPlaceTy Miri.Memory.Provenance)
    (metaScalar : Miri.Memory.Scalar Miri.Memory.Provenance)
    (vtPtr : Miri.Memory.Pointer (Option Miri.Memory.Provenance))
    (hcl : h.classify c place.layout.ty st = .ok (.reference mutBool) st)
    (hrd : h.readImmediate c place .reference st = .ok ptrImm st)
    (hpt : h.ptrToPlace c ptrImm st = .ok target st)
    (htuns : target.layout.layout.isSized = false)
    (hmt : h.metadataTail c target.layout.ty st = .ok (.dynamic expected) st)
    (hunwrap : target.mplace.metadata.unwrapMeta = .ok metaScalar)
    (htoptr : metaScalar.toPointer h.target.base = .ok vtPtr) :
    let childSession : Miri.Interpreter.ValidityVisitor.Session Miri.Memory.Provenance :=
      { path := path.push .deref, flags := ⟨false, true⟩, ctfeMode := none, refTracking := none, dataBytes := none }
    (∀ err st',
      Miri.Interpreter.VTable.getPtrVTableType h.vtable c vtPtr (some expected) st = .error err st' →
      Miri.Interpreter.ValidityVisitor.visit h c (fuel + 1) childSession place st = .error err st') ∧
    (∀ vtTy size align sc intVal addr,
      Miri.Interpreter.VTable.getPtrVTableType h.vtable c vtPtr (some expected) st = .ok vtTy st →
      h.sizeAndAlign c target st = .ok (some (size, align)) st →
      Miri.Memory.Scalar.fromMaybePointer h.target.base target.mplace.ptr = .ok sc →
      sc.tryToScalarInt = .ok (.integer intVal) →
      intVal.toTargetUsize h.target.pointerSize = .ok addr →
      let maximum : Nat := 2 ^ h.target.base.pointerWidth.bits.toNat - 1
      (addr.toNat + size.bytes.toNat ≥ maximum →
        Miri.Interpreter.ValidityVisitor.visit h c (fuel + 1) childSession place st =
          .error (.undefinedBehavior
            s!"validation{childSession.path.render}: safe pointer too close to address-space end") st) ∧
      (addr.toNat + size.bytes.toNat < maximum →
        h.scalarMayBeNull c sc st = .ok false st →
        h.opsemInhabited c target.layout.ty st = .ok true st →
        h.checkPointerAlignResult c target.mplace.ptr align st = .ok (.ok ()) st →
        Miri.Interpreter.ValidityVisitor.visit h c (fuel + 1) childSession place st =
          .ok childSession st)) := by
  dsimp only
  let childSession : Miri.Interpreter.ValidityVisitor.Session Miri.Memory.Provenance :=
    { path := path.push .deref, flags := ⟨false, true⟩, ctfeMode := none, refTracking := none, dataBytes := none }
  refine ⟨fun err st' hvtErr =>
    visit_wideDyn_checkSafe_vtableBeforeDataUB h c fuel childSession place st mutBool expected
      ptrImm target metaScalar vtPtr err st' rfl hcl hrd hpt htuns hmt hunwrap htoptr hvtErr,
    fun vtTy size align sc intVal addr hvtOk hsa hfrom htry haddr => ?_⟩
  have hcmOk : (miri_etm_private% Miri.Interpreter.ValidityVisitor Miri.Interpreter.ValidityVisitor.checkMetadata)
      h c target st = .ok () st := by
    rw [checkMetadata_dynamic_eq h c target st expected metaScalar vtPtr hmt hunwrap htoptr, hvtOk]
  have hmd := visit_checkSafe_mayDangle_precedence h c fuel childSession place st mutBool
    ptrImm target size align sc intVal addr rfl rfl hcl hrd hpt (Or.inr hcmOk) hsa hfrom htry haddr
  exact ⟨hmd.1, fun hlt hnn hinh hal => ((((hmd.2 hlt).2 hnn).2 hinh).2 hal)⟩

/-! ## Part 2D. Round-1 counter-audit strengthenings

Strengthenings of Parts 1C, 1E, and 2: two-way and hypothesis-minimal `StateRelLM3_*` liftings,
the frame pop for arbitrarily many protectors with a whole-frame simulation against
`execFrameExitMiri`, and state/choice-polymorphic vtable reads through the `validatePlace` driver
with the exact `annealValidityHooks` boundary. -/

/-! ### 2D.1 `KeyedStateRelLM3_*` ↔ `StateRelLM3_*` and direct `live` / `dead` permutation invariance -/

/-- **Two-way characterization (`KeyedStateRelLM3_1` ↔ `StateRelLM3_1`)**: `KeyedStateRelLM3_1` is
EXACTLY `StateRelLM3_1` together with the functional equation `kw = annealMachineToKeyed m.machine`;
the keyed lifting adds no invariant beyond `StateRelLM3_1`. -/
theorem keyedStateRelLM3_1_iff {body : Trusted.Rustc.V2026_06_01.MirAst.CapturedMir}
    {s : MachineState} {m : AnnealStepState} {allocMap : List AllocMapEntry}
    {kw : KeyedAllocWorld} :
    KeyedStateRelLM3_1 body s m allocMap kw ↔
      StateRelLM3_1 body s m allocMap ∧ kw = annealMachineToKeyed m.machine :=
  ⟨fun h => ⟨h.stateRel, h.keyed_eq⟩, fun h => ⟨h.1, h.2⟩⟩

/-- **Two-way characterization (`KeyedStateRelLM3_2` ↔ `StateRelLM3_2`)**. -/
theorem keyedStateRelLM3_2_iff {body : Trusted.Rustc.V2026_06_01.MirAst.CapturedMir}
    {s : MachineState} {m : AnnealStepState} {allocMap : List AllocMapEntry}
    {kw : KeyedAllocWorld} :
    KeyedStateRelLM3_2 body s m allocMap kw ↔
      StateRelLM3_2 body s m allocMap ∧ kw = annealMachineToKeyed m.machine :=
  ⟨fun h => ⟨h.stateRel, h.keyed_eq⟩, fun h => ⟨h.1, h.2⟩⟩

/-- `StateRelLM3_1` holds iff SOME keyed lifting exists, and the keyed world of a lifting is unique:
`StateRelLM3_1` and `∃! kw, KeyedStateRelLM3_1 … kw` are interchangeable. -/
theorem stateRelLM3_1_iff_existsUnique_keyed
    {body : Trusted.Rustc.V2026_06_01.MirAst.CapturedMir}
    {s : MachineState} {m : AnnealStepState} {allocMap : List AllocMapEntry} :
    StateRelLM3_1 body s m allocMap ↔
      ∃ kw, KeyedStateRelLM3_1 body s m allocMap kw ∧
        ∀ kw', KeyedStateRelLM3_1 body s m allocMap kw' → kw' = kw :=
  ⟨fun h => ⟨annealMachineToKeyed m.machine, ⟨h, rfl⟩, fun _ h' => h'.keyed_eq⟩,
   fun ⟨_, h, _⟩ => h.stateRel⟩

/-- `StateRelLM3_2` holds iff SOME keyed lifting exists, and the keyed world of a lifting is unique. -/
theorem stateRelLM3_2_iff_existsUnique_keyed
    {body : Trusted.Rustc.V2026_06_01.MirAst.CapturedMir}
    {s : MachineState} {m : AnnealStepState} {allocMap : List AllocMapEntry} :
    StateRelLM3_2 body s m allocMap ↔
      ∃ kw, KeyedStateRelLM3_2 body s m allocMap kw ∧
        ∀ kw', KeyedStateRelLM3_2 body s m allocMap kw' → kw' = kw :=
  ⟨fun h => ⟨annealMachineToKeyed m.machine, ⟨h, rfl⟩, fun _ h' => h'.keyed_eq⟩,
   fun ⟨_, h, _⟩ => h.stateRel⟩

/-- First-match lookup of ONE key is permutation-invariant as soon as that key's rows agree on their
payload — no global distinct-key (`Nodup`) hypothesis. -/
private theorem list_find?_eq_of_perm_keyUnique {α : Type}
    {xs ys : List (Miri.Memory.AllocId × α)} (hperm : xs.Perm ys) (id : Miri.Memory.AllocId)
    (huniq : ∀ a₁ a₂, (id, a₁) ∈ xs → (id, a₂) ∈ xs → a₁ = a₂) :
    xs.find? (fun row => row.1 == id) = ys.find? (fun row => row.1 == id) := by
  cases hx : xs.find? (fun row => row.1 == id) with
  | none =>
    cases hy : ys.find? (fun row => row.1 == id) with
    | none => rfl
    | some r =>
      have hm := hperm.symm.subset (List.mem_of_find?_eq_some hy)
      have hp := List.find?_some hy
      have hnone := List.find?_eq_none.mp hx r hm
      exact absurd hp hnone
  | some r =>
    cases hy : ys.find? (fun row => row.1 == id) with
    | none =>
      have hm := hperm.subset (List.mem_of_find?_eq_some hx)
      have hp := List.find?_some hx
      exact absurd hp (List.find?_eq_none.mp hy r hm)
    | some r' =>
      have h1 : r.1 = id := eq_of_beq (by simpa using List.find?_some hx)
      have h2 : r'.1 = id := eq_of_beq (by simpa using List.find?_some hy)
      have hm1 := List.mem_of_find?_eq_some hx
      have hm2 := hperm.symm.subset (List.mem_of_find?_eq_some hy)
      obtain ⟨k, a⟩ := r
      obtain ⟨k', a'⟩ := r'
      simp only at h1 h2
      subst h1; subst h2
      rw [huniq a a' hm1 hm2]

/-- `AllocMapRel` transports along ANY `live` permutation and ANY replacement of `dead`. -/
private theorem allocMapRel_of_livePerm
    {body : Trusted.Rustc.V2026_06_01.MirAst.CapturedMir} {s : MachineState}
    {m : AnnealStepState} {allocMap : List AllocMapEntry}
    (halloc : AllocMapRel body s m allocMap)
    (live' : Array (Miri.Memory.AllocId ×
      Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind))
    (dead' : Array Miri.Memory.DeadAllocation)
    (hlivePerm : m.machine.memory.live.toList.Perm live'.toList) :
    AllocMapRel body s
      { m with machine := { m.machine with memory :=
        { m.machine.memory with live := live', dead := dead' } } } allocMap :=
  { tags_nodup := halloc.tags_nodup
    local_to_alloc_unique := halloc.local_to_alloc_unique
    alloc_to_local_injective := halloc.alloc_to_local_injective
    target_decl := halloc.target_decl
    base_addr_valid := halloc.base_addr_valid
    borrow_sync := halloc.borrow_sync
    live_key_unique := fun e he la₁ la₂ h1 h2 =>
      halloc.live_key_unique e he la₁ la₂ (hlivePerm.symm.subset h1) (hlivePerm.symm.subset h2)
    local_alloc_sync := fun tf' hfrEq e he => by
      have hsync := halloc.local_alloc_sync tf' hfrEq e he
      have hfindEq : live'.find? (fun x => x.1 == e.allocId) =
          m.machine.memory.live.find? (fun x => x.1 == e.allocId) := by
        rw [← Array.find?_toList, ← Array.find?_toList]
        exact (list_find?_eq_of_perm_keyUnique hlivePerm e.allocId
          (halloc.live_key_unique e he)).symm
      refine ⟨fun slot hslot hne => ?_, fun hdead => ?_⟩
      · rcases hsync.1 slot hslot hne with ⟨hloc, hsc, hdecl⟩
        refine ⟨hloc, hsc, fun decl hd => ?_⟩
        rcases hdecl decl hd with ⟨la, hfind, hk, ha, hsh⟩
        exact ⟨la, by rw [hfindEq]; exact hfind, hk, ha, hsh⟩
      · rw [hfindEq]; exact hsync.2 hdead }

/-- **Direct `StateRelLM3_1` invariance, with no distinct-key hypothesis**: `StateRelLM3_1` itself
(not a keyed projection of it) is preserved by ANY permutation of `m.machine.memory.live` — even
with duplicate keys, because `AllocMapRel.live_key_unique` already makes the first-match lookup of
every mapped allocation order-independent — and by ANY replacement of `m.machine.memory.dead`
(the relation never reads tombstones). The `Nodup` and `MemoryStateGlobalsDistinct` hypotheses of
`keyedStateRelLM3_1_liveDead_perm_invariant` are needed only for the equality of the KEYED world
(`annealMachineToKeyed_eq_of_liveDead_perm`, `liveDuplicateKey_perm_separation_canary`). -/
theorem stateRelLM3_1_livePerm_deadAny
    {body : Trusted.Rustc.V2026_06_01.MirAst.CapturedMir} {s : MachineState}
    {m : AnnealStepState} {allocMap : List AllocMapEntry}
    (h : StateRelLM3_1 body s m allocMap)
    (live' : Array (Miri.Memory.AllocId ×
      Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind))
    (dead' : Array Miri.Memory.DeadAllocation)
    (hlivePerm : m.machine.memory.live.toList.Perm live'.toList) :
    StateRelLM3_1 body s
      { m with machine := { m.machine with memory :=
        { m.machine.memory with live := live', dead := dead' } } } allocMap := by
  rcases h with ⟨tf, hframes, hrc, hrp, hfr, hac, hcs, hap, hcl, hbor, halloc, hdisj⟩
  exact .mk tf hframes hrc hrp
    (hfr.of_live_base (fun e he => hlivePerm.subset he) (fun _ _ _ => rfl))
    hac hcs hap hcl hbor (allocMapRel_of_livePerm halloc live' dead' hlivePerm) hdisj

/-- **Direct `StateRelLM3_2` invariance, with no distinct-key hypothesis**: `StateRelLM3_2` is
preserved by ANY permutation of `m.machine.memory.live` and ANY replacement of
`m.machine.memory.dead`. -/
theorem stateRelLM3_2_livePerm_deadAny
    {body : Trusted.Rustc.V2026_06_01.MirAst.CapturedMir} {s : MachineState}
    {m : AnnealStepState} {allocMap : List AllocMapEntry}
    (h : StateRelLM3_2 body s m allocMap)
    (live' : Array (Miri.Memory.AllocId ×
      Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind))
    (dead' : Array Miri.Memory.DeadAllocation)
    (hlivePerm : m.machine.memory.live.toList.Perm live'.toList) :
    StateRelLM3_2 body s
      { m with machine := { m.machine with memory :=
        { m.machine.memory with live := live', dead := dead' } } } allocMap := by
  rcases h with ⟨tf, hframes, hrc, hrp, hfr, hac, hcs, hap, hcl, hbor, halloc, hdisj⟩
  exact .mk tf hframes hrc hrp
    (hfr.of_live_base (fun e he => hlivePerm.subset he) (fun _ _ _ => rfl))
    hac hcs hap hcl hbor (allocMapRel_of_livePerm halloc live' dead' hlivePerm) hdisj

/-- Two-way form of `stateRelLM3_1_livePerm_deadAny`: `StateRelLM3_1` cannot distinguish a machine
from the same machine with permuted `live` rows and arbitrary `dead` rows. -/
theorem stateRelLM3_1_livePerm_deadAny_iff
    {body : Trusted.Rustc.V2026_06_01.MirAst.CapturedMir} {s : MachineState}
    {m : AnnealStepState} {allocMap : List AllocMapEntry}
    (live' : Array (Miri.Memory.AllocId ×
      Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind))
    (dead' : Array Miri.Memory.DeadAllocation)
    (hlivePerm : m.machine.memory.live.toList.Perm live'.toList) :
    StateRelLM3_1 body s m allocMap ↔
      StateRelLM3_1 body s
        { m with machine := { m.machine with memory :=
          { m.machine.memory with live := live', dead := dead' } } } allocMap := by
  refine ⟨fun h => stateRelLM3_1_livePerm_deadAny h live' dead' hlivePerm, fun h => ?_⟩
  have h' := stateRelLM3_1_livePerm_deadAny h m.machine.memory.live m.machine.memory.dead
    hlivePerm.symm
  exact h'

/-- Two-way form of `stateRelLM3_2_livePerm_deadAny`. -/
theorem stateRelLM3_2_livePerm_deadAny_iff
    {body : Trusted.Rustc.V2026_06_01.MirAst.CapturedMir} {s : MachineState}
    {m : AnnealStepState} {allocMap : List AllocMapEntry}
    (live' : Array (Miri.Memory.AllocId ×
      Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind))
    (dead' : Array Miri.Memory.DeadAllocation)
    (hlivePerm : m.machine.memory.live.toList.Perm live'.toList) :
    StateRelLM3_2 body s m allocMap ↔
      StateRelLM3_2 body s
        { m with machine := { m.machine with memory :=
          { m.machine.memory with live := live', dead := dead' } } } allocMap := by
  refine ⟨fun h => stateRelLM3_2_livePerm_deadAny h live' dead' hlivePerm, fun h => ?_⟩
  have h' := stateRelLM3_2_livePerm_deadAny h m.machine.memory.live m.machine.memory.dead
    hlivePerm.symm
  exact h'



/-- The keyed world of an `AnnealMachine` is invariant under distinct-key `live` / `dead`
permutations with NO distinctness assumption on the (unchanged) compiler-global table: the
`MemoryStateGlobalsDistinct` hypothesis of `memoryState_toKeyed_eq_of_perm` is needed only when the
global rows themselves are permuted. -/
theorem annealMachineToKeyed_eq_of_liveDead_perm (mach : AnnealMachine)
    (live' : Array (Miri.Memory.AllocId ×
      Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind))
    (dead' : Array Miri.Memory.DeadAllocation)
    (hlivePerm : mach.memory.live.toList.Perm live'.toList)
    (hliveNd : (mach.memory.live.toList.map Prod.fst).Nodup)
    (hdeadPerm : mach.memory.dead.toList.Perm dead'.toList)
    (hdeadNd : (mach.memory.dead.toList.map fun d => d.allocId).Nodup) :
    annealMachineToKeyed
        { mach with memory := { mach.memory with live := live', dead := dead' } } =
      annealMachineToKeyed mach := by
  have r1 := allocWorldRel_memoryState annealRowProjection mach.memory
  have r2 := allocWorldRel_memoryState annealRowProjection
    { mach.memory with live := live', dead := dead' }
  apply KeyedAllocWorld.ext
  · rfl
  · rfl
  · intro _; rfl
  · intro _; rfl
  · intro id
    show (memoryStateToKeyed annealRowProjection
        { mach.memory with live := live', dead := dead' }).findLive? id =
      (memoryStateToKeyed annealRowProjection mach.memory).findLive? id
    rw [← r2.live_rel, ← r1.live_rel]
    refine (linearFind?_eq_of_perm (hlivePerm.map _) ?_ id).symm
    show ((mach.memory.live.toList.map fun row =>
        (ofMiriAllocId row.1, liveEntryOfMiri annealRowProjection row.2)).map Prod.fst).Nodup
    rw [List.map_map]
    exact nodup_map_ofMiri mach.memory.live.toList (fun row => row.1) hliveNd
  · intro id
    show (memoryStateToKeyed annealRowProjection
        { mach.memory with live := live', dead := dead' }).findDead? id =
      (memoryStateToKeyed annealRowProjection mach.memory).findDead? id
    rw [← r2.dead_rel, ← r1.dead_rel]
    refine (linearFind?_eq_of_perm (hdeadPerm.map _) ?_ id).symm
    show ((mach.memory.dead.toList.map fun d =>
        (ofMiriAllocId d.allocId, deadEntryOfMiri d)).map Prod.fst).Nodup
    rw [List.map_map]
    exact nodup_map_ofMiri mach.memory.dead.toList (fun d => d.allocId) hdeadNd
  · intro _; rfl

/-- **Two-way `KeyedStateRelLM3_1` live/dead permutation invariance**, strengthening
`keyedStateRelLM3_1_liveDead_perm_invariant` to an equivalence and dropping its
`MemoryStateGlobalsDistinct` hypothesis. -/
theorem keyedStateRelLM3_1_liveDead_perm_iff
    {body : Trusted.Rustc.V2026_06_01.MirAst.CapturedMir} {s : MachineState}
    {m : AnnealStepState} {allocMap : List AllocMapEntry} {kw : KeyedAllocWorld}
    (live' : Array (Miri.Memory.AllocId ×
      Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind))
    (dead' : Array Miri.Memory.DeadAllocation)
    (hlivePerm : m.machine.memory.live.toList.Perm live'.toList)
    (hliveNd : (m.machine.memory.live.toList.map Prod.fst).Nodup)
    (hdeadPerm : m.machine.memory.dead.toList.Perm dead'.toList)
    (hdeadNd : (m.machine.memory.dead.toList.map fun d => d.allocId).Nodup) :
    KeyedStateRelLM3_1 body s m allocMap kw ↔
      KeyedStateRelLM3_1 body s
        { m with machine := { m.machine with memory :=
          { m.machine.memory with live := live', dead := dead' } } } allocMap kw := by
  have hkw := annealMachineToKeyed_eq_of_liveDead_perm m.machine live' dead' hlivePerm hliveNd
    hdeadPerm hdeadNd
  rw [keyedStateRelLM3_1_iff, keyedStateRelLM3_1_iff,
    ← stateRelLM3_1_livePerm_deadAny_iff live' dead' hlivePerm]
  constructor
  · rintro ⟨h, rfl⟩; exact ⟨h, hkw.symm⟩
  · rintro ⟨h, rfl⟩; exact ⟨h, hkw⟩

/-- **Two-way `KeyedStateRelLM3_2` live/dead permutation invariance**, strengthening
`keyedStateRelLM3_2_liveDead_perm_invariant` to an equivalence and dropping its
`MemoryStateGlobalsDistinct` hypothesis. -/
theorem keyedStateRelLM3_2_liveDead_perm_iff
    {body : Trusted.Rustc.V2026_06_01.MirAst.CapturedMir} {s : MachineState}
    {m : AnnealStepState} {allocMap : List AllocMapEntry} {kw : KeyedAllocWorld}
    (live' : Array (Miri.Memory.AllocId ×
      Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind))
    (dead' : Array Miri.Memory.DeadAllocation)
    (hlivePerm : m.machine.memory.live.toList.Perm live'.toList)
    (hliveNd : (m.machine.memory.live.toList.map Prod.fst).Nodup)
    (hdeadPerm : m.machine.memory.dead.toList.Perm dead'.toList)
    (hdeadNd : (m.machine.memory.dead.toList.map fun d => d.allocId).Nodup) :
    KeyedStateRelLM3_2 body s m allocMap kw ↔
      KeyedStateRelLM3_2 body s
        { m with machine := { m.machine with memory :=
          { m.machine.memory with live := live', dead := dead' } } } allocMap kw := by
  have hkw := annealMachineToKeyed_eq_of_liveDead_perm m.machine live' dead' hlivePerm hliveNd
    hdeadPerm hdeadNd
  rw [keyedStateRelLM3_2_iff, keyedStateRelLM3_2_iff,
    ← stateRelLM3_2_livePerm_deadAny_iff live' dead' hlivePerm]
  constructor
  · rintro ⟨h, rfl⟩; exact ⟨h, hkw.symm⟩
  · rintro ⟨h, rfl⟩; exact ⟨h, hkw⟩

/-! ### 2D.2 Deallocation data-race stage (one relational theorem for every branch) and the exact
race-table effect of `AllocationMachine.deallocate` -/

local macro "miriRaceSize" : term =>
  `(miri_etm_private% Miri.Interpreter.MachineHooks Miri.Interpreter.MachineHooks.raceSize)

/-- The theory `RaceDetectorMode` of a vendored machine: `.unconfigured` iff `dataRace = none`,
otherwise `.configured global.raceDetecting`. -/
def raceModeOfMachine {K User : Type}
    (machine : Miri.Interpreter.MachineHooks.MachineState K User) : RaceDetectorMode :=
  match machine.dataRace with
  | none => .unconfigured
  | some global => .configured global.raceDetecting

/-- Outcome correspondence of the deallocation data-race stage (`MachineHooks.memoryRaceAccess`
with `some .Deallocate`) against `machineDeallocHook`: success, the missing-vector-clock failure,
and the data-race undefined behavior correspond one-to-one; nothing else is related. -/
inductive DeallocRaceStageRel :
    Except Miri.Interpreter.StepError Unit → Except String Unit → Prop
  | ok : DeallocRaceStageRel (.ok ()) (.ok ())
  | missingClock :
    DeallocRaceStageRel (.error (.invalidProgram "allocation missing vector-clock extra"))
      (.error "MissingVectorClockExtra")
  | dataRace : DeallocRaceStageRel (.error (.undefinedBehavior "DataRace")) (.error "DataRace")

/-- **Deallocation data-race stage, every branch in ONE relational statement**
(`MachineHooks.memoryRaceAccess … (some .Deallocate)` vs `machineDeallocHook`). The theory inputs
are DERIVED from the vendored machine — the mode is `raceModeOfMachine machine` and the clock
option `clk?` is present exactly when the vendored vector clock is — instead of being unrelated
parameters. The outcomes then correspond (`DeallocRaceStageRel`) on all branches:
* detector unconfigured — no-op;
* configured but vector clock missing — `MissingVectorClockExtra`, reported BEFORE the
  `raceDetecting` gate;
* `raceDetecting = false` — no-op without reading clocks;
* detecting, zero-sized range — never a race (`writeNonAtomic_zeroSize_ok`), whatever the clocks;
* detecting, nonzero range — a race exactly when `hasDeallocDataRace` holds, given the vector-clock
  abstraction hypothesis that `VClockAlloc.writeNonAtomic` reports `.race` iff
  `hasDeallocDataRace actor clk` (multi-reader clocks and the unlisted-thread zero fallback of
  `DeallocActor.ofVClock` enter only through this hypothesis;
  `nonAtomicWriteDetect_dealloc_writer_race_iff` discharges its single-cell writer case). -/
theorem memoryRaceAccess_dealloc_rel_machineDeallocHook {K User : Type}
    (machine : Miri.Interpreter.MachineHooks.MachineState K User)
    (id : Miri.Memory.AllocId) (size : Miri.ABI.Size)
    (actor : DeallocActor) (clk? : Option RaceClockEntry)
    (hclk : clk?.isSome = (machine.raceAllocations.find? fun entry => entry.1 == id).isSome)
    (hactive : ∀ global, machine.dataRace = some global → global.raceDetecting = true →
      ∃ index clocks, global.activeThreadState machine.threads = .ok (index, clocks) ∧
        ∀ row clk, machine.raceAllocations.find? (fun entry => entry.1 == id) = some row →
          clk? = some clk → size.bytes ≠ 0 →
          (row.2.writeNonAtomic ⟨miriRaceSize Miri.ABI.Size.ZERO, miriRaceSize size⟩ clocks index
            .Deallocate).result = if hasDeallocDataRace actor clk then .race else .ok) :
    DeallocRaceStageRel
      (Miri.Interpreter.MachineHooks.memoryRaceAccess machine id ⟨Miri.ABI.Size.ZERO, size⟩
        (some .Deallocate) .Read).2
      (machineDeallocHook (raceModeOfMachine machine) actor .ok clk? size.bytes) := by
  unfold Miri.Interpreter.MachineHooks.memoryRaceAccess raceModeOfMachine
  cases hdr : machine.dataRace with
  | none =>
    simp only [Id.run, pure, Pure.pure]
    exact .ok
  | some global =>
    cases hf : machine.raceAllocations.find? (fun entry => entry.1 == id) with
    | none =>
      rw [hf] at hclk
      cases clk? with
      | some _ => cases hclk
      | none =>
        simp only [Id.run, pure, Pure.pure, bind, Bind.bind]
        exact .missingClock
    | some row =>
      rw [hf] at hclk
      cases clk? with
      | none => cases hclk
      | some clk =>
        cases hdet : global.raceDetecting with
        | false =>
          simp only [hdet, Id.run, pure, Pure.pure, bind, Bind.bind, Bool.not_false, ↓reduceIte]
          exact .ok
        | true =>
          obtain ⟨index, clocks, hact, hres⟩ := hactive global hdr hdet
          simp only [hdet, hact, Id.run, pure, Pure.pure, bind, Bind.bind, Bool.not_true,
            Bool.false_eq_true, ↓reduceIte]
          by_cases hz : size.bytes = 0
          · obtain ⟨b⟩ := size
            simp only at hz
            subst hz
            have h0 : (row.2.writeNonAtomic
                ⟨miriRaceSize Miri.ABI.Size.ZERO, miriRaceSize ⟨0⟩⟩ clocks index
                .Deallocate).result = .ok :=
              (writeNonAtomic_zeroSize_ok row.2 clocks index (miriRaceSize Miri.ABI.Size.ZERO)
                (Nat.zero_le _) actor clk).1
            rw [h0]
            exact .ok
          · rw [hres row clk hf rfl hz]
            have hnz : (size.bytes != 0) = true := bne_iff_ne.mpr hz
            cases hr : hasDeallocDataRace actor clk with
            | true =>
              simp only [machineDeallocHook, hnz, hr, Bool.and_self, ↓reduceIte]
              exact .dataRace
            | false =>
              simp only [machineDeallocHook, hr, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
              exact .ok

/-- **Exact race-table effect of `AllocationMachine.deallocate` on BOTH branches
(`detachRaceClock`)**: after the vendored machine deallocation — whether it succeeds or throws —
the vector-clock table is the hook-state table with the detached allocation's clock removed when
`deallocatePtrWith` detached an allocation (success AND every post-removal failure), and is the
hook-state table UNCHANGED when nothing was detached (every pre-removal failure). This is the
two-sided content of `KeyedAllocWorld.detachRaceClock`, strengthening
`allocationMachine_deallocate_detaches_race_on_postRemoval` from "the detached clock is absent" to
the exact post-state table. -/
theorem allocationMachine_deallocate_raceAllocations_eq {K User Payload : Type}
    [DecidableEq K]
    (h : Miri.Interpreter.AllocationMachine.DeallocationHooks K User Payload)
    (ptr : Miri.Memory.Pointer (Option Miri.Memory.Provenance))
    (oldLayout : Option (Miri.ABI.Size × Miri.ABI.Align))
    (kind : Miri.Memory.MemoryKind K)
    (st : Miri.Interpreter.MachineHooks.State K User)
    (hnoNative : ∀ id entry,
      (Miri.Memory.MemoryLifecycle.deallocatePtrWith st.machine.memory ⟨st.machine, none⟩
          ptr oldLayout kind
          { synchronizeMemory := fun memory access =>
              { access with machine := { access.machine with memory } }
            resolvePointer := h.resolvePointer
            beforeDeallocation := miriAllocMachCallback h }).detached = some (id, entry) →
      entry.allocation.nativeBuffer = none) :
    let res := Miri.Memory.MemoryLifecycle.deallocatePtrWith st.machine.memory ⟨st.machine, none⟩
      ptr oldLayout kind
      { synchronizeMemory := fun memory access =>
          { access with machine := { access.machine with memory } }
        resolvePointer := h.resolvePointer
        beforeDeallocation := miriAllocMachCallback h }
    let st' :=
      match Miri.Interpreter.AllocationMachine.deallocate h ptr oldLayout kind st with
      | .ok _ s => s
      | .error _ s => s
    st'.machine.raceAllocations =
      match res.detached with
      | some (id, _) => res.hooks.machine.raceAllocations.filter fun e => e.1 != id
      | none => res.hooks.machine.raceAllocations := by
  dsimp only
  unfold Miri.Interpreter.AllocationMachine.deallocate
  simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind,
    modify, pure, Pure.pure, throw, throwThe, MonadExceptOf.throw]
  generalize Miri.Memory.MemoryLifecycle.deallocatePtrWith st.machine.memory ⟨st.machine, none⟩
      ptr oldLayout kind
      { synchronizeMemory := fun memory access =>
          { access with machine := { access.machine with memory } }
        resolvePointer := h.resolvePointer
        beforeDeallocation := miriAllocMachCallback h } = res at hnoNative ⊢
  cases hd : res.detached with
  | none =>
    cases res.outcome <;> rfl
  | some pair =>
    obtain ⟨id, entry⟩ := pair
    have hnn := hnoNative id entry hd
    simp only [hnn, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
    cases res.outcome <;> rfl

/-! ### 2D.3 N-ary frame pop: `beforeStackPopWithEnsure` as a release fold, and whole-frame
simulation against `execFrameExitMiri` -/


/-- Classification of one `BorrowTree.releaseProtector` status inside
`MachineHooks.beforeStackPopWithEnsure`: `some none` = released (the loop continues),
`some (some err)` = an implicit protector-end access failed and the frame pop throws `err`
(`borrowAccessError`), `none` = an internal release-invariant status outside the specified domain. -/
def stackPopReleaseErr :
    Miri.TreeBorrows.BorrowTree.ProtectorReleaseStatus → Option (Option Miri.Interpreter.StepError)
  | .Released => some none
  | .AccessFailure _ status => some (some (miriBorrowAccessError status))
  | _ => none

/-- Memory after writing one released protector's tree back into its live allocation row
(`MemoryState.setLiveAllocation`). -/
def stackPopWriteBack {K : Type}
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree K)
    (id : Miri.Memory.AllocId)
    (entry : Miri.Memory.LocalAllocation Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree K)
    (tree : Miri.TreeBorrows.BorrowTree) :
    Miri.Memory.MemoryState Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree K :=
  { mem with live := (mem.live.filter fun r => r.1 != id).push (id, { entry with allocation := entry.allocation.setExtra tree }) }

/-- Machine state with its memory replaced (the only component the release loop mutates). -/
def stackPopWithMemory {K User : Type} (s : Miri.Interpreter.MachineHooks.State K User)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree K) :
    Miri.Interpreter.MachineHooks.State K User :=
  { s with machine := { s.machine with memory := mem } }

/-- Pure fold specification of the vendored frame-pop protector-release loop
(`MachineHooks.beforeStackPopWithEnsure`): every release runs against the SAME protector set `pt`;
the first failing release aborts with its (already committed) tree mutation. `none` = outside the
specified domain (a protected allocation that is not live, or an internal release-invariant
status). -/
def stackPopReleaseAll {K : Type} (pt : Miri.TreeBorrows.ProtectedTags) :
    List (Miri.Memory.AllocId × Miri.Memory.BorTag) →
    Miri.Memory.MemoryState Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree K →
    Option (Miri.Memory.MemoryState Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree K ×
      Option Miri.Interpreter.StepError)
  | [], mem => some (mem, none)
  | (id, tag) :: rest, mem =>
    match mem.live.find? (fun e => e.1 == id) with
    | none => none
    | some row =>
      let rel := row.2.allocation.extra.releaseProtector tag pt
      let mem' := stackPopWriteBack mem id row.2 rel.tree
      match stackPopReleaseErr rel.status with
      | some none => stackPopReleaseAll pt rest mem'
      | some (some err) => some (mem', some err)
      | none => none

private theorem stackPop_forIn_eq {K User : Type}
    (tracker : Miri.Interpreter.MachineHooks.BorrowState)
    (body : (Miri.Memory.AllocId × Miri.Memory.BorTag) → PUnit →
      Miri.Interpreter.MachineHooks.M K User (ForInStep PUnit))
    (hbodyOk : ∀ (id : Miri.Memory.AllocId) (tag : Miri.Memory.BorTag)
        (s : Miri.Interpreter.MachineHooks.State K User)
        (entry : Miri.Memory.LocalAllocation Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree K),
      s.machine.borrowTracker = some tracker →
      s.machine.memory.live.find? (fun e => e.1 == id) = some (id, entry) →
      stackPopReleaseErr
        (entry.allocation.extra.releaseProtector tag tracker.global.protectedTags).status =
          some none →
      body (id, tag) PUnit.unit s = .ok (.yield PUnit.unit)
        (stackPopWithMemory s (stackPopWriteBack s.machine.memory id entry
          (entry.allocation.extra.releaseProtector tag tracker.global.protectedTags).tree)))
    (hbodyErr : ∀ (id : Miri.Memory.AllocId) (tag : Miri.Memory.BorTag)
        (s : Miri.Interpreter.MachineHooks.State K User)
        (entry : Miri.Memory.LocalAllocation Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree K)
        (err : Miri.Interpreter.StepError),
      s.machine.borrowTracker = some tracker →
      s.machine.memory.live.find? (fun e => e.1 == id) = some (id, entry) →
      stackPopReleaseErr
        (entry.allocation.extra.releaseProtector tag tracker.global.protectedTags).status =
          some (some err) →
      body (id, tag) PUnit.unit s = .error err
        (stackPopWithMemory s (stackPopWriteBack s.machine.memory id entry
          (entry.allocation.extra.releaseProtector tag tracker.global.protectedTags).tree)))
    (xs : List (Miri.Memory.AllocId × Miri.Memory.BorTag)) :
    ∀ (s : Miri.Interpreter.MachineHooks.State K User)
      (mem' : Miri.Memory.MemoryState Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree K)
      (res : Option Miri.Interpreter.StepError),
      s.machine.borrowTracker = some tracker →
      stackPopReleaseAll tracker.global.protectedTags xs s.machine.memory = some (mem', res) →
      forIn (m := Miri.Interpreter.MachineHooks.M K User) xs PUnit.unit body s =
        match res with
        | none => .ok PUnit.unit (stackPopWithMemory s mem')
        | some err => .error err (stackPopWithMemory s mem') := by
  induction xs with
  | nil =>
    intro s mem' res _ hall
    simp only [stackPopReleaseAll, Option.some.injEq, Prod.mk.injEq] at hall
    obtain ⟨rfl, rfl⟩ := hall
    rfl
  | cons x rest ih =>
    intro s mem' res hs hall
    obtain ⟨id, tag⟩ := x
    simp only [stackPopReleaseAll] at hall
    cases hfind : s.machine.memory.live.find? (fun e => e.1 == id) with
    | none => rw [hfind] at hall; cases hall
    | some row =>
      rw [hfind] at hall
      obtain ⟨rid, entry⟩ := row
      have hrid : rid = id := by
        have hp := Array.find?_some hfind
        exact eq_of_beq (by simpa using hp)
      subst hrid
      simp only at hall
      rw [List.forIn_cons]
      cases hE : stackPopReleaseErr
          (entry.allocation.extra.releaseProtector tag tracker.global.protectedTags).status with
      | none => rw [hE] at hall; cases hall
      | some r =>
        rw [hE] at hall
        cases r with
        | none =>
          simp only at hall
          refine (est_bind_ok _ _ _ _ _ (hbodyOk rid tag s entry hs hfind hE)).trans ?_
          exact ih _ mem' res hs hall
        | some err =>
          simp only [Option.some.injEq, Prod.mk.injEq] at hall
          obtain ⟨rfl, rfl⟩ := hall
          exact est_bind_err _ _ _ _ _ (hbodyErr rid tag s entry err hs hfind hE)



private theorem stackPop_bind_forIn_eq {K User : Type}
    (tracker : Miri.Interpreter.MachineHooks.BorrowState)
    (body : (Miri.Memory.AllocId × Miri.Memory.BorTag) → PUnit →
      Miri.Interpreter.MachineHooks.M K User (ForInStep PUnit))
    (rest : PUnit → Miri.Interpreter.MachineHooks.M K User Unit)
    (hbodyOk : ∀ (id : Miri.Memory.AllocId) (tag : Miri.Memory.BorTag)
        (s : Miri.Interpreter.MachineHooks.State K User)
        (entry : Miri.Memory.LocalAllocation Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree K),
      s.machine.borrowTracker = some tracker →
      s.machine.memory.live.find? (fun e => e.1 == id) = some (id, entry) →
      stackPopReleaseErr
        (entry.allocation.extra.releaseProtector tag tracker.global.protectedTags).status =
          some none →
      body (id, tag) PUnit.unit s = .ok (.yield PUnit.unit)
        (stackPopWithMemory s (stackPopWriteBack s.machine.memory id entry
          (entry.allocation.extra.releaseProtector tag tracker.global.protectedTags).tree)))
    (hbodyErr : ∀ (id : Miri.Memory.AllocId) (tag : Miri.Memory.BorTag)
        (s : Miri.Interpreter.MachineHooks.State K User)
        (entry : Miri.Memory.LocalAllocation Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree K)
        (err : Miri.Interpreter.StepError),
      s.machine.borrowTracker = some tracker →
      s.machine.memory.live.find? (fun e => e.1 == id) = some (id, entry) →
      stackPopReleaseErr
        (entry.allocation.extra.releaseProtector tag tracker.global.protectedTags).status =
          some (some err) →
      body (id, tag) PUnit.unit s = .error err
        (stackPopWithMemory s (stackPopWriteBack s.machine.memory id entry
          (entry.allocation.extra.releaseProtector tag tracker.global.protectedTags).tree)))
    (xs : List (Miri.Memory.AllocId × Miri.Memory.BorTag))
    (s : Miri.Interpreter.MachineHooks.State K User)
    (mem' : Miri.Memory.MemoryState Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree K)
    (res : Option Miri.Interpreter.StepError)
    (hs : s.machine.borrowTracker = some tracker)
    (hall : stackPopReleaseAll tracker.global.protectedTags xs s.machine.memory =
      some (mem', res)) :
    (forIn (m := Miri.Interpreter.MachineHooks.M K User) xs PUnit.unit body >>= rest) s =
      match res with
      | none => rest PUnit.unit (stackPopWithMemory s mem')
      | some err => .error err (stackPopWithMemory s mem') := by
  have h := stackPop_forIn_eq tracker body hbodyOk hbodyErr xs s mem' res hs hall
  cases res with
  | none => exact est_bind_ok _ _ _ _ _ h
  | some err => exact est_bind_err _ _ _ _ _ h

/-- **N-ary frame pop: `MachineHooks.beforeStackPopWithEnsure` IS the release fold**, for a frame
with ARBITRARILY many protectors (generalizing the two-protector
`miri_beforeStackPopWithEnsure_retains_protectors_until_endCall`). Whenever the pure fold
`stackPopReleaseAll` is defined on the frame's protector list:
* every release in the frame runs against the SAME `tracker.global.protectedTags` — no protector is
  popped between releases (pinned-Miri batch order, `execFrameExitMiri`);
* the first failing release aborts the pop with its error, commits the partial tree mutations into
  `memory`, and leaves `borrowTracker` untouched (`end_call` never runs);
* `GlobalState.endCall` runs exactly once, only after ALL releases succeeded. -/
theorem miri_beforeStackPopWithEnsure_eq_releaseAll
    {K User : Type} [DecidableEq K]
    (st : Miri.Interpreter.MachineHooks.State K User)
    (tracker : Miri.Interpreter.MachineHooks.BorrowState)
    (frame : Miri.Interpreter.Frame Miri.Memory.Provenance Miri.Interpreter.LocalLayout
      Miri.Interpreter.MachineHooks.FrameExtra)
    (prots : Array (Miri.Memory.AllocId × Miri.Memory.BorTag))
    (htracker : st.machine.borrowTracker = some tracker)
    (hframe : st.stack.currentFrame? = some frame)
    (hbf : frame.extra.borrowTracker = some ⟨prots⟩) :
    ∀ (mem' : Miri.Memory.MemoryState Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree K)
      (res : Option Miri.Interpreter.StepError),
      stackPopReleaseAll tracker.global.protectedTags prots.toList st.machine.memory =
        some (mem', res) →
      Miri.Interpreter.MachineHooks.beforeStackPopWithEnsure (fun _ => pure ()) st =
        match res with
        | none => .ok () { st with machine := { st.machine with
            memory := mem'
            borrowTracker := some { tracker with global := tracker.global.endCall ⟨prots⟩ } } }
        | some err => .error err (stackPopWithMemory st mem') := by
  intro mem' res hall
  have hcur : Miri.Interpreter.MachineHooks.currentFrame st = .ok frame st := by
    unfold Miri.Interpreter.MachineHooks.currentFrame
    refine (est_bind_ok (get : Miri.Interpreter.MachineHooks.M K User _) _ st st st rfl).trans ?_
    rw [hframe]; rfl
  unfold Miri.Interpreter.MachineHooks.beforeStackPopWithEnsure
  refine (est_bind_ok (get : Miri.Interpreter.MachineHooks.M K User _) _ st st st rfl).trans ?_
  rw [htracker]
  simp only [Option.isSome_some, ↓reduceIte]
  refine (est_bind_ok _ _ _ _ _ hcur).trans ?_
  rw [hbf]
  dsimp only
  refine (est_bind_ok _ _ st st _ rfl).trans ?_
  rw [← Array.forIn_toList]
  refine (stackPop_bind_forIn_eq tracker _ _ ?_ ?_ prots.toList st mem' res htracker hall).trans ?_
  · intro id tag s entry hs hfind hE
    have hinfo : s.machine.memory.getAllocInfo id =
        .ok ⟨entry.allocation.byteSize, entry.allocation.align, .liveData,
             entry.allocation.mutability⟩ := by
      unfold Miri.Memory.MemoryState.getAllocInfo
      simp [hfind, pure, Except.pure]
    have hset := Miri.Memory.MemoryState.setLiveAllocation_of_find s.machine.memory id entry
      (entry.allocation.setExtra
        (entry.allocation.extra.releaseProtector tag tracker.global.protectedTags).tree) hfind
    have hstatus : (entry.allocation.extra.releaseProtector tag
        tracker.global.protectedTags).status = .Released := by
      cases hst : (entry.allocation.extra.releaseProtector tag
          tracker.global.protectedTags).status <;>
        simp [stackPopReleaseErr, hst] at hE
      rfl
    simp only [stackPopWithMemory, stackPopWriteBack, hs, hinfo, hfind, hset, hstatus,
      beq_self_eq_true, ↓reduceIte,
      get, getThe, MonadStateOf.get, EStateM.get,
      modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
      bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  · intro id tag s entry err hs hfind hE
    have hinfo : s.machine.memory.getAllocInfo id =
        .ok ⟨entry.allocation.byteSize, entry.allocation.align, .liveData,
             entry.allocation.mutability⟩ := by
      unfold Miri.Memory.MemoryState.getAllocInfo
      simp [hfind, pure, Except.pure]
    have hset := Miri.Memory.MemoryState.setLiveAllocation_of_find s.machine.memory id entry
      (entry.allocation.setExtra
        (entry.allocation.extra.releaseProtector tag tracker.global.protectedTags).tree) hfind
    cases hst : (entry.allocation.extra.releaseProtector tag
        tracker.global.protectedTags).status with
    | AccessFailure r status =>
      rw [hst] at hE
      simp only [stackPopReleaseErr, Option.some.injEq] at hE
      subst hE
      simp only [stackPopWithMemory, stackPopWriteBack, hs, hinfo, hfind, hset, hst,
        beq_self_eq_true, ↓reduceIte,
        get, getThe, MonadStateOf.get, EStateM.get,
        modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
        bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure,
        throw, throwThe, MonadExceptOf.throw, EStateM.throw]
    | Released => rw [hst] at hE; simp [stackPopReleaseErr] at hE
    | MissingTag _ => rw [hst] at hE; simp [stackPopReleaseErr] at hE
    | RangeMapFailure _ => rw [hst] at hE; simp [stackPopReleaseErr] at hE
    | LocationMapFailure _ => rw [hst] at hE; simp [stackPopReleaseErr] at hE
    | ExposureUpdateFailure _ => rw [hst] at hE; simp [stackPopReleaseErr] at hE
  · cases res with
    | some err => rfl
    | none =>
      simp only [stackPopWithMemory, htracker,
        get, getThe, MonadStateOf.get, EStateM.get, set, MonadStateOf.set, EStateM.set,
        bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]



private theorem find?_filter_push_self {α : Type} (xs : Array (Miri.Memory.AllocId × α))
    (id : Miri.Memory.AllocId) (v : α) :
    ((xs.filter fun r => r.1 != id).push (id, v)).find? (fun e => e.1 == id) = some (id, v) := by
  rw [← Array.find?_toList, Array.toList_push, List.find?_append, Array.toList_filter]
  have hnone : (xs.toList.filter fun r => r.1 != id).find? (fun e => e.1 == id) = none := by
    rw [List.find?_eq_none]
    intro x hx
    have hne := (List.mem_filter.mp hx).2
    simpa [bne] using hne
  rw [hnone]
  simp

/-- **Per-release simulation interface** between a vendored `BorrowTree` and a theory
`FnEntryBorrowWorld`: `R` is a protector-release simulation for the protector set `pt` on the tags
selected by `frameTag` when every vendored `BorrowTree.releaseProtector` step from `R`-related
states is matched by the theory's implicit protector-end access
(`execProtectorEndAccessFor protectorEndAccessIsWrite?`): both succeed into `R`-related states, or
both fail. -/
structure ProtectorReleaseSim (pt : Miri.TreeBorrows.ProtectedTags)
    (frameTag : Miri.Memory.BorTag → Prop) (tagOf : Miri.Memory.BorTag → Nat)
    (R : Miri.TreeBorrows.BorrowTree → FnEntryBorrowWorld → Prop) : Prop where
  step : ∀ tree w tag, frameTag tag → R tree w →
    match stackPopReleaseErr (tree.releaseProtector tag pt).status,
        execProtectorEndAccessFor protectorEndAccessIsWrite? w (tagOf tag) with
    | some none, .ok w' => R (tree.releaseProtector tag pt).tree w'
    | some (some _), .error _ => True
    | _, _ => False

/-- **Fold lifting**: a per-release simulation lifts to the whole multi-tag release fold of one
allocation, for ANY number of frame tags: `stackPopReleaseAll` and the theory's
`execProtectorEndAccesses` (no protector popped in between) either both succeed with `R`-related
final trees/worlds, or both fail. -/
theorem stackPopReleaseAll_simulates_execProtectorEndAccesses {K : Type}
    (pt : Miri.TreeBorrows.ProtectedTags)
    (frameTag : Miri.Memory.BorTag → Prop) (tagOf : Miri.Memory.BorTag → Nat)
    (R : Miri.TreeBorrows.BorrowTree → FnEntryBorrowWorld → Prop)
    (hsim : ProtectorReleaseSim pt frameTag tagOf R)
    (id : Miri.Memory.AllocId) (tags : List Miri.Memory.BorTag)
    (htags : ∀ t ∈ tags, frameTag t) :
    ∀ (mem : Miri.Memory.MemoryState Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree K)
      (entry : Miri.Memory.LocalAllocation Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree K)
      (w : FnEntryBorrowWorld),
      mem.live.find? (fun e => e.1 == id) = some (id, entry) →
      R entry.allocation.extra w →
      ∃ mem' res, stackPopReleaseAll pt (tags.map fun t => (id, t)) mem = some (mem', res) ∧
        match res, execProtectorEndAccesses protectorEndAccessIsWrite? w (tags.map tagOf) with
        | none, .ok w' =>
          ∃ entry', mem'.live.find? (fun e => e.1 == id) = some (id, entry') ∧
            R entry'.allocation.extra w'
        | some _, .error _ => True
        | _, _ => False := by
  induction tags with
  | nil =>
    intro mem entry w hfind hR
    exact ⟨mem, none, rfl, entry, hfind, hR⟩
  | cons t rest ih =>
    intro mem entry w hfind hR
    have hstep := hsim.step entry.allocation.extra w t (htags t List.mem_cons_self) hR
    have hunf : stackPopReleaseAll pt (((t :: rest).map fun t => (id, t))) mem =
        match stackPopReleaseErr (entry.allocation.extra.releaseProtector t pt).status with
        | some none => stackPopReleaseAll pt (rest.map fun t => (id, t))
            (stackPopWriteBack mem id entry (entry.allocation.extra.releaseProtector t pt).tree)
        | some (some err) => some (stackPopWriteBack mem id entry
            (entry.allocation.extra.releaseProtector t pt).tree, some err)
        | none => none := by
      simp only [List.map_cons, stackPopReleaseAll, hfind]
    have hexec : execProtectorEndAccesses protectorEndAccessIsWrite? w ((t :: rest).map tagOf) =
        match execProtectorEndAccessFor protectorEndAccessIsWrite? w (tagOf t) with
        | .error e => .error e
        | .ok w' => execProtectorEndAccesses protectorEndAccessIsWrite? w' (rest.map tagOf) := by
      simp only [List.map_cons, execProtectorEndAccesses]
      cases execProtectorEndAccessFor protectorEndAccessIsWrite? w (tagOf t) <;> rfl
    rw [hunf, hexec]
    generalize entry.allocation.extra.releaseProtector t pt = rel at hstep ⊢
    cases hE : stackPopReleaseErr rel.status with
    | none =>
      rw [hE] at hstep
      cases hX : execProtectorEndAccessFor protectorEndAccessIsWrite? w (tagOf t) with
      | error e => rw [hX] at hstep; exact False.elim hstep
      | ok w1 => rw [hX] at hstep; exact False.elim hstep
    | some r =>
      rw [hE] at hstep
      cases r with
      | none =>
        cases hX : execProtectorEndAccessFor protectorEndAccessIsWrite? w (tagOf t) with
        | error e => rw [hX] at hstep; exact False.elim hstep
        | ok w1 =>
          rw [hX] at hstep
          exact ih (fun t' ht' => htags t' (List.mem_cons_of_mem _ ht')) _ _ w1
            (find?_filter_push_self mem.live id _) hstep
      | some err =>
        cases hX : execProtectorEndAccessFor protectorEndAccessIsWrite? w (tagOf t) with
        | error e => exact ⟨_, _, rfl, trivial⟩
        | ok w1 => rw [hX] at hstep; exact False.elim hstep



/-- **Whole-frame relational simulation (`beforeStackPopWithEnsure` vs `execFrameExitMiri`)**: for
a frame protecting ANY number of tags of one live allocation, every per-release simulation `R`
(`ProtectorReleaseSim`) lifts to the complete vendored frame pop:
* both sides succeed — the final vendored tree is `R`-related to the theory world reached by all
  implicit accesses, the theory then pops every protector (`releaseProtectors`), and the vendored
  machine runs `end_call` exactly once; or
* both sides fail — and the vendored protector set is still the ORIGINAL one (no protector was
  popped before the failure).
Mixed outcomes are impossible. -/
theorem miri_beforeStackPopWithEnsure_simulates_execFrameExitMiri
    {K User : Type} [DecidableEq K]
    (st : Miri.Interpreter.MachineHooks.State K User)
    (tracker : Miri.Interpreter.MachineHooks.BorrowState)
    (frame : Miri.Interpreter.Frame Miri.Memory.Provenance Miri.Interpreter.LocalLayout
      Miri.Interpreter.MachineHooks.FrameExtra)
    (id : Miri.Memory.AllocId) (tags : List Miri.Memory.BorTag)
    (htracker : st.machine.borrowTracker = some tracker)
    (hframe : st.stack.currentFrame? = some frame)
    (hbf : frame.extra.borrowTracker = some ⟨(tags.map fun t => (id, t)).toArray⟩)
    (frameTag : Miri.Memory.BorTag → Prop) (tagOf protOf : Miri.Memory.BorTag → Nat)
    (R : Miri.TreeBorrows.BorrowTree → FnEntryBorrowWorld → Prop)
    (hsim : ProtectorReleaseSim tracker.global.protectedTags frameTag tagOf R)
    (htags : ∀ t ∈ tags, frameTag t)
    (entry : Miri.Memory.LocalAllocation Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree K)
    (hlive : st.machine.memory.live.find? (fun e => e.1 == id) = some (id, entry))
    (w : FnEntryBorrowWorld) (hR : R entry.allocation.extra w) :
    match Miri.Interpreter.MachineHooks.beforeStackPopWithEnsure (fun _ => pure ()) st,
        execFrameExitMiri w (tags.map fun t => (tagOf t, protOf t)) with
    | .ok () st', .ok w' =>
      st'.machine.borrowTracker = some { tracker with
        global := tracker.global.endCall ⟨(tags.map fun t => (id, t)).toArray⟩ } ∧
      ∃ entry' w'', st'.machine.memory.live.find? (fun e => e.1 == id) = some (id, entry') ∧
        R entry'.allocation.extra w'' ∧ w' = releaseProtectors w'' (tags.map protOf)
    | .error _ st', .error _ => st'.machine.borrowTracker = some tracker
    | _, _ => False := by
  obtain ⟨mem', res, hall, hmatch⟩ :=
    stackPopReleaseAll_simulates_execProtectorEndAccesses (K := K) tracker.global.protectedTags
      frameTag tagOf R hsim id tags htags st.machine.memory entry w hlive hR
  have hrun := miri_beforeStackPopWithEnsure_eq_releaseAll st tracker frame
    (tags.map fun t => (id, t)).toArray htracker hframe hbf mem' res hall
  have hexit : execFrameExitMiri w (tags.map fun t => (tagOf t, protOf t)) =
      match execProtectorEndAccesses protectorEndAccessIsWrite? w (tags.map tagOf) with
      | .error e => .error e
      | .ok w' => .ok (releaseProtectors w' (tags.map protOf)) := by
    unfold execFrameExitMiri
    rw [List.map_map, List.map_map]
    rfl
  rw [hrun, hexit]
  cases res with
  | none =>
    cases hX : execProtectorEndAccesses protectorEndAccessIsWrite? w (tags.map tagOf) with
    | error e => rw [hX] at hmatch; exact False.elim hmatch
    | ok w1 =>
      rw [hX] at hmatch
      obtain ⟨entry', hfind', hR'⟩ := hmatch
      exact ⟨rfl, entry', w1, hfind', hR', rfl⟩
  | some err =>
    cases hX : execProtectorEndAccesses protectorEndAccessIsWrite? w (tags.map tagOf) with
    | error e => exact htracker
    | ok w1 => rw [hX] at hmatch; exact False.elim hmatch

/-- The **no-implicit-access** simulation relation: every frame tag is present and unexposed in the
vendored tree with no accessed non-`Cell` location, and its theory node has no protector-end access
(`protectorEndAccessIsWrite? = none`). -/
def NoAccessReleaseRel (frameTag : Miri.Memory.BorTag → Prop) (tagOf : Miri.Memory.BorTag → Nat)
    (tree : Miri.TreeBorrows.BorrowTree) (w : FnEntryBorrowWorld) : Prop :=
  ∀ tag, frameTag tag →
    (∃ index node, tree.indexOfTag tag = some index ∧ tree.nodeAt index = some node ∧
      node.isExposed = false ∧
      ∀ pos (hvalid : pos < tree.locations.entries.size),
        match tree.locations.entries[pos].data.perms.get index with
        | none => True
        | some st => st.accessed = false ∨ st.permission.associatedAccess = none) ∧
    (∃ n, findNode? w.nodes (tagOf tag) = some n ∧ protectorEndAccessIsWrite? n = none)

/-- **A discharged simulation instance**: `NoAccessReleaseRel` IS a protector-release simulation
for every protector set (`miri_releaseProtector_noAccess_preserves_tree` on the vendored side,
`execProtectorEndAccessFor … = .ok w` on the theory side). Hence
`miri_beforeStackPopWithEnsure_simulates_execFrameExitMiri` applies unconditionally to every frame
whose protected tags were never accessed (or are `Cell`). -/
theorem noAccessReleaseSim (pt : Miri.TreeBorrows.ProtectedTags)
    (frameTag : Miri.Memory.BorTag → Prop) (tagOf : Miri.Memory.BorTag → Nat) :
    ProtectorReleaseSim pt frameTag tagOf (NoAccessReleaseRel frameTag tagOf) where
  step := by
    intro tree w tag ht hR
    obtain ⟨⟨index, node, hidx, hnode, hexp, hno⟩, n, hfn, hk⟩ := hR tag ht
    have hrel := miri_releaseProtector_noAccess_preserves_tree tree tag index node hidx hnode hexp
      hno pt
    have hexec : execProtectorEndAccessFor protectorEndAccessIsWrite? w (tagOf tag) = .ok w := by
      unfold execProtectorEndAccessFor
      rw [hfn]
      simp only [hk]
    rw [hrel, hexec]
    exact hR



/-- Single-protector frames: the release fold is exactly one classified release step. -/
theorem stackPopReleaseAll_singleton {K : Type} (pt : Miri.TreeBorrows.ProtectedTags)
    (id : Miri.Memory.AllocId) (tag : Miri.Memory.BorTag)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree K)
    (entry : Miri.Memory.LocalAllocation Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree K)
    (hfind : mem.live.find? (fun e => e.1 == id) = some (id, entry)) :
    stackPopReleaseAll pt [(id, tag)] mem =
      match stackPopReleaseErr (entry.allocation.extra.releaseProtector tag pt).status with
      | some none => some (stackPopWriteBack mem id entry
          (entry.allocation.extra.releaseProtector tag pt).tree, none)
      | some (some err) => some (stackPopWriteBack mem id entry
          (entry.allocation.extra.releaseProtector tag pt).tree, some err)
      | none => none := by
  simp only [stackPopReleaseAll, hfind]

/-! ### 2D.4 State- and choice-polymorphic vtable reads, invalid-vtable precedence through the
`validatePlace` driver, and the `annealValidityHooks` wide-pointer boundary -/

/-- World-backed `globalVTable` leaf: the `(concrete type, existential)` pair of a registered
`.vtable` global, `none` for every other allocation (dead, live local, non-vtable global, or a
`.vtable` global without registry metadata). -/
def worldGlobalVTable (w : KeyedAllocWorld) (reg : VTableRegistry)
    (dynCode : DynExistentialSpec → Nat) (id : Miri.Memory.AllocId) :
    Option (Miri.MIR.TyId × Nat) :=
  match w.findGlobal? (ofMiriAllocId id) with
  | some g =>
    if g.kind == .vtable then
      match reg.allocToData.get? (ofMiriAllocId id) with
      | some data => some (data.concreteTyCode, dynCode data.spec)
      | none => none
    else none
  | none => none

/-- **State/choice-polymorphic world reading**: the four vtable read leaves of `h` — for ANY state
type `S` and choice type `C` — answer at `(c, st)` exactly as the world `(w, reg)` does and leave
the state unchanged. `worldVTableReadHooks` (`Unit` state) and `worldVTableHooks` (any state)
satisfy it; `annealValidityHooks` does not (`annealValidityHooks_not_readsWorld`). -/
structure VTableReadsWorldAt {P S C : Type} (h : Miri.Interpreter.VTableReadHooks P S C)
    (c : C) (st : S) (w : KeyedAllocWorld) (reg : VTableRegistry)
    (resolve : Miri.Memory.Pointer (Option P) →
      Except Miri.Interpreter.VTablePointerError (Miri.Memory.AllocId × Miri.ABI.Size))
    (dynTable : Nat → DynExistentialSpec) (dynCode : DynExistentialSpec → Nat) : Prop where
  resolvePointer : ∀ ptr, h.resolvePointer c ptr st = .ok (resolve ptr) st
  globalVTable : ∀ id, h.globalVTable c id st = .ok (worldGlobalVTable w reg dynCode id) st
  predicates : ∀ n, h.predicates c n st = .ok (specPredicates (dynTable n)) st
  normalizePredicate : ∀ p, h.normalizePredicate c p st = .ok p.id st

/-- The `Unit`-state hooks `worldVTableReadHooks` read the world. -/
theorem worldVTableReadHooks_readsWorldAt (P : Type)
    (w : KeyedAllocWorld) (reg : VTableRegistry)
    (resolve : Miri.Memory.Pointer (Option P) →
      Except Miri.Interpreter.VTablePointerError (Miri.Memory.AllocId × Miri.ABI.Size))
    (dynTable : Nat → DynExistentialSpec) (dynCode : DynExistentialSpec → Nat)
    (layoutOfTy : Miri.MIR.TyId →
      Miri.Interpreter.RvalueM Unit (Miri.ABI.TyAndLayout Miri.MIR.TyId)) :
    VTableReadsWorldAt (worldVTableReadHooks P w reg resolve dynTable dynCode layoutOfTy) () ()
      w reg resolve dynTable dynCode where
  resolvePointer := fun _ => rfl
  globalVTable := fun id => by
    unfold worldVTableReadHooks worldGlobalVTable
    dsimp only
    cases w.findGlobal? (ofMiriAllocId id) with
    | none => rfl
    | some g =>
      cases hkind : (g.kind == .vtable) with
      | false => simp only [hkind, Bool.false_eq_true, ↓reduceIte]; rfl
      | true =>
        simp only [hkind, ↓reduceIte]
        cases reg.allocToData.get? (ofMiriAllocId id) <;> rfl
  predicates := fun _ => rfl
  normalizePredicate := fun _ => rfl

private theorem checkForTypeRead_zip_loop_eq_at {S : Type} (st : S)
    (step : Miri.Interpreter.VTablePredicate × Miri.Interpreter.VTablePredicate → Unit →
      Miri.Interpreter.RvalueM S (ForInStep Unit))
    (hstep : ∀ p u, step p u st =
      if p.1.id != p.2.id then .error (.undefinedBehavior "InvalidVTableTrait") st
      else .ok (.yield ()) st)
    (xs ys : List Miri.Interpreter.VTablePredicate) (hlen : xs.length = ys.length) :
    (forIn (m := Miri.Interpreter.RvalueM S) (xs.zip ys) () step) st =
      if xs.map (·.id) == ys.map (·.id) then .ok () st
      else .error (.undefinedBehavior "InvalidVTableTrait") st := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons _ _ => cases hlen
  | cons x xt ih =>
    cases ys with
    | nil => cases hlen
    | cons y yt =>
      have hlen' : xt.length = yt.length := Nat.succ.inj hlen
      simp only [List.zip_cons_cons, List.forIn_cons, List.map_cons]
      have hs := hstep (x, y) ()
      by_cases hid : x.id = y.id
      · have hbne : (x.id != y.id) = false := by simp [hid]
        have hbeq : (x.id :: xt.map (·.id) == y.id :: yt.map (·.id)) =
            (xt.map (·.id) == yt.map (·.id)) := by simp [hid]
        rw [hbne] at hs
        simp only [Bool.false_eq_true, ↓reduceIte] at hs
        rw [hbeq]
        refine (est_bind_ok _ _ _ _ _ hs).trans ?_
        exact ih yt hlen'
      · have hbne : (x.id != y.id) = true := bne_iff_ne.mpr hid
        have hbeq : (x.id :: xt.map (·.id) == y.id :: yt.map (·.id)) = false := by
          apply beq_false_of_ne
          intro hEq; exact hid (List.cons.inj hEq).1
        rw [hbne] at hs
        simp only [↓reduceIte] at hs
        rw [hbeq]
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact est_bind_err _ _ _ _ _ hs

/-- **State/choice-polymorphic `VTable.checkForTypeRead` correspondence**: generalizes
`miri_checkForTypeRead_eq_vtableMatchesExpectedSpec` from the concrete `Unit`-state
`specReadHooks` to ANY hooks (any state and choice types) whose `predicates` / `normalizePredicate`
leaves read the specification table at the current state. -/
theorem miri_checkForTypeRead_eq_vtableMatchesExpectedSpec_at {P S C : Type}
    (h : Miri.Interpreter.VTableReadHooks P S C) (c : C) (st : S)
    (dynTable : Nat → DynExistentialSpec) (actual expected : Nat)
    (hpred : ∀ n, h.predicates c n st = .ok (specPredicates (dynTable n)) st)
    (hnorm : ∀ p, h.normalizePredicate c p st = .ok p.id st)
    (ha : PredsKeyInjective (dynTable actual).effectivePreds)
    (he : PredsKeyInjective (dynTable expected).effectivePreds) :
    Miri.Interpreter.VTable.checkForTypeRead h c actual expected st =
      if vtableMatchesExpectedSpec (dynTable actual) (dynTable expected) then .ok () st
      else .error (.undefinedBehavior "InvalidVTableTrait") st := by
  let aList := miriSortedPredicates (specPredicates (dynTable actual))
  let eList := miriSortedPredicates (specPredicates (dynTable expected))
  have haId : aList.map (·.id) = canonicalNonAutoPredIds (dynTable actual).effectivePreds :=
    miri_sortedPredicates_map_id_eq_canonical (dynTable actual).effectivePreds ha
  have heId : eList.map (·.id) = canonicalNonAutoPredIds (dynTable expected).effectivePreds :=
    miri_sortedPredicates_map_id_eq_canonical (dynTable expected).effectivePreds he
  have hmatchEq : vtableMatchesExpectedSpec (dynTable actual) (dynTable expected) =
      (aList.map (·.id) == eList.map (·.id)) := by
    unfold vtableMatchesExpectedSpec; rw [haId, heId]
  rw [hmatchEq]
  unfold Miri.Interpreter.VTable.checkForTypeRead
  refine (est_bind_ok _ _ _ _ _ (hpred actual)).trans ?_
  refine (est_bind_ok _ _ _ _ _ (hpred expected)).trans ?_
  by_cases hlen : aList.length = eList.length
  · have hbne : (aList.length != eList.length) = false := by simp [hlen]
    rw [show (aList.length != eList.length) = false from hbne]
    rw [ite_f (by decide)]
    have hforEq :
        (forIn (m := Miri.Interpreter.RvalueM S) (aList.zip eList) () fun x _ =>
          match x with
          | (a, b) => do
            let a ← h.normalizePredicate c a
            let b ← h.normalizePredicate c b
            if a != b then
              (miri_etm_private% Miri.Interpreter.VTable Miri.Interpreter.VTable.ub) "InvalidVTableTrait"
            pure (.yield ())) st =
        if aList.map (·.id) == eList.map (·.id) then .ok () st
        else .error (.undefinedBehavior "InvalidVTableTrait") st := by
      refine checkForTypeRead_zip_loop_eq_at st _ ?_ aList eList hlen
      intro ⟨a, b⟩ u
      refine (est_bind_ok _ _ _ _ _ (hnorm a)).trans ?_
      refine (est_bind_ok _ _ _ _ _ (hnorm b)).trans ?_
      by_cases hne : a.id = b.id
      · have hbne' : (a.id != b.id) = false := by simp [hne]
        simp only [hbne', Bool.false_eq_true, ↓reduceIte]
        rfl
      · have hbne' : (a.id != b.id) = true := bne_iff_ne.mpr hne
        simp only [hbne', ↓reduceIte]
        rfl
    cases heq : (aList.map (·.id) == eList.map (·.id)) with
    | true =>
      rw [heq] at hforEq
      exact (est_bind_ok _ _ _ _ () hforEq).trans rfl
    | false =>
      rw [heq] at hforEq
      exact est_bind_err _ _ _ _ _ hforEq
  · have hbne : (aList.length != eList.length) = true := bne_iff_ne.mpr hlen
    have hbeq : (aList.map (·.id) == eList.map (·.id)) = false := by
      apply beq_false_of_ne
      intro hEq
      have hl := congrArg List.length hEq
      simp at hl
      exact hlen hl
    rw [show (aList.length != eList.length) = true from hbne, hbeq, ite_t (by decide)]
    exact est_bind_err _ _ _ _ _ rfl

/-- **State/choice-polymorphic `VTable.getPtrVTableTypeRead` vs `validateVTableHalf`**: generalizes
`miri_getPtrVTableTypeRead_eq_validateVTableHalf` to ANY world-reading hooks
(`VTableReadsWorldAt`), and weakens its global round-trip hypothesis `∀ s, dynTable (dynCode s) = s`
(an encoding of ALL existentials into `Nat`) to the round trip of the REGISTERED existentials only,
which finite tables satisfy (`wideDyn_invalidVTable_validatePlace_canary`). -/
theorem miri_getPtrVTableTypeRead_eq_validateVTableHalf_at {P S C : Type}
    (h : Miri.Interpreter.VTableReadHooks P S C) (c : C) (st : S)
    (w : KeyedAllocWorld) (reg : VTableRegistry)
    (resolve : Miri.Memory.Pointer (Option P) →
      Except Miri.Interpreter.VTablePointerError (Miri.Memory.AllocId × Miri.ABI.Size))
    (dynTable : Nat → DynExistentialSpec) (dynCode : DynExistentialSpec → Nat)
    (hw : VTableReadsWorldAt h c st w reg resolve dynTable dynCode)
    (ptr : Miri.Memory.Pointer (Option P)) (vptr : VTablePtrVal) (expected : Nat)
    (hdynRt : ∀ id data, reg.allocToData.get? id = some data →
      dynTable (dynCode data.spec) = data.spec)
    (hres : match vptr with
      | .null => resolve ptr = .error .danglingInteger
      | .danglingInt _ => resolve ptr = .error .danglingInteger
      | .provenanced id off => resolve ptr = .ok (toMiriAllocId id, Miri.ABI.Size.ofBytes off))
    (hinjExp : PredsKeyInjective (dynTable expected).effectivePreds)
    (hinjReg : ∀ id data, reg.allocToData.get? id = some data →
      PredsKeyInjective data.spec.effectivePreds) :
    Miri.Interpreter.VTable.getPtrVTableTypeRead h c ptr (some expected) st =
      match validateVTableHalf w reg vptr (dynTable expected) with
      | .ok data => .ok data.concreteTyCode st
      | .error (.invalidVTableTrait _ _) => .error (.undefinedBehavior "InvalidVTableTrait") st
      | .error _ => .error (.undefinedBehavior "InvalidVTablePointer") st := by
  unfold Miri.Interpreter.VTable.getPtrVTableTypeRead validateVTableHalf
  cases vptr with
  | null =>
    refine (est_bind_ok _ _ _ _ _ (hw.resolvePointer ptr)).trans ?_
    rw [hres]
    exact est_bind_err _ _ _ _ _ rfl
  | danglingInt addr =>
    refine (est_bind_ok _ _ _ _ _ (hw.resolvePointer ptr)).trans ?_
    rw [hres]
    exact est_bind_err _ _ _ _ _ rfl
  | provenanced id off =>
    refine (est_bind_ok _ _ _ _ _ (hw.resolvePointer ptr)).trans ?_
    rw [hres]
    refine (est_bind_ok _ _ _ _ _ rfl).trans ?_
    dsimp only
    have hzero : (Miri.ABI.Size.ofBytes off != Miri.ABI.Size.ZERO) = (off != 0) := by
      simp [Miri.ABI.Size.ofBytes, Miri.ABI.Size.ZERO, bne, BEq.beq]
    rw [hzero]
    cases hoff : (off != 0) with
    | true =>
      rw [ite_t (by decide)]
      exact est_bind_err _ _ _ _ _ rfl
    | false =>
      rw [ite_f (by decide)]
      have hgvEq : h.globalVTable c (toMiriAllocId id) st =
            .ok (match w.findGlobal? id with
              | some g =>
                if g.kind == .vtable then
                  match reg.allocToData.get? id with
                  | some data => some (data.concreteTyCode, dynCode data.spec)
                  | none => none
                else none
              | none => none) st := by
        rw [hw.globalVTable (toMiriAllocId id)]
        unfold worldGlobalVTable
        rw [ofMiriAllocId_toMiriAllocId]
      refine (est_bind_ok _ _ _ _ _ hgvEq).trans ?_
      cases hg : w.findGlobal? id with
      | none => rfl
      | some g =>
        cases hkind : (g.kind == .vtable) with
        | false =>
          have hne : (g.kind != .vtable) = true := by simp [bne, hkind]
          simp only [hkind, hne, Bool.false_eq_true, ↓reduceIte]; rfl
        | true =>
          have hne : (g.kind != .vtable) = false := by simp [bne, hkind]
          simp only [hkind, hne, Bool.false_eq_true, ↓reduceIte]
          cases hdata : reg.allocToData.get? id with
          | none => rfl
          | some data =>
            dsimp only
            have hchk := miri_checkForTypeRead_eq_vtableMatchesExpectedSpec_at h c st dynTable
              (dynCode data.spec) expected hw.predicates hw.normalizePredicate
              (by rw [hdynRt id data hdata]; exact hinjReg id data hdata) hinjExp
            rw [hdynRt id data hdata] at hchk
            cases hmatch : vtableMatchesExpectedSpec data.spec (dynTable expected) with
            | true =>
              rw [hmatch] at hchk
              simp only [↓reduceIte] at hchk
              exact (est_bind_ok _ _ _ _ () hchk).trans rfl
            | false =>
              rw [hmatch] at hchk
              simp only [Bool.false_eq_true, ↓reduceIte] at hchk
              exact est_bind_err _ _ _ _ _ hchk


/-- The vendored step error of a `validateVTableHalf` rejection: `InvalidVTableTrait` for a trait
mismatch, `InvalidVTablePointer` for every other vtable-half rejection. -/
def wideDynVTableErrToMiri : WideDynErr → Miri.Interpreter.StepError
  | .invalidVTableTrait _ _ => .undefinedBehavior "InvalidVTableTrait"
  | _ => .undefinedBehavior "InvalidVTablePointer"

/-- Every vtable-half rejection is reported as undefined behavior. -/
theorem wideDynVTableErrToMiri_isUB (e : WideDynErr) :
    isUndefinedBehavior (wideDynVTableErrToMiri e) = true := by
  cases e <;> rfl

/-- **Every invalid vtable form beats every data-pointer check on `ValidityVisitor.visit`**, for
ANY hooks whose vtable leaves read a world: if the vtable word of a safe wide `dyn` reference is
rejected by `validateVTableHalf` (null, dangling integer, dead allocation, wrong global kind, live
non-global allocation, trait mismatch, nonzero offset, missing metadata), `visit` fails with the
corresponding undefined behavior. No hypothesis constrains `sizeAndAlign`, `checkPointerAccess`,
`scalarMayBeNull`, `opsemInhabited`, `checkPointerAlignResult`, or the data pointer itself. -/
theorem visit_wideDyn_invalidVTable_precedes_dataPtr_at {P S C E F A Pad : Type}
    [Miri.Memory.PointerProvenance P] [DecidableEq P]
    (h : Miri.Interpreter.ValidityVisitor.Hooks P S C E F A Pad) (c : C)
    (fuel : Nat) (session : Miri.Interpreter.ValidityVisitor.Session P)
    (place : Miri.Interpreter.RuntimePlace P) (st : S)
    (mutBool : Bool) (expected : Nat)
    (ptrImm : Miri.Interpreter.RvalueImmTy P) (target : Miri.Interpreter.MPlaceTy P)
    (metaScalar : Miri.Memory.Scalar P) (vtPtr : Miri.Memory.Pointer (Option P))
    (w : KeyedAllocWorld) (reg : VTableRegistry)
    (resolve : Miri.Memory.Pointer (Option P) →
      Except Miri.Interpreter.VTablePointerError (Miri.Memory.AllocId × Miri.ABI.Size))
    (dynTable : Nat → DynExistentialSpec) (dynCode : DynExistentialSpec → Nat)
    (vptr : VTablePtrVal) (e : WideDynErr)
    (hreset : session.flags.resetProvenanceAndPadding = false)
    (hcl : h.classify c place.layout.ty st = .ok (.reference mutBool) st)
    (hrd : h.readImmediate c place .reference st = .ok ptrImm st)
    (hpt : h.ptrToPlace c ptrImm st = .ok target st)
    (htuns : target.layout.layout.isSized = false)
    (hmt : h.metadataTail c target.layout.ty st = .ok (.dynamic expected) st)
    (hunwrap : target.mplace.metadata.unwrapMeta = .ok metaScalar)
    (htoptr : metaScalar.toPointer h.target.base = .ok vtPtr)
    (hw : VTableReadsWorldAt h.vtable.readHooks c st w reg resolve dynTable dynCode)
    (hdynRt : ∀ id data, reg.allocToData.get? id = some data →
      dynTable (dynCode data.spec) = data.spec)
    (hres : match vptr with
      | .null => resolve vtPtr = .error .danglingInteger
      | .danglingInt _ => resolve vtPtr = .error .danglingInteger
      | .provenanced id off => resolve vtPtr = .ok (toMiriAllocId id, Miri.ABI.Size.ofBytes off))
    (hinjExp : PredsKeyInjective (dynTable expected).effectivePreds)
    (hinjReg : ∀ id data, reg.allocToData.get? id = some data →
      PredsKeyInjective data.spec.effectivePreds)
    (hbad : validateVTableHalf w reg vptr (dynTable expected) = .error e) :
    Miri.Interpreter.ValidityVisitor.visit h c (fuel + 1) session place st =
      .error (wideDynVTableErrToMiri e) st := by
  have hvt := miri_getPtrVTableTypeRead_eq_validateVTableHalf_at h.vtable.readHooks c st w reg
    resolve dynTable dynCode hw vtPtr vptr expected hdynRt hres hinjExp hinjReg
  rw [hbad] at hvt
  have hvt' : Miri.Interpreter.VTable.getPtrVTableType h.vtable c vtPtr (some expected) st =
      .error (wideDynVTableErrToMiri e) st := by
    cases e <;> exact hvt
  exact visit_wideDyn_checkSafe_vtableBeforeDataUB h c fuel session place st mutBool expected
    ptrImm target metaScalar vtPtr _ st hreset hcl hrd hpt htuns hmt hunwrap htoptr hvt'

/-- A root `visit` failure propagates through the `validatePlace` driver for BOTH
`recursive = false` and `recursive = true` (the recursive worklist loop is never entered), provided
`withGhostValidation` propagates that failure. -/
theorem validatePlace_error_of_root_visit_error {P S C E F A Pad : Type}
    [Miri.Memory.PointerProvenance P] [DecidableEq P]
    (h : Miri.Interpreter.ValidityVisitor.Hooks P S C E F A Pad) (c : C)
    (fuel : Nat) (place : Miri.Interpreter.RuntimePlace P) (recursive : Bool)
    (st st' : S) (name : String) (err : Miri.Interpreter.StepError)
    (hname : h.typeName c place.layout.ty st = .ok name st)
    (hghost : ∀ (x : Miri.Interpreter.ValidityVisitor.M S
        (Miri.Interpreter.ValidityVisitor.Session P)),
      x st = .error err st' → h.withGhostValidation x st = .error err st')
    (hvisit : Miri.Interpreter.ValidityVisitor.visit h c fuel
        { path := ⟨name, #[]⟩, flags := ⟨false, false⟩, ctfeMode := none,
          refTracking := if recursive then some .empty else none, dataBytes := none }
        place st = .error err st') :
    Miri.Interpreter.ValidityVisitor.validatePlace h c fuel place recursive false st =
      .error err st' := by
  unfold Miri.Interpreter.ValidityVisitor.validatePlace
  refine (est_bind_ok _ _ _ _ _ hname).trans ?_
  refine est_bind_err _ _ _ _ _ ?_
  apply hghost
  rw [ite_f (by decide)]
  exact est_bind_err _ _ _ _ _ hvisit


/-- **All invalid vtable forms beat every data-pointer check through the `validatePlace` driver,
for BOTH `recursive = false` and `recursive = true`** (`lean-miri#82`), on ANY hooks — any state and
choice types — whose vtable leaves read a world: the driver fails with the vtable undefined
behavior whatever the data-pointer leaves would report (including double-null `&dyn Trait`). -/
theorem validatePlace_wideDyn_invalidVTable_precedes_dataPtr_at {P S C E F A Pad : Type}
    [Miri.Memory.PointerProvenance P] [DecidableEq P]
    (h : Miri.Interpreter.ValidityVisitor.Hooks P S C E F A Pad) (c : C)
    (fuel : Nat) (place : Miri.Interpreter.RuntimePlace P) (recursive : Bool) (st : S)
    (name : String) (mutBool : Bool) (expected : Nat)
    (ptrImm : Miri.Interpreter.RvalueImmTy P) (target : Miri.Interpreter.MPlaceTy P)
    (metaScalar : Miri.Memory.Scalar P) (vtPtr : Miri.Memory.Pointer (Option P))
    (w : KeyedAllocWorld) (reg : VTableRegistry)
    (resolve : Miri.Memory.Pointer (Option P) →
      Except Miri.Interpreter.VTablePointerError (Miri.Memory.AllocId × Miri.ABI.Size))
    (dynTable : Nat → DynExistentialSpec) (dynCode : DynExistentialSpec → Nat)
    (vptr : VTablePtrVal) (e : WideDynErr)
    (hname : h.typeName c place.layout.ty st = .ok name st)
    (hghost : ∀ (x : Miri.Interpreter.ValidityVisitor.M S
        (Miri.Interpreter.ValidityVisitor.Session P)) err,
      x st = .error err st → h.withGhostValidation x st = .error err st)
    (hcl : h.classify c place.layout.ty st = .ok (.reference mutBool) st)
    (hrd : h.readImmediate c place .reference st = .ok ptrImm st)
    (hpt : h.ptrToPlace c ptrImm st = .ok target st)
    (htuns : target.layout.layout.isSized = false)
    (hmt : h.metadataTail c target.layout.ty st = .ok (.dynamic expected) st)
    (hunwrap : target.mplace.metadata.unwrapMeta = .ok metaScalar)
    (htoptr : metaScalar.toPointer h.target.base = .ok vtPtr)
    (hw : VTableReadsWorldAt h.vtable.readHooks c st w reg resolve dynTable dynCode)
    (hdynRt : ∀ id data, reg.allocToData.get? id = some data →
      dynTable (dynCode data.spec) = data.spec)
    (hres : match vptr with
      | .null => resolve vtPtr = .error .danglingInteger
      | .danglingInt _ => resolve vtPtr = .error .danglingInteger
      | .provenanced id off => resolve vtPtr = .ok (toMiriAllocId id, Miri.ABI.Size.ofBytes off))
    (hinjExp : PredsKeyInjective (dynTable expected).effectivePreds)
    (hinjReg : ∀ id data, reg.allocToData.get? id = some data →
      PredsKeyInjective data.spec.effectivePreds)
    (hbad : validateVTableHalf w reg vptr (dynTable expected) = .error e) :
    Miri.Interpreter.ValidityVisitor.validatePlace h c (fuel + 1) place recursive false st =
        .error (wideDynVTableErrToMiri e) st ∧
      isUndefinedBehavior (wideDynVTableErrToMiri e) = true := by
  refine ⟨?_, wideDynVTableErrToMiri_isUB e⟩
  exact validatePlace_error_of_root_visit_error h c (fuel + 1) place recursive st st name _ hname
    (fun x hx => hghost x _ hx)
    (visit_wideDyn_invalidVTable_precedes_dataPtr_at h c fuel _ place st mutBool expected ptrImm
      target metaScalar vtPtr w reg resolve dynTable dynCode vptr e rfl hcl hrd hpt htuns hmt
      hunwrap htoptr hw hdynRt hres hinjExp hinjReg hbad)

/-- **Every invalid vtable form** fails `validateVTableHalf` on ANY world: the six forms `null`,
`danglingInt`, `deadAlloc`, `wrongGlobalKind`, `nonGlobalLiveAlloc`, `traitMismatch`, plus the two
remaining vendored rejections (nonzero offset into a vtable, `.vtable` global without registry
metadata). -/
theorem validateVTableHalf_invalidForms (w : KeyedAllocWorld) (reg : VTableRegistry)
    (expected : DynExistentialSpec) :
    validateVTableHalf w reg .null expected = .error .invalidVTableNull ∧
    (∀ addr, validateVTableHalf w reg (.danglingInt addr) expected =
      .error (.invalidVTableDanglingInt addr)) ∧
    (∀ id d, w.findDead? id = some d → w.findGlobal? id = none →
      validateVTableHalf w reg (.provenanced id 0) expected =
        .error (.invalidVTableNotGlobalVTable id)) ∧
    (∀ id g, w.findGlobal? id = some g → g.kind ≠ .vtable →
      validateVTableHalf w reg (.provenanced id 0) expected =
        .error (.invalidVTableNotGlobalVTable id)) ∧
    (∀ id l, w.findLive? id = some l → w.findGlobal? id = none →
      validateVTableHalf w reg (.provenanced id 0) expected =
        .error (.invalidVTableNotGlobalVTable id)) ∧
    (∀ id g data, w.findGlobal? id = some g → g.kind = .vtable →
      reg.allocToData.get? id = some data →
      vtableMatchesExpectedSpec data.spec expected = false →
      validateVTableHalf w reg (.provenanced id 0) expected =
        .error (.invalidVTableTrait data.spec expected)) ∧
    (∀ id off, off ≠ 0 →
      validateVTableHalf w reg (.provenanced id off) expected =
        .error (.invalidVTableNonzeroOffset id off)) ∧
    (∀ id g, w.findGlobal? id = some g → g.kind = .vtable →
      reg.allocToData.get? id = none →
      validateVTableHalf w reg (.provenanced id 0) expected =
        .error (.invalidVTableMissingMetadata id)) := by
  refine ⟨rfl, fun _ => rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro id d _ hg
    simp [validateVTableHalf, hg]
  · intro id g hg hk
    have hne : (g.kind != .vtable) = true := bne_iff_ne.mpr hk
    simp [validateVTableHalf, hg, hne]
  · intro id l _ hg
    simp [validateVTableHalf, hg]
  · intro id g data hg hk hd hm
    have hne : (g.kind != .vtable) = false := by rw [hk]; rfl
    simp [validateVTableHalf, hg, hne, hd, hm]
  · intro id off hoff
    have hne : (off != 0) = true := bne_iff_ne.mpr hoff
    simp [validateVTableHalf, hne]
  · intro id g hg hk hd
    have hne : (g.kind != .vtable) = false := by rw [hk]; rfl
    simp [validateVTableHalf, hg, hne, hd]

/-- **`annealValidityHooks` cannot read ANY vtable**: `VTable.getPtrVTableType` through
`RefLM3_2.annealValidityHooks` fails closed with `StepError.unsupported` — never accepting and
never reporting undefined behavior — for every pointer and every expected trait. -/
theorem annealValidityHooks_getPtrVTableType_failClosed (layouts : Trusted.Rustc.V2026_06_01.Layout.LayoutTable)
    (c : Trusted.Rustc.V2026_06_01.MirAst.Ty)
    (ptr : Miri.Memory.Pointer (Option AnnealProv)) (expected : Option Nat)
    (m : AnnealStepState) :
    Miri.Interpreter.VTable.getPtrVTableType (annealValidityHooks layouts).vtable c ptr expected m =
        .error (.unsupported "validity vtable: resolvePointer") m ∧
      isUndefinedBehavior (.unsupported "validity vtable: resolvePointer") = false :=
  ⟨rfl, rfl⟩

/-- **Exact boundary**: `annealValidityHooks` reads NO vtable world, so the vtable-precedence
theorems above apply to it only through an extension that replaces its fail-closed wide-pointer
leaves (`annealWideDynHooks`). -/
theorem annealValidityHooks_not_readsWorld (layouts : Trusted.Rustc.V2026_06_01.Layout.LayoutTable)
    (c : Trusted.Rustc.V2026_06_01.MirAst.Ty) (m : AnnealStepState)
    (w : KeyedAllocWorld) (reg : VTableRegistry)
    (resolve : Miri.Memory.Pointer (Option AnnealProv) →
      Except Miri.Interpreter.VTablePointerError (Miri.Memory.AllocId × Miri.ABI.Size))
    (dynTable : Nat → DynExistentialSpec) (dynCode : DynExistentialSpec → Nat) :
    ¬ VTableReadsWorldAt (annealValidityHooks layouts).vtable.readHooks c m w reg resolve
      dynTable dynCode := by
  intro hw
  have h := hw.predicates 0
  cases h

/-- Positive direction of the precedence: once the vtable half of a safe wide `dyn` reference is
ACCEPTED, `visit` proceeds to the first data-pointer leaf (`sizeAndAlign`) and propagates its
failure. -/
theorem visit_wideDyn_validVTable_reaches_sizeAndAlign {P S C E F A Pad : Type}
    [Miri.Memory.PointerProvenance P] [DecidableEq P]
    (h : Miri.Interpreter.ValidityVisitor.Hooks P S C E F A Pad) (c : C)
    (fuel : Nat) (session : Miri.Interpreter.ValidityVisitor.Session P)
    (place : Miri.Interpreter.RuntimePlace P) (st st' : S)
    (mutBool : Bool) (expected : Nat)
    (ptrImm : Miri.Interpreter.RvalueImmTy P) (target : Miri.Interpreter.MPlaceTy P)
    (metaScalar : Miri.Memory.Scalar P) (vtPtr : Miri.Memory.Pointer (Option P))
    (ty : Miri.MIR.TyId) (err : Miri.Interpreter.StepError)
    (hreset : session.flags.resetProvenanceAndPadding = false)
    (hcl : h.classify c place.layout.ty st = .ok (.reference mutBool) st)
    (hrd : h.readImmediate c place .reference st = .ok ptrImm st)
    (hpt : h.ptrToPlace c ptrImm st = .ok target st)
    (htuns : target.layout.layout.isSized = false)
    (hmt : h.metadataTail c target.layout.ty st = .ok (.dynamic expected) st)
    (hunwrap : target.mplace.metadata.unwrapMeta = .ok metaScalar)
    (htoptr : metaScalar.toPointer h.target.base = .ok vtPtr)
    (hvtOk : Miri.Interpreter.VTable.getPtrVTableType h.vtable c vtPtr (some expected) st =
      .ok ty st)
    (hsa : h.sizeAndAlign c target st = .error err st') :
    Miri.Interpreter.ValidityVisitor.visit h c (fuel + 1) session place st = .error err st' := by
  have hcm := checkMetadata_dynamic_eq h c target st expected metaScalar vtPtr hmt hunwrap htoptr
  rw [hvtOk] at hcm
  unfold Miri.Interpreter.ValidityVisitor.visit
  refine (est_bind_ok _ _ _ _ _ hcl).trans ?_
  refine est_bind_err _ _ _ _ _ ?_
  with_unfolding_all
    refine est_bind_err _ _ _ _ _ ?_
    refine (est_bind_ok _ _ _ _ _ hrd).trans ?_
    rw [hreset, ite_f (by decide)]
    dsimp only
    refine (est_bind_ok _ _ _ _ _ hpt).trans ?_
    rw [htuns, Bool.not_false, ite_t (by decide)]
    refine (est_bind_ok _ _ _ _ _ hcm).trans ?_
    exact est_bind_err _ _ _ _ _ hsa

/-- A failing `metadataTail` leaf aborts a safe reference to an unsized pointee BEFORE any vtable
or data-pointer check. -/
theorem visit_unsizedRef_metadataTail_error {P S C E F A Pad : Type}
    [Miri.Memory.PointerProvenance P] [DecidableEq P]
    (h : Miri.Interpreter.ValidityVisitor.Hooks P S C E F A Pad) (c : C)
    (fuel : Nat) (session : Miri.Interpreter.ValidityVisitor.Session P)
    (place : Miri.Interpreter.RuntimePlace P) (st st' : S)
    (mutBool : Bool) (ptrImm : Miri.Interpreter.RvalueImmTy P)
    (target : Miri.Interpreter.MPlaceTy P) (err : Miri.Interpreter.StepError)
    (hreset : session.flags.resetProvenanceAndPadding = false)
    (hcl : h.classify c place.layout.ty st = .ok (.reference mutBool) st)
    (hrd : h.readImmediate c place .reference st = .ok ptrImm st)
    (hpt : h.ptrToPlace c ptrImm st = .ok target st)
    (htuns : target.layout.layout.isSized = false)
    (hmt : h.metadataTail c target.layout.ty st = .error err st') :
    Miri.Interpreter.ValidityVisitor.visit h c (fuel + 1) session place st = .error err st' := by
  have hcm : (miri_etm_private% Miri.Interpreter.ValidityVisitor
      Miri.Interpreter.ValidityVisitor.checkMetadata) h c target st = .error err st' := by
    with_unfolding_all
      exact est_bind_err _ _ _ _ _ hmt
  unfold Miri.Interpreter.ValidityVisitor.visit
  refine (est_bind_ok _ _ _ _ _ hcl).trans ?_
  refine est_bind_err _ _ _ _ _ ?_
  with_unfolding_all
    refine est_bind_err _ _ _ _ _ ?_
    refine (est_bind_ok _ _ _ _ _ hrd).trans ?_
    rw [hreset, ite_f (by decide)]
    dsimp only
    refine (est_bind_ok _ _ _ _ _ hpt).trans ?_
    rw [htuns, Bool.not_false, ite_t (by decide)]
    exact est_bind_err _ _ _ _ _ hcm

/-- **`annealValidityHooks` fail-closed boundary for safe references to unsized pointees**, for
BOTH `recursive = false` and `recursive = true`: whenever its `ptrToPlace` yields an unsized
pointee layout, `validatePlace` fails with `StepError.unsupported "validity metadataTail"`, which
is NOT undefined behavior. `annealValidityHooks` therefore never reproduces a wide-`dyn` verdict
of the theory — neither an acceptance nor a UB rejection. -/
theorem annealValidityHooks_unsizedRef_validatePlace_failClosed
    (layouts : Trusted.Rustc.V2026_06_01.Layout.LayoutTable)
    (c : Trusted.Rustc.V2026_06_01.MirAst.Ty) (fuel : Nat)
    (place : Miri.Interpreter.RuntimePlace AnnealProv) (recursive : Bool) (m : AnnealStepState)
    (mutBool : Bool) (ptrImm : Miri.Interpreter.RvalueImmTy AnnealProv)
    (target : Miri.Interpreter.MPlaceTy AnnealProv)
    (hcl : (annealValidityHooks layouts).classify c place.layout.ty m = .ok (.reference mutBool) m)
    (hrd : (annealValidityHooks layouts).readImmediate c place .reference m = .ok ptrImm m)
    (hpt : (annealValidityHooks layouts).ptrToPlace c ptrImm m = .ok target m)
    (htuns : target.layout.layout.isSized = false) :
    Miri.Interpreter.ValidityVisitor.validatePlace (annealValidityHooks layouts) c (fuel + 1)
        place recursive false m = .error (.unsupported "validity metadataTail") m ∧
      isUndefinedBehavior (.unsupported "validity metadataTail") = false := by
  refine ⟨?_, rfl⟩
  exact validatePlace_error_of_root_visit_error (annealValidityHooks layouts) c (fuel + 1) place
    recursive m m "" _ rfl (fun _ hx => hx)
    (visit_unsizedRef_metadataTail_error (annealValidityHooks layouts) c fuel _ place m m mutBool
      ptrImm target _ rfl hcl hrd hpt htuns rfl)


/-- State/choice-polymorphic world-backed `VTableHooks`: the four read leaves read the world for
ANY state and choice types, and every other leaf fails closed. -/
def worldVTableHooks (P S C : Type) (w : KeyedAllocWorld) (reg : VTableRegistry)
    (resolve : Miri.Memory.Pointer (Option P) →
      Except Miri.Interpreter.VTablePointerError (Miri.Memory.AllocId × Miri.ABI.Size))
    (dynTable : Nat → DynExistentialSpec) (dynCode : DynExistentialSpec → Nat) :
    Miri.Interpreter.VTableHooks P S C Unit Unit where
  target := annealTargetDataLayout
  isDynamic := fun _ _ => throw (.unsupported "worldVTableHooks: isDynamic")
  memoryOffset := fun _ _ _ _ _ => throw (.unsupported "worldVTableHooks: memoryOffset")
  resolvePointer := fun _ ptr => pure (resolve ptr)
  globalVTable := fun _ id => pure (worldGlobalVTable w reg dynCode id)
  globalFunction := fun _ _ => throw (.unsupported "worldVTableHooks: globalFunction")
  predicates := fun _ n => pure (specPredicates (dynTable n))
  normalizePredicate := fun _ p => pure p.id
  layoutOf := fun _ _ => throw (.unsupported "worldVTableHooks: layoutOf")
  eraseAndAnonymize := fun _ _ _ => throw (.unsupported "worldVTableHooks: eraseAndAnonymize")
  ensureMonomorphicType := fun _ _ => throw (.unsupported "worldVTableHooks: ensureMonomorphicType")
  ensureMonomorphicDyn := fun _ _ => throw (.unsupported "worldVTableHooks: ensureMonomorphicDyn")
  globalSalt := fun _ => throw (.unsupported "worldVTableHooks: globalSalt")
  reserveVTable := fun _ _ _ _ => throw (.unsupported "worldVTableHooks: reserveVTable")
  globalRootPointer := fun _ _ => throw (.unsupported "worldVTableHooks: globalRootPointer")
  entries := fun _ _ _ => throw (.unsupported "worldVTableHooks: entries")
  assertVirtualInstanceMatches := fun _ _ _ _ _ =>
    throw (.unsupported "worldVTableHooks: assertVirtualInstanceMatches")

/-- `worldVTableHooks` reads the world at every state and choice, so `VTableReadsWorldAt` is
satisfiable at arbitrary state and choice types. -/
theorem worldVTableHooks_readsWorldAt (P S C : Type) (w : KeyedAllocWorld) (reg : VTableRegistry)
    (resolve : Miri.Memory.Pointer (Option P) →
      Except Miri.Interpreter.VTablePointerError (Miri.Memory.AllocId × Miri.ABI.Size))
    (dynTable : Nat → DynExistentialSpec) (dynCode : DynExistentialSpec → Nat) (c : C) (st : S) :
    VTableReadsWorldAt (worldVTableHooks P S C w reg resolve dynTable dynCode).readHooks c st
      w reg resolve dynTable dynCode :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

/-- `RefLM3_2.annealValidityHooks` with its fail-closed wide-pointer leaves (`vtable`,
`metadataTail`) and its pointer-reading leaves (`classify`, `readImmediate`, `ptrToPlace`)
replaced; every data-pointer leaf (`checkPointerAccess`, `scalarMayBeNull`, `opsemInhabited`,
`checkPointerAlignResult`, `sizeAndAlign`), `typeName`, and `withGhostValidation` remain those of
`annealValidityHooks`. -/
def annealWideDynHooks (layouts : Trusted.Rustc.V2026_06_01.Layout.LayoutTable)
    (vt : Miri.Interpreter.VTableHooks AnnealProv AnnealStepState
      Trusted.Rustc.V2026_06_01.MirAst.Ty Unit Unit)
    (ptrImm : Miri.Interpreter.RvalueImmTy AnnealProv)
    (target : Miri.Interpreter.MPlaceTy AnnealProv) (expected : Nat) :
    Miri.Interpreter.ValidityVisitor.Hooks AnnealProv AnnealStepState
      Trusted.Rustc.V2026_06_01.MirAst.Ty Unit Unit Unit Unit :=
  { annealValidityHooks layouts with
    vtable := vt
    classify := fun _ _ => pure (.reference false)
    readImmediate := fun _ _ _ => pure ptrImm
    ptrToPlace := fun _ _ => pure target
    metadataTail := fun _ _ => pure (.dynamic expected) }

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

/-- Real vendored `Miri.Memory.MemoryState` lifecycle canary (`lean-miri#73`):
reserving `AllocId 1` from `MemoryState.empty`, observing `isAllocLive = true` for a live stack
allocation both on the vendored state (`memoryState_isAllocLive_eq_keyed`) and on its keyed world,
checking `deallocErrOfMiri_toMiri` unconditionally on `.layoutMismatch`, and observing
`isAllocLive = false` on the empty state. -/
theorem memoryState_lifecycle_canary :
    let proj : RowProjection Miri.Memory.Provenance Unit Unit :=
      ⟨fun _ => .heap, fun _ => [], fun _ => []⟩
    let id1 : Miri.Memory.AllocId := ⟨1, by decide⟩
    let mem0 : Miri.Memory.MemoryState Miri.Memory.Provenance Unit Unit :=
      Miri.Memory.MemoryState.empty
    let mem1 : Miri.Memory.MemoryState Miri.Memory.Provenance Unit Unit :=
      { mem0 with live := #[(id1, ⟨.stack, baseRetagAllocation⟩)] }
    mem0.reserveAllocId.2 = .ok id1 ∧
    mem1.isAllocLive id1 = true ∧
    (memoryStateToKeyed proj mem1).isAllocLive (ofMiriAllocId id1) = true ∧
    deallocErrOfMiri (deallocErrToMiri (.layoutMismatch (ofMiriAllocId id1) 4 2 8 2)) =
      some (.layoutMismatch (ofMiriAllocId id1) 4 2 8 2) ∧
    (Miri.Memory.MemoryState.empty (Prov := Unit) (Extra := Unit) (MachineKind := Unit)
      |>.isAllocLive id1) = false := by
  intro proj id1 mem0 mem1
  have hmem0Keyed : memoryStateToKeyed proj mem0 = KeyedAllocWorld.empty := by
    apply KeyedAllocWorld.ext <;> first | rfl | (intro _; rfl)
  have hres : mem0.reserveAllocId.2 = .ok id1 := by
    have hb : ((mem0.reserveAllocId.2).map ofMiriAllocId).mapError allocIdErrOfMiri =
        (memoryStateToKeyed proj mem0).reserveAllocId.2 :=
      (memoryState_reserveAllocId_eq_keyed proj mem0 rfl).2
    rw [hmem0Keyed] at hb
    have hk : KeyedAllocWorld.empty.reserveAllocId.2 = .ok (ofMiriAllocId id1) := rfl
    rw [hk] at hb
    cases hm : mem0.reserveAllocId.2 with
    | error e => rw [hm] at hb; cases hb
    | ok a =>
      rw [hm] at hb
      simp only [Except.map, Except.mapError] at hb
      injection hb with hEq
      exact congrArg Except.ok (ofMiriAllocId_injective hEq)
  have hlive : mem1.isAllocLive id1 = true := by
    rw [memoryState_isAllocLive_eq_keyed proj mem1 ⟨rfl, rfl, rfl⟩]
    change ((memoryStateToRows mem1).toKeyed proj).isAllocLive (ofMiriAllocId id1) = true
    rw [toKeyed_isAllocLive]; rfl
  have hklive : (memoryStateToKeyed proj mem1).isAllocLive (ofMiriAllocId id1) = true := by
    change ((memoryStateToRows mem1).toKeyed proj).isAllocLive (ofMiriAllocId id1) = true
    rw [toKeyed_isAllocLive]; rfl
  have hempty : (Miri.Memory.MemoryState.empty (Prov := Unit) (Extra := Unit)
      (MachineKind := Unit)).isAllocLive id1 = false := by
    have h0 := memoryState_isAllocLive_eq_keyed
      (⟨fun _ => .heap, fun _ => [], fun _ => []⟩ : RowProjection Unit Unit Unit)
      (Miri.Memory.MemoryState.empty (Prov := Unit) (Extra := Unit) (MachineKind := Unit))
      ⟨rfl, rfl, rfl⟩ id1
    rw [h0]; rfl
  exact ⟨hres, hlive, hklive, deallocErrOfMiri_toMiri _, hempty⟩

/-- Choice-free traversal fuel-closure & `.SkipChildrenOfAccessed` canary
(`lean-miri#74`): on `canaryTreeNodes`, `foreignPostorderTags` agrees at fuel
`nodes.length` and `nodes.length + 1`, and `.SkipChildrenOfAccessed` visits
ancestors `[1, 0]` plus foreign sibling `2` while excluding strict descendant `3`. -/
theorem traversal_skipChildren_canary :
    let tree := traversalTreeOfNodes canaryTreeNodes
    foreignPostorderTags (childTagsInListOrder canaryTreeNodes) (fun _ => false) canaryTreeNodes.length 1 =
      foreignPostorderTags (childTagsInListOrder canaryTreeNodes) (fun _ => false) (canaryTreeNodes.length + 1) 1 ∧
    (Miri.TreeBorrows.Tree.TraversalTree.traverse tree 1 .SkipChildrenOfAccessed []).2 =
      [⟨1, .LocalAccess⟩, ⟨0, .LocalAccess⟩, ⟨2, .ForeignAccess⟩] ∧
    isStrictDescendantOf canaryTreeNodes 1 ⟨3, some 1, .reservedFrz false, 0, 4, none, true⟩ = true := by
  intro tree
  exact ⟨by decide, by decide, by decide⟩

/-- Real vendored `Miri.TreeBorrows.BorrowTree.releaseProtector` canary
(`lean-miri#74`): missing tag returns `.MissingTag`, and the 4-node
`.SkipChildrenOfAccessed` configuration separates protected-descendant
acceptance (Miri) from protected-sibling UB (`Miri` vs sequential `MiniRust`). -/
theorem releaseProtector_canary :
    let t1 : Miri.Memory.BorTag := ⟨1, by decide⟩
    let t2 : Miri.Memory.BorTag := ⟨2, by decide⟩
    let t3 : Miri.Memory.BorTag := ⟨3, by decide⟩
    let t4 : Miri.Memory.BorTag := ⟨4, by decide⟩
    let t9 : Miri.Memory.BorTag := ⟨9, by decide⟩
    let treeMissing := Miri.TreeBorrows.BorrowTree.new t1 Miri.ABI.Size.ZERO
    (treeMissing.releaseProtector t9 ⟨#[]⟩).status = .MissingTag t9 ∧
    (releaseProtectorSimTree.releaseProtector t2
      ⟨#[(t2, .StrongProtector), (t4, .StrongProtector)]⟩).status = .Released ∧
    (match (releaseProtectorSimTree.releaseProtector t2
      ⟨#[(t2, .StrongProtector), (t3, .StrongProtector)]⟩).status with
      | .AccessFailure _ _ => true | _ => false) = true := by
  intro t1 t2 t3 t4 t9 treeMissing
  have hmiss : (treeMissing.releaseProtector t9 ⟨#[]⟩).status = .MissingTag t9 :=
    congrArg Miri.TreeBorrows.BorrowTree.ProtectorReleaseResult.status
      (miri_releaseProtector_missingTag treeMissing t9 ⟨#[]⟩ (by decide))
  have hsep := miri_releaseProtector_skipChildren_and_siblingConflict
  exact ⟨hmiss, hsep.1, hsep.2.2.2.1⟩

/-- Choice-free general VTable read & `stableKey`-collision boundary canary
(`lean-miri#75`): checks `worldVTableReadHooks` on valid offset-0 vtable
(`dyn Trait7 + Send` vs `dyn Trait7`), non-zero offset (`InvalidVTablePointer`),
mismatched principal (`InvalidVTableTrait`), and the exact `stableKey`-collision
separation witness. -/
theorem vtable_general_canary :
    let id1 : MiriAllocId := ⟨1, by decide⟩
    let spec7Send : DynExistentialSpec := canarySpecTable 2
    let vtData : VTableData := ⟨.uint 8, 42, none, 16, 3, spec7Send, []⟩
    let w : KeyedAllocWorld :=
      KeyedAllocWorld.empty.registerGlobal id1 ⟨.vtable, 24, 3, .not, []⟩
    let reg : VTableRegistry :=
      { VTableRegistry.empty with allocToData := VTableRegistry.empty.allocToData.insert id1 vtData }
    let dynCode : DynExistentialSpec → Nat := fun s =>
      if s == canarySpecTable 0 then 0
      else if s == canarySpecTable 1 then 1
      else if s == canarySpecTable 2 then 2
      else if s == canarySpecTable 3 then 3
      else 4
    let resOk : Miri.Memory.Pointer (Option Unit) →
        Except Miri.Interpreter.VTablePointerError (Miri.Memory.AllocId × Miri.ABI.Size) :=
      fun p => .ok (toMiriAllocId id1, p.offset)
    let layOf : Miri.MIR.TyId → Miri.Interpreter.RvalueM Unit (Miri.ABI.TyAndLayout Miri.MIR.TyId) :=
      fun _ => throw (.invalidProgram "")
    let hooks := worldVTableReadHooks Unit w reg resOk canarySpecTable dynCode layOf
    Miri.Interpreter.VTable.getPtrVTableTypeRead hooks () ⟨⟨0⟩, some ()⟩ (some 3) () = .ok 42 () ∧
    Miri.Interpreter.VTable.getPtrVTableTypeRead hooks () ⟨⟨8⟩, some ()⟩ (some 3) () =
      .error (.undefinedBehavior "InvalidVTablePointer") () ∧
    Miri.Interpreter.VTable.getPtrVTableTypeRead hooks () ⟨⟨0⟩, some ()⟩ (some 4) () =
      .error (.undefinedBehavior "InvalidVTableTrait") () ∧
    miriVTableTraitCheckOk (fun n =>
      if n == 0 then ⟨some 1, AutoTraitSet.empty, [⟨1, 50, false⟩, ⟨2, 50, false⟩]⟩
      else ⟨some 1, AutoTraitSet.empty, [⟨2, 50, false⟩, ⟨1, 50, false⟩]⟩) 0 1 = false := by
  intro id1 spec7Send vtData w reg dynCode resOk layOf hooks
  have hfg : w.findGlobal? id1 = some ⟨.vtable, 24, 3, .not, []⟩ := by
    unfold w KeyedAllocWorld.registerGlobal KeyedAllocWorld.findGlobal?
    dsimp only
    exact ExtTreeMap0.get?_insert_self _ id1 _
  have hreg : reg.allocToData.get? id1 = some vtData := by
    unfold reg
    dsimp only
    exact ExtTreeMap0.get?_insert_self _ id1 _
  have hg : hooks.globalVTable () (toMiriAllocId id1) () = .ok (some (42, 2)) () := by
    change EStateM.Result.ok (match w.findGlobal? (ofMiriAllocId (toMiriAllocId id1)) with
      | some g => if g.kind == GlobalAllocKind.vtable then
          match reg.allocToData.get? (ofMiriAllocId (toMiriAllocId id1)) with
          | some d => some (d.concreteTyCode, dynCode d.spec) | none => none
        else none
      | none => none) () = _
    rw [ofMiriAllocId_toMiriAllocId, hfg, hreg]; rfl
  have hok : Miri.Interpreter.VTable.getPtrVTableTypeRead hooks () ⟨⟨0⟩, some ()⟩ (some 3) () =
      .ok 42 () := by
    unfold Miri.Interpreter.VTable.getPtrVTableTypeRead
    with_unfolding_all
      refine (est_bind_ok _ _ () () (Except.ok (toMiriAllocId id1, Miri.ABI.Size.ofBytes 0)) rfl).trans ?_
      refine (est_bind_ok _ _ () () (toMiriAllocId id1, Miri.ABI.Size.ofBytes 0) rfl).trans ?_
      dsimp only
      rw [ite_f (by decide)]
      refine (est_bind_ok _ _ () () (some (42, 2)) hg).trans ?_
      have hchk : Miri.Interpreter.VTable.checkForTypeRead hooks () 2 3 () = .ok () () := rfl
      exact (est_bind_ok _ _ () () () hchk).trans rfl
  have hbadOff : Miri.Interpreter.VTable.getPtrVTableTypeRead hooks () ⟨⟨8⟩, some ()⟩ (some 3) () =
      .error (.undefinedBehavior "InvalidVTablePointer") () := by
    unfold Miri.Interpreter.VTable.getPtrVTableTypeRead
    with_unfolding_all
      refine (est_bind_ok _ _ () () (Except.ok (toMiriAllocId id1, Miri.ABI.Size.ofBytes 8)) rfl).trans ?_
      refine (est_bind_ok _ _ () () (toMiriAllocId id1, Miri.ABI.Size.ofBytes 8) rfl).trans ?_
      dsimp only
      rw [ite_t (by decide)]
      exact est_bind_err _ _ () () _ rfl
  have hbadTr : Miri.Interpreter.VTable.getPtrVTableTypeRead hooks () ⟨⟨0⟩, some ()⟩ (some 4) () =
      .error (.undefinedBehavior "InvalidVTableTrait") () := by
    unfold Miri.Interpreter.VTable.getPtrVTableTypeRead
    with_unfolding_all
      refine (est_bind_ok _ _ () () (Except.ok (toMiriAllocId id1, Miri.ABI.Size.ofBytes 0)) rfl).trans ?_
      refine (est_bind_ok _ _ () () (toMiriAllocId id1, Miri.ABI.Size.ofBytes 0) rfl).trans ?_
      dsimp only
      rw [ite_f (by decide)]
      refine (est_bind_ok _ _ () () (some (42, 2)) hg).trans ?_
      have hchk : Miri.Interpreter.VTable.checkForTypeRead hooks () 2 4 () =
          .error (.undefinedBehavior "InvalidVTableTrait") () := rfl
      exact est_bind_err _ _ () () _ hchk
  exact ⟨hok, hbadOff, hbadTr, by decide⟩

/-- Real vendored `Miri.Interpreter.VTableMachine.reserve` salted-dedup canary
(`lean-miri#75`): reserving `(42, 7)` twice from `MemoryState.empty` +
`VTableMachine.Registry.empty` under distinct salts `0 ≠ 1 : Fin 32` allocates
distinct `AllocId`s `1 ≠ 2` that both resolve via `VTableMachine.globalVTable`
to `some (42, 7)`. -/
theorem vtable_salted_canary :
    let st₀ : Miri.Interpreter.MachineHooks.State Unit Miri.Interpreter.VTableMachine.Registry :=
      { stack := ⟨#[]⟩
        machine := {
          memory := Miri.Memory.MemoryState.empty
          borrowTracker := none
          dataRace := none
          threads := Miri.Concurrency.ThreadManager.initial true
          raceAllocations := #[]
          allocationSpans := #[]
          user := Miri.Interpreter.VTableMachine.Registry.empty } }
    let fnHooks : Miri.Interpreter.FunctionPointers.Hooks Unit Miri.Interpreter.VTableMachine.Registry Unit :=
      { registry := fun _ => Miri.Interpreter.FunctionPointers.Registry.empty
        putRegistry := fun u _ => u
        crossCrateInlineAlways := false
        inlineNever := fun _ => pure false
        chooseSalt := pure ⟨0, by decide⟩
        ptrGetAlloc := fun _ => pure none
        adjustRootPointer := fun id tag => pure ⟨Miri.ABI.Size.ZERO, .concrete id tag⟩
        importedFunction := fun _ => pure none }
    let vtHooks : Miri.Interpreter.VTableMachine.Hooks Unit Miri.Interpreter.VTableMachine.Registry Unit :=
      { functions := fnHooks
        target := annealRuntimeDataLayout
        registry := fun u => u
        putRegistry := fun _ r => r
        importedVTable := fun _ => pure none }
    let id1 : Miri.Memory.AllocId := ⟨1, by decide⟩
    let id2 : Miri.Memory.AllocId := ⟨2, by decide⟩
    ∃ st₁ st₂,
      Miri.Interpreter.VTableMachine.reserve vtHooks 42 7 ⟨0, by decide⟩ st₀ = .ok id1 st₁ ∧
      Miri.Interpreter.VTableMachine.reserve vtHooks 42 7 ⟨1, by decide⟩ st₁ = .ok id2 st₂ ∧
      id1 ≠ id2 ∧
      Miri.Interpreter.VTableMachine.globalVTable vtHooks id1 st₂ = .ok (some (42, 7)) st₂ ∧
      Miri.Interpreter.VTableMachine.globalVTable vtHooks id2 st₂ = .ok (some (42, 7)) st₂ := by
  intro st₀ fnHooks vtHooks id1 id2
  let dummyBase : Miri.Interpreter.VTableHooks Miri.Memory.Provenance
      (Miri.Interpreter.MachineHooks.State Unit Miri.Interpreter.VTableMachine.Registry) Unit
      Miri.Interpreter.CallInstance Unit :=
    { target := annealTargetDataLayout
      isDynamic := fun _ _ => pure false
      memoryOffset := fun _ _ _ _ _ => throw (.invalidProgram "")
      resolvePointer := fun _ _ => throw (.invalidProgram "")
      globalFunction := fun _ _ => pure none
      globalVTable := fun _ _ => pure none
      predicates := fun _ _ => pure #[]
      normalizePredicate := fun _ p => pure p.id
      layoutOf := fun _ _ => throw (.invalidProgram "")
      eraseAndAnonymize := fun _ t d => pure (t, d)
      ensureMonomorphicType := fun _ _ => pure ()
      ensureMonomorphicDyn := fun _ _ => pure ()
      globalSalt := fun _ => pure 0
      reserveVTable := fun _ _ _ _ => pure id1
      globalRootPointer := fun _ _ => throw (.invalidProgram "")
      entries := fun _ _ _ => pure #[]
      assertVirtualInstanceMatches := fun _ _ _ _ _ => pure () }
  obtain ⟨hne, st₁, st₂, hr1, hr2, _, _, hg1, hg2⟩ :=
    miri_vtable_getPointer_salted_distinct_allocIds vtHooks dummyBase () 42 7
      ⟨0, by decide⟩ ⟨1, by decide⟩ (by decide) st₀ rfl rfl (fun _ _ => rfl)
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      ⟨Miri.ABI.Size.ZERO, .concrete id1 ⟨1, by decide⟩⟩
      ⟨Miri.ABI.Size.ZERO, .concrete id2 ⟨1, by decide⟩⟩
  exact ⟨st₁, st₂, hr1, hr2, hne, hg1, hg2⟩

/-- Choice-free `[T; N]` `Sized` fast-path (`lean-miri#79`), Unicode scalar
`ScalarInt.toChar` (`lean-miri#82`), and wide-`dyn` precedence canary:
1. `[u8; usize::MAX]` is syntactically `Sized` and passes `validateRawPtrFastPath`
   without layout evaluation (`computeTyLayout` overflows).
2. `ScalarInt.ofUInt32` `.toChar.isOk` matches `isUnicodeScalarValue` on `'A'`,
   surrogate `0xD800`, and out-of-range `0x110000`.
3. Double-null `&dyn Send` fails with `invalidVTableNull` BEFORE data-pointer UB. -/
theorem sized_fastPath_char_and_wideDyn_canary :
    isSyntacticallySized (.array (.uint 1) 18446744073709551615) = true ∧
    validateRawPtrFastPath (.array (.uint 1) 18446744073709551615) (.thin 0) = .ok () ∧
    unsizedMetadataTail (.dynamic "Send") = some .dynVTable ∧
    (Miri.Memory.ScalarInt.ofUInt32 0x41).toChar.isOk = true ∧
    (Miri.Memory.ScalarInt.ofUInt32 0xD800).toChar.isOk = false ∧
    (Miri.Memory.ScalarInt.ofUInt32 0x110000).toChar.isOk = false ∧
    validateWideDynSafePtr KeyedAllocWorld.empty VTableRegistry.empty
      .null .null (canarySpecTable 0) = .error .invalidVTableNull := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, rfl⟩
  · rw [← isUnicodeScalarValue_eq_scalarInt_toChar_isOk]; rfl
  · rw [← isUnicodeScalarValue_eq_scalarInt_toChar_isOk]; rfl
  · rw [← isUnicodeScalarValue_eq_scalarInt_toChar_isOk]; rfl

/-- Real vendored `Miri.Interpreter.ValidityMachine.scalarMayBeNull` canary
(`lean-miri#82`): provenance-agnostic null detection returns `true` for BOTH a
provenance-free `0` integer AND a provenanced pointer with `offset = 0`, and
`false` for `offset = 8`. -/
theorem validityMachine_null_canary :
    let st : Miri.Interpreter.ValidityMachine.State Unit Unit :=
      { stack := ⟨#[]⟩
        machine := {
          memory := Miri.Memory.MemoryState.empty
          borrowTracker := none
          dataRace := none
          threads := Miri.Concurrency.ThreadManager.initial true
          raceAllocations := #[]
          allocationSpans := #[]
          user := { addresses := { provenanceMode := .default
                                   addressMode := .managed
                                   generation := none }
                    payload := { payload := (), validation := .Deep, alignment := .Int } } } }
    let prov : Miri.Memory.Provenance := .concrete ⟨1, by decide⟩ ⟨1, by decide⟩
    (∃ sc, Miri.Memory.Scalar.fromMaybePointer annealTargetDataLayout ⟨⟨0⟩, none⟩ = .ok sc ∧
      Miri.Interpreter.ValidityMachine.scalarMayBeNull sc st = .ok true st) ∧
    (∃ sc, Miri.Memory.Scalar.fromMaybePointer annealTargetDataLayout ⟨⟨0⟩, some prov⟩ = .ok sc ∧
      Miri.Interpreter.ValidityMachine.scalarMayBeNull sc st = .ok true st) ∧
    (∃ sc, Miri.Memory.Scalar.fromMaybePointer annealTargetDataLayout ⟨⟨8⟩, some prov⟩ = .ok sc ∧
      Miri.Interpreter.ValidityMachine.scalarMayBeNull sc st = .ok false st) := by
  intro st prov
  exact ⟨validityMachine_scalarMayBeNull_eq ⟨⟨0⟩, none⟩ st,
    validityMachine_scalarMayBeNull_eq ⟨⟨0⟩, some prov⟩ st,
    validityMachine_scalarMayBeNull_eq ⟨⟨8⟩, some prov⟩ st⟩

/-- **Tightness of the `live` distinct-key hypothesis for the KEYED world** (closed canary):
swapping two `live` rows that share one `AllocId` (`.stack` first vs `.machine` first) is a
permutation, yet it changes the first-match keyed entry and therefore the whole `KeyedAllocWorld`.
The distinct-key hypothesis of `annealMachineToKeyed_eq_of_liveDead_perm` is thus exact, while
`stateRelLM3_1_livePerm_deadAny` shows `StateRelLM3_1` itself needs none. -/
theorem liveDuplicateKey_perm_separation_canary :
    let proj : RowProjection Miri.Memory.Provenance Unit Unit :=
      ⟨fun _ => .heap, fun _ => [], fun _ => []⟩
    let id1 : Miri.Memory.AllocId := ⟨1, by decide⟩
    let la1 : Miri.Memory.LocalAllocation Miri.Memory.Provenance Unit Unit :=
      ⟨.stack, baseRetagAllocation⟩
    let la2 : Miri.Memory.LocalAllocation Miri.Memory.Provenance Unit Unit :=
      ⟨.machine (), baseRetagAllocation⟩
    let rows₁ : MiriAllocRows Miri.Memory.Provenance Unit Unit :=
      { nextAllocId := 2, issued := #[id1], live := #[(id1, la1), (id1, la2)] }
    let rows₂ : MiriAllocRows Miri.Memory.Provenance Unit Unit :=
      { nextAllocId := 2, issued := #[id1], live := #[(id1, la2), (id1, la1)] }
    rows₁.live.toList.Perm rows₂.live.toList ∧
    ((rows₁.toKeyed proj).findLive? (ofMiriAllocId id1)).map (·.kind) = some .stack ∧
    ((rows₂.toKeyed proj).findLive? (ofMiriAllocId id1)).map (·.kind) = some .heap ∧
    rows₁.toKeyed proj ≠ rows₂.toKeyed proj := by
  intro proj id1 la1 la2 rows₁ rows₂
  have h1 : ((rows₁.toKeyed proj).findLive? (ofMiriAllocId id1)).map (·.kind) = some .stack := by
    rw [toKeyed_findLive?]; rfl
  have h2 : ((rows₂.toKeyed proj).findLive? (ofMiriAllocId id1)).map (·.kind) = some .heap := by
    rw [toKeyed_findLive?]; rfl
  refine ⟨List.Perm.swap _ _ [], h1, h2, fun heq => ?_⟩
  rw [heq, h2] at h1
  cases h1

/-- **Closed deallocation data-race stage canary** on real vendored machines:
1. `DeallocRaceStageRel` discriminates outcomes (a vendored success is never related to a theory
   data race, nor a vendored data race to a theory success);
2. without a race detector the stage relates to `machineDeallocHook .unconfigured`;
3. with a configured detector whose `raceDetecting` is `false` and NO vector clock for the
   allocation, both sides report the missing clock — BEFORE the `raceDetecting` gate. -/
theorem deallocRaceStage_canary :
    let machine : Miri.Interpreter.MachineHooks.MachineState Unit Unit :=
      { memory := Miri.Memory.MemoryState.empty
        borrowTracker := none
        dataRace := none
        threads := Miri.Concurrency.ThreadManager.initial true
        raceAllocations := #[]
        allocationSpans := #[]
        user := () }
    let configured : Miri.Interpreter.MachineHooks.MachineState Unit Unit :=
      { machine with dataRace := some (Miri.Concurrency.GlobalState.initial false false) }
    let id1 : Miri.Memory.AllocId := ⟨1, by decide⟩
    let actor : DeallocActor := DeallocActor.ofVClock 0 []
    ¬ DeallocRaceStageRel (.ok ()) (.error "DataRace") ∧
    ¬ DeallocRaceStageRel (.error (.undefinedBehavior "DataRace")) (.ok ()) ∧
    raceModeOfMachine machine = .unconfigured ∧
    DeallocRaceStageRel
      (Miri.Interpreter.MachineHooks.memoryRaceAccess machine id1 ⟨Miri.ABI.Size.ZERO, ⟨8⟩⟩
        (some .Deallocate) .Read).2
      (machineDeallocHook .unconfigured actor .ok none 8) ∧
    raceModeOfMachine configured = .configured false ∧
    DeallocRaceStageRel
      (Miri.Interpreter.MachineHooks.memoryRaceAccess configured id1 ⟨Miri.ABI.Size.ZERO, ⟨8⟩⟩
        (some .Deallocate) .Read).2
      (machineDeallocHook (.configured false) actor .ok none 8) ∧
    machineDeallocHook (.configured false) actor .ok none 8 =
      .error "MissingVectorClockExtra" := by
  intro machine configured id1 actor
  refine ⟨?_, ?_, rfl, ?_, rfl, ?_, rfl⟩
  · intro h; cases h
  · intro h; cases h
  · exact memoryRaceAccess_dealloc_rel_machineDeallocHook machine id1 ⟨8⟩ actor none rfl
      (fun _ h => by cases h)
  · exact memoryRaceAccess_dealloc_rel_machineDeallocHook configured id1 ⟨8⟩ actor none rfl
      (fun g hg hdet => by
        cases hg
        exact absurd hdet (by decide))

/-- **Closed frame-pop release-fold canary on a real vendored `BorrowTree`**
(`releaseProtectorSimTree` inside `liveTreeMemory`): the fold succeeds when the co-protected tag is
a strict descendant, fails with a protector-end access error when the co-protected tag is a
sibling (pinned-Miri batch order), and is undefined for an allocation that is not live. -/
theorem stackPopReleaseAll_canary :
    let t2 : Miri.Memory.BorTag := ⟨2, by decide⟩
    let t3 : Miri.Memory.BorTag := ⟨3, by decide⟩
    let t4 : Miri.Memory.BorTag := ⟨4, by decide⟩
    let mem := liveTreeMemory releaseProtectorSimTree
    (∃ mem', stackPopReleaseAll ⟨#[(t2, .StrongProtector), (t4, .StrongProtector)]⟩
      [(retagTestAllocId, t2)] mem = some (mem', none)) ∧
    (∃ mem' err, stackPopReleaseAll ⟨#[(t2, .StrongProtector), (t3, .StrongProtector)]⟩
      [(retagTestAllocId, t2)] mem = some (mem', some err)) ∧
    stackPopReleaseAll ⟨#[]⟩ [((⟨9, by decide⟩ : Miri.Memory.AllocId), t2)] mem = none := by
  intro t2 t3 t4 mem
  have hsep := miri_releaseProtector_skipChildren_and_siblingConflict
  have hfind : mem.live.find? (fun e => e.1 == retagTestAllocId) =
      some (retagTestAllocId,
        { kind := .stack, allocation := liveTreeAllocation releaseProtectorSimTree }) := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [stackPopReleaseAll_singleton _ _ _ _ _ hfind]
    have h1 : stackPopReleaseErr (releaseProtectorSimTree.releaseProtector t2
        ⟨#[(t2, .StrongProtector), (t4, .StrongProtector)]⟩).status = some none := by
      rw [hsep.1]; rfl
    exact ⟨_, by
      show (match stackPopReleaseErr (releaseProtectorSimTree.releaseProtector t2
          ⟨#[(t2, .StrongProtector), (t4, .StrongProtector)]⟩).status with
        | some none => _ | some (some err) => _ | none => _) = _
      rw [h1]⟩
  · rw [stackPopReleaseAll_singleton _ _ _ _ _ hfind]
    have h2 : ∃ err, stackPopReleaseErr (releaseProtectorSimTree.releaseProtector t2
        ⟨#[(t2, .StrongProtector), (t3, .StrongProtector)]⟩).status = some (some err) := by
      have hs := hsep.2.2.2.1
      cases hst : (releaseProtectorSimTree.releaseProtector t2
          ⟨#[(t2, .StrongProtector), (t3, .StrongProtector)]⟩).status with
      | AccessFailure r status => exact ⟨_, rfl⟩
      | Released => rw [hst] at hs; cases hs
      | MissingTag _ => rw [hst] at hs; cases hs
      | RangeMapFailure _ => rw [hst] at hs; cases hs
      | LocationMapFailure _ => rw [hst] at hs; cases hs
      | ExposureUpdateFailure _ => rw [hst] at hs; cases hs
    obtain ⟨err, h2⟩ := h2
    exact ⟨_, err, by
      show (match stackPopReleaseErr (releaseProtectorSimTree.releaseProtector t2
          ⟨#[(t2, .StrongProtector), (t3, .StrongProtector)]⟩).status with
        | some none => _ | some (some err) => _ | none => _) = _
      rw [h2]⟩
  · rfl

/-- Canary resolver for vtable words. -/
def canaryWideResolve (p : Miri.Memory.Pointer (Option AnnealProv)) :
    Except Miri.Interpreter.VTablePointerError (Miri.Memory.AllocId × Miri.ABI.Size) :=
  match p.provenance with
  | some (.concrete id _) => .ok (id, p.offset)
  | _ => .error .danglingInteger

/-- Canary unsized pointee layout. -/
def canaryUnsizedLayout : Miri.Interpreter.LocalLayout :=
  ⟨0, { zstLayoutData with backendRepr := .Memory (sized := false) }⟩

/-- Canary wide place: NULL data pointer, vtable word `vtWord`. -/
def canaryWideTarget (vtWord : Miri.Memory.Scalar AnnealProv) :
    Miri.Interpreter.MPlaceTy AnnealProv :=
  ⟨⟨⟨Miri.ABI.Size.ZERO, none⟩, .metadata vtWord, none⟩, canaryUnsizedLayout⟩

/-- Canary world: `1` a `.vtable` global, `2` a tombstone, `3` a `.function` global, `4` a live heap
allocation. -/
def canaryWideWorld : KeyedAllocWorld :=
  ((((KeyedAllocWorld.empty.registerGlobal ⟨1, by decide⟩ ⟨.vtable, 24, 3, .not, []⟩).registerGlobal
    ⟨3, by decide⟩ ⟨.function, 0, 0, .not, []⟩).insertLive ⟨4, by decide⟩
      ⟨8, 3, .heap, .mut, []⟩).insertDead ⟨2, by decide⟩ ⟨8, 3⟩)

/-- Canary registry: vtable `1` implements `dyn Trait7 + Send` for concrete type code `42`. -/
def canaryWideReg : VTableRegistry :=
  { VTableRegistry.empty with
    allocToData := VTableRegistry.empty.allocToData.insert ⟨1, by decide⟩
      ⟨.uint 8, 42, none, 16, 3, canarySpecTable 2, []⟩ }

/-- Canary encoding of the existentials of `canarySpecTable`. -/
def canaryWideDynCode (s : DynExistentialSpec) : Nat :=
  if s == canarySpecTable 0 then 0
  else if s == canarySpecTable 1 then 1
  else if s == canarySpecTable 2 then 2
  else if s == canarySpecTable 3 then 3
  else 4


private theorem canaryWideReg_get? (id : MiriAllocId) (data : VTableData)
    (h : canaryWideReg.allocToData.get? id = some data) :
    id = ⟨1, by decide⟩ ∧ data.spec = canarySpecTable 2 := by
  unfold canaryWideReg at h
  dsimp only at h
  by_cases hid : id = ⟨1, by decide⟩
  · subst hid
    rw [ExtTreeMap0.get?_insert_self] at h
    injection h with h
    subst h
    exact ⟨rfl, rfl⟩
  · rw [ExtTreeMap0.get?_insert_ne _ _ hid] at h
    cases h

private theorem canaryWide_predsKeyInjective (n : Nat) :
    PredsKeyInjective (canarySpecTable n).effectivePreds := by
  have h : ∀ k : Nat, PredsKeyInjective (canarySpecTable k).effectivePreds := by
    intro k
    match k with
    | 0 => intro p hp q hq; revert p q; decide
    | 1 => intro p hp q hq; revert p q; decide
    | 2 => intro p hp q hq; revert p q; decide
    | 3 => intro p hp q hq; revert p q; decide
    | k + 4 =>
      have hk : canarySpecTable (k + 4) = ⟨some 8, AutoTraitSet.empty, []⟩ := rfl
      rw [hk]
      intro p hp q hq; revert p q; decide
  exact h n

/-- Canary hooks: `annealValidityHooks` data-pointer leaves + world-backed vtable leaves. -/
def canaryWideHooks (vtWord : Miri.Memory.Scalar AnnealProv) (expected : Nat) :
    Miri.Interpreter.ValidityVisitor.Hooks AnnealProv AnnealStepState
      Trusted.Rustc.V2026_06_01.MirAst.Ty Unit Unit Unit Unit :=
  annealWideDynHooks emptyLayoutTable
    (worldVTableHooks AnnealProv AnnealStepState Trusted.Rustc.V2026_06_01.MirAst.Ty
      canaryWideWorld canaryWideReg canaryWideResolve canarySpecTable canaryWideDynCode)
    ⟨.uninit, canaryUnsizedLayout⟩ (canaryWideTarget vtWord) expected

private theorem canaryWide_run (m : AnnealStepState) (recursive : Bool)
    (vtWord : Miri.Memory.Scalar AnnealProv) (expected : Nat)
    (vtPtr : Miri.Memory.Pointer (Option AnnealProv)) (vptr : VTablePtrVal) (e : WideDynErr)
    (htoptr : vtWord.toPointer annealTargetDataLayout = .ok vtPtr)
    (hres : match vptr with
      | .null => canaryWideResolve vtPtr = .error .danglingInteger
      | .danglingInt _ => canaryWideResolve vtPtr = .error .danglingInteger
      | .provenanced id off =>
        canaryWideResolve vtPtr = .ok (toMiriAllocId id, Miri.ABI.Size.ofBytes off))
    (hbad : validateVTableHalf canaryWideWorld canaryWideReg vptr (canarySpecTable expected) =
      .error e) :
    Miri.Interpreter.ValidityVisitor.validatePlace (canaryWideHooks vtWord expected)
        { kind := .tuple .nil, layoutIdx := 0 } 1
        ⟨.memory ⟨⟨Miri.ABI.Size.ZERO, none⟩, .none, none⟩, canaryUnsizedLayout⟩
        recursive false m = .error (wideDynVTableErrToMiri e) m :=
  (validatePlace_wideDyn_invalidVTable_precedes_dataPtr_at (canaryWideHooks vtWord expected)
    { kind := .tuple .nil, layoutIdx := 0 } 0
    ⟨.memory ⟨⟨Miri.ABI.Size.ZERO, none⟩, .none, none⟩, canaryUnsizedLayout⟩ recursive m ""
    false expected ⟨.uninit, canaryUnsizedLayout⟩ (canaryWideTarget vtWord) vtWord vtPtr
    canaryWideWorld canaryWideReg canaryWideResolve canarySpecTable canaryWideDynCode vptr e
    rfl (fun _ _ hx => hx) rfl rfl rfl rfl rfl rfl htoptr
    (worldVTableHooks_readsWorldAt _ _ _ _ _ _ _ _ _ _)
    (fun id data hd => by rw [(canaryWideReg_get? id data hd).2]; decide)
    hres (canaryWide_predsKeyInjective expected)
    (fun id data hd => by
      rw [(canaryWideReg_get? id data hd).2]; exact canaryWide_predsKeyInjective 2)
    hbad).1

/-- **Closed wide-`dyn` vtable-before-data canary on the vendored `validatePlace` driver**
(`lean-miri#82`), for EVERY machine state and BOTH `recursive = false` and `recursive = true`. The
data pointer is null in every case, and every data-pointer leaf is the real
`RefLM3_2.annealValidityHooks` leaf:
1. double-null `&dyn Trait7` (`null` vtable word) — `InvalidVTablePointer`;
2. dangling integer vtable word — `InvalidVTablePointer`;
3. vtable word pointing to a dead allocation — `InvalidVTablePointer`;
4. vtable word pointing to a `.function` global (wrong global kind) — `InvalidVTablePointer`;
5. vtable word pointing to a live heap allocation — `InvalidVTablePointer`;
6. `dyn Trait7 + Send` vtable for an expected `dyn Trait8` — `InvalidVTableTrait`;
and the valid vtable is accepted by the vtable stage (`.ok 42`) — so the six rejections are not
vacuous — after which the driver reaches the first data-pointer leaf, where the stock
`annealValidityHooks.sizeAndAlign` fails closed (`unsupported`, not undefined behavior). -/
theorem wideDyn_invalidVTable_validatePlace_canary (m : AnnealStepState) (recursive : Bool) :
    let intWord : UInt64 → Miri.Memory.Scalar AnnealProv := fun a =>
      Miri.Memory.Scalar.fromScalarInt (Miri.Memory.ScalarInt.ofUInt64 a)
    let ptrWord : Miri.Memory.AllocId → Miri.Memory.Scalar AnnealProv := fun id =>
      Miri.Memory.Scalar.fromPointer annealTargetDataLayout ⟨⟨0⟩, .concrete id ⟨1, by decide⟩⟩
    let run := fun (vtWord : Miri.Memory.Scalar AnnealProv) (expected : Nat) =>
      Miri.Interpreter.ValidityVisitor.validatePlace (canaryWideHooks vtWord expected)
        { kind := .tuple .nil, layoutIdx := 0 } 1
        ⟨.memory ⟨⟨Miri.ABI.Size.ZERO, none⟩, .none, none⟩, canaryUnsizedLayout⟩
        recursive false m
    run (intWord 0) 3 = .error (.undefinedBehavior "InvalidVTablePointer") m ∧
    run (intWord 4096) 3 = .error (.undefinedBehavior "InvalidVTablePointer") m ∧
    run (ptrWord ⟨2, by decide⟩) 3 = .error (.undefinedBehavior "InvalidVTablePointer") m ∧
    run (ptrWord ⟨3, by decide⟩) 3 = .error (.undefinedBehavior "InvalidVTablePointer") m ∧
    run (ptrWord ⟨4, by decide⟩) 3 = .error (.undefinedBehavior "InvalidVTablePointer") m ∧
    run (ptrWord ⟨1, by decide⟩) 4 = .error (.undefinedBehavior "InvalidVTableTrait") m ∧
    Miri.Interpreter.VTable.getPtrVTableType (canaryWideHooks (ptrWord ⟨1, by decide⟩) 3).vtable
      { kind := .tuple .nil, layoutIdx := 0 }
      ⟨⟨0⟩, some (.concrete ⟨1, by decide⟩ ⟨1, by decide⟩)⟩ (some 3) m = .ok 42 m ∧
    run (ptrWord ⟨1, by decide⟩) 3 = .error (.unsupported "validity of an unsized pointee") m := by
  intro intWord ptrWord run
  have hvalid : Miri.Interpreter.VTable.getPtrVTableType
      (canaryWideHooks (ptrWord ⟨1, by decide⟩) 3).vtable
      ({ kind := .tuple .nil, layoutIdx := 0 } : Trusted.Rustc.V2026_06_01.MirAst.Ty)
      ⟨⟨0⟩, some (.concrete ⟨1, by decide⟩ ⟨1, by decide⟩)⟩ (some 3) m = .ok 42 m :=
    miri_getPtrVTableTypeRead_eq_validateVTableHalf_at
      (canaryWideHooks (ptrWord ⟨1, by decide⟩) 3).vtable.readHooks
      ({ kind := .tuple .nil, layoutIdx := 0 } : Trusted.Rustc.V2026_06_01.MirAst.Ty) m
      canaryWideWorld canaryWideReg canaryWideResolve canarySpecTable canaryWideDynCode
      (worldVTableHooks_readsWorldAt _ _ _ _ _ _ _ _ _ _)
      ⟨⟨0⟩, some (.concrete ⟨1, by decide⟩ ⟨1, by decide⟩)⟩ (.provenanced ⟨1, by decide⟩ 0) 3
      (fun id data hd => by rw [(canaryWideReg_get? id data hd).2]; decide)
      rfl (canaryWide_predsKeyInjective 3)
      (fun id data hd => by
        rw [(canaryWideReg_get? id data hd).2]; exact canaryWide_predsKeyInjective 2)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hvalid, ?_⟩
  · exact canaryWide_run m recursive (intWord 0) 3 ⟨⟨0⟩, none⟩ .null .invalidVTableNull
      (by decide) rfl rfl
  · exact canaryWide_run m recursive (intWord 4096) 3 ⟨⟨4096⟩, none⟩ (.danglingInt 4096)
      (.invalidVTableDanglingInt 4096) (by decide) rfl rfl
  · exact canaryWide_run m recursive (ptrWord ⟨2, by decide⟩) 3
      ⟨⟨0⟩, some (.concrete ⟨2, by decide⟩ ⟨1, by decide⟩)⟩ (.provenanced ⟨2, by decide⟩ 0)
      (.invalidVTableNotGlobalVTable ⟨2, by decide⟩) (by decide) rfl rfl
  · exact canaryWide_run m recursive (ptrWord ⟨3, by decide⟩) 3
      ⟨⟨0⟩, some (.concrete ⟨3, by decide⟩ ⟨1, by decide⟩)⟩ (.provenanced ⟨3, by decide⟩ 0)
      (.invalidVTableNotGlobalVTable ⟨3, by decide⟩) (by decide) rfl rfl
  · exact canaryWide_run m recursive (ptrWord ⟨4, by decide⟩) 3
      ⟨⟨0⟩, some (.concrete ⟨4, by decide⟩ ⟨1, by decide⟩)⟩ (.provenanced ⟨4, by decide⟩ 0)
      (.invalidVTableNotGlobalVTable ⟨4, by decide⟩) (by decide) rfl rfl
  · exact canaryWide_run m recursive (ptrWord ⟨1, by decide⟩) 4
      ⟨⟨0⟩, some (.concrete ⟨1, by decide⟩ ⟨1, by decide⟩)⟩ (.provenanced ⟨1, by decide⟩ 0)
      (.invalidVTableTrait (canarySpecTable 2) (canarySpecTable 4)) (by decide) rfl rfl
  · exact validatePlace_error_of_root_visit_error (canaryWideHooks (ptrWord ⟨1, by decide⟩) 3)
      { kind := .tuple .nil, layoutIdx := 0 } 1
      ⟨.memory ⟨⟨Miri.ABI.Size.ZERO, none⟩, .none, none⟩, canaryUnsizedLayout⟩ recursive m m "" _
      rfl (fun _ hx => hx)
      (visit_wideDyn_validVTable_reaches_sizeAndAlign
        (canaryWideHooks (ptrWord ⟨1, by decide⟩) 3) { kind := .tuple .nil, layoutIdx := 0 } 0 _
        ⟨.memory ⟨⟨Miri.ABI.Size.ZERO, none⟩, .none, none⟩, canaryUnsizedLayout⟩ m m false 3
        ⟨.uninit, canaryUnsizedLayout⟩ (canaryWideTarget (ptrWord ⟨1, by decide⟩))
        (ptrWord ⟨1, by decide⟩) ⟨⟨0⟩, some (.concrete ⟨1, by decide⟩ ⟨1, by decide⟩)⟩ 42 _
        rfl rfl rfl rfl rfl rfl rfl (by decide) hvalid rfl)

/-! ## Part 4. Axiom pins

Every public theorem of this module is pinned below via
`#guard_msgs (whitespace := lax) in #print axioms <name>`:

* **Part 4A (choice-free)**: every theorem whose statement only touches
  choice-free types (`Anneal.ExtTreeMapAllocAndNoWritable`,
  `Miri.Memory.AllocId`, `Miri.TreeBorrows.RetagPolicy`,
  `TraversalTree.traverse`, `VTable.checkForTypeRead`, `VTable.getPtrVTableTypeRead`,
  `VTable.getSizeAndAlignRead`, `ValidityVisitor.visit`, `ScalarInt.toChar`, etc.)
  depends on at most `[propext, Quot.sound]` — **zero `Classical.choice`**.
* **Part 4B (vendored stateful bridges)**: theorems whose statements reference
  vendored `Miri.Memory.MemoryState` (`KeyedArray` over `Std.HashMap`),
  `StateRelLM3_1` / `StateRelLM3_2`, `ValidityMachine`, `ValidityVisitor.validatePlace`,
  `annealValidityHooks`, `VTableMachine.reserve`, or `BorrowTree.releaseProtector`
  depend on at most `[propext, Classical.choice, Quot.sound]`, matching
  `LeanMiriSpec.FloatCastLM` and `LeanMiriSpec.WitFloatCastLM`.
* **Zero `sorryAx`, zero `Lean.ofReduceBool` (`native_decide`), zero `unsafe`,
  and zero custom axioms** anywhere in this module.

### 4A. Choice-free public theorems (at most `propext` and `Quot.sound`) -/

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

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.writeNonAtomic_zeroSize_ok'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms writeNonAtomic_zeroSize_ok

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.nonAtomicWriteDetect_dealloc_writer_race_iff'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms nonAtomicWriteDetect_dealloc_writer_race_iff

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.reachesRoot_unique_depth'
does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms reachesRoot_unique_depth

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.foreignPostorderTags_fuel_irrel_rooted'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms foreignPostorderTags_fuel_irrel_rooted

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.foreignPostorderTags_len_eq_len_succ'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms foreignPostorderTags_len_eq_len_succ

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.traversalChildren_traversalTreeOfNodes_of_mem'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms traversalChildren_traversalTreeOfNodes_of_mem

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.miri_traverse_eq_foreignVisitScheduleNodes'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms miri_traverse_eq_foreignVisitScheduleNodes

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.miri_initialForeignRoots_skipChildren_eq'
does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms miri_initialForeignRoots_skipChildren_eq

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.miri_traverse_skipChildren_eq_schedule'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms miri_traverse_skipChildren_eq_schedule

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.miri_traverse_skipChildren_excludes_strictDescendants'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms miri_traverse_skipChildren_excludes_strictDescendants

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.miri_sortedPredicates_map_id_eq_canonical'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms miri_sortedPredicates_map_id_eq_canonical

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.miri_checkForTypeRead_eq_vtableMatchesExpectedSpec'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms miri_checkForTypeRead_eq_vtableMatchesExpectedSpec

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.miriVTableTraitCheckOk_eq_vtableMatchesExpectedSpec'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms miriVTableTraitCheckOk_eq_vtableMatchesExpectedSpec

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.miri_checkForTypeRead_principal_auto_eq'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms miri_checkForTypeRead_principal_auto_eq

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.miri_checkForTypeRead_stableKey_collision_separation'
depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms miri_checkForTypeRead_stableKey_collision_separation

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.miri_getPtrVTableTypeRead_eq_validateVTableHalf'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms miri_getPtrVTableTypeRead_eq_validateVTableHalf

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.miri_getSizeAndAlignRead_eq_of_layoutConsistent'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms miri_getSizeAndAlignRead_eq_of_layoutConsistent

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.upcastVTableToAutoTraits_preserves_miri_sizeAndAlign'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms upcastVTableToAutoTraits_preserves_miri_sizeAndAlign

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.visit_rawPointer_sized_fastPath'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms visit_rawPointer_sized_fastPath

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.visit_rawPointer_unsized_foreign_and_slice'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms visit_rawPointer_unsized_foreign_and_slice

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.visit_rawPointer_unsized_dyn_vtable_only'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms visit_rawPointer_unsized_dyn_vtable_only

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.visit_wideDyn_checkSafe_vtableBeforeDataUB'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms visit_wideDyn_checkSafe_vtableBeforeDataUB

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.visit_checkSafe_mayDangle_precedence'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms visit_checkSafe_mayDangle_precedence

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.isUnicodeScalarValue_eq_scalarInt_toChar_isOk'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isUnicodeScalarValue_eq_scalarInt_toChar_isOk

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.visit_childSession_pointee_correspondence'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms visit_childSession_pointee_correspondence

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.visit_root_tracks_pointee_for_childSession'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms visit_root_tracks_pointee_for_childSession

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.visit_nested_wideSafeRef_childSession'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms visit_nested_wideSafeRef_childSession

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.traversal_skipChildren_canary'
does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms traversal_skipChildren_canary

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.vtable_general_canary'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms vtable_general_canary

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.sized_fastPath_char_and_wideDyn_canary'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms sized_fastPath_char_and_wideDyn_canary

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.worldVTableReadHooks_readsWorldAt'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms worldVTableReadHooks_readsWorldAt

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.miri_checkForTypeRead_eq_vtableMatchesExpectedSpec_at'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms miri_checkForTypeRead_eq_vtableMatchesExpectedSpec_at

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.miri_getPtrVTableTypeRead_eq_validateVTableHalf_at'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms miri_getPtrVTableTypeRead_eq_validateVTableHalf_at

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.wideDynVTableErrToMiri_isUB'
depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms wideDynVTableErrToMiri_isUB

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.visit_wideDyn_invalidVTable_precedes_dataPtr_at'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms visit_wideDyn_invalidVTable_precedes_dataPtr_at

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.validateVTableHalf_invalidForms'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms validateVTableHalf_invalidForms

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.visit_wideDyn_validVTable_reaches_sizeAndAlign'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms visit_wideDyn_validVTable_reaches_sizeAndAlign

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.visit_unsizedRef_metadataTail_error'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms visit_unsizedRef_metadataTail_error

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.worldVTableHooks_readsWorldAt'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms worldVTableHooks_readsWorldAt

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.liveDuplicateKey_perm_separation_canary'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms liveDuplicateKey_perm_separation_canary

/-! ### 4B. Vendored stateful bridge theorems (at most `propext`, `Classical.choice`, `Quot.sound`)

The statements of these 72 theorems directly mention vendored `Miri.*` or
`LeanMiriSpec.*` stateful definitions (`MemoryState`, `KeyedArray`,
`AnnealMachine` / `annealResolvePtr`, `StateRelLM3_1` / `StateRelLM3_2`,
`BorrowTree.releaseProtector`, `beforeStackPopWithEnsure`, `MachineHooks.MachineState`,
`VTableMachine.reserve`, `ValidityMachine`, `annealValidityHooks`,
`ValidityVisitor.validatePlace`) whose own types/definitions inherit
`Classical.choice` from `Std.HashMap` / `KeyedArray` (recorded in Part 4C),
matching `LeanMiriSpec.FloatCastLM` and `LeanMiriSpec.WitFloatCastLM`. -/

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.resolveWithBase_eq_annealResolvePtr'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms resolveWithBase_eq_annealResolvePtr

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.ptrRel_annealResolvePtr_resolvesAs'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ptrRel_annealResolvePtr_resolvesAs

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.ptrRel_annealResolvePtr_checkPtrAccess_isOk_eq_keyed'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ptrRel_annealResolvePtr_checkPtrAccess_isOk_eq_keyed

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.keyedArray_find?_eq_list_find?'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms keyedArray_find?_eq_list_find?

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.keyedArray_any?_eq_list_any'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms keyedArray_any?_eq_list_any

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.allocWorldRel_memoryState'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms allocWorldRel_memoryState

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.memoryState_findGlobal?_eq_list_find?'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms memoryState_findGlobal?_eq_list_find?

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.memoryState_hasIssuedId_eq_any'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms memoryState_hasIssuedId_eq_any

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.memoryState_hasGlobalId_eq_any'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms memoryState_hasGlobalId_eq_any

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.memoryState_isAllocLive_eq_keyed'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms memoryState_isAllocLive_eq_keyed

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.memoryState_getAllocInfo_eq_keyed'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms memoryState_getAllocInfo_eq_keyed

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.memoryState_getLiveAllocSizeAndAlign_eq_keyed'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms memoryState_getLiveAllocSizeAndAlign_eq_keyed

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.memoryState_checkPtrAccess_isOk_eq_keyed'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms memoryState_checkPtrAccess_isOk_eq_keyed

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.memoryState_toKeyed_eq_of_perm'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms memoryState_toKeyed_eq_of_perm

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.memoryState_reserveAllocId_eq_keyed'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms memoryState_reserveAllocId_eq_keyed

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.memoryState_insertAllocation_eq_keyed'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms memoryState_insertAllocation_eq_keyed

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.memoryState_allocatePtr_eq_keyed'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms memoryState_allocatePtr_eq_keyed

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.memoryState_deallocatePtrWith_eq_keyed'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms memoryState_deallocatePtrWith_eq_keyed

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.memoryState_duplicateGlobal_hasFunctionPointer_separation'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms memoryState_duplicateGlobal_hasFunctionPointer_separation

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.memoryState_machineKind_collapse_separation'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms memoryState_machineKind_collapse_separation

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.memoryRaceAccess_unconfigured'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms memoryRaceAccess_unconfigured

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.memoryRaceAccess_missingClock_before_raceDetecting'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms memoryRaceAccess_missingClock_before_raceDetecting

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.memoryRaceAccess_raceDetecting_false'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms memoryRaceAccess_raceDetecting_false

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.allocationMachine_deallocate_detaches_race_on_postRemoval'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms allocationMachine_deallocate_detaches_race_on_postRemoval

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.StateRelLM3_1.toKeyed'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms StateRelLM3_1.toKeyed

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.StateRelLM3_2.toKeyed'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms StateRelLM3_2.toKeyed

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.KeyedStateRelLM3_1.toLM3_2'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms KeyedStateRelLM3_1.toLM3_2

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.keyedStateRelLM3_1_alloc_lookup'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms keyedStateRelLM3_1_alloc_lookup

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.keyedStateRelLM3_1_checkPtrAccess'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms keyedStateRelLM3_1_checkPtrAccess

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.keyedStateRelLM3_1_liveDead_perm_invariant'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms keyedStateRelLM3_1_liveDead_perm_invariant

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.keyedStateRelLM3_2_liveDead_perm_invariant'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms keyedStateRelLM3_2_liveDead_perm_invariant

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.keyedStateRelLM3_1_insertAllocation_step'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms keyedStateRelLM3_1_insertAllocation_step

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.keyedStateRelLM3_1_deallocate_step'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms keyedStateRelLM3_1_deallocate_step

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.miri_releaseProtector_missingTag'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms miri_releaseProtector_missingTag

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.miri_releaseProtector_noAccess_preserves_tree'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms miri_releaseProtector_noAccess_preserves_tree

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.miri_releaseProtector_skipChildren_and_siblingConflict'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms miri_releaseProtector_skipChildren_and_siblingConflict

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.miri_beforeStackPopWithEnsure_retains_protectors_until_endCall'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms miri_beforeStackPopWithEnsure_retains_protectors_until_endCall

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.miri_vtableMachine_reserve_eq_internSalted'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms miri_vtableMachine_reserve_eq_internSalted

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.miri_vtable_getPointer_salted_distinct_allocIds'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms miri_vtable_getPointer_salted_distinct_allocIds

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.validityMachine_scalarMayBeNull_eq'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms validityMachine_scalarMayBeNull_eq

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.validityMachine_checkPointerAccessResult_eq_keyed'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms validityMachine_checkPointerAccessResult_eq_keyed

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.validateSafeThinRef_eq_annealValidityHooks_validatePlace'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms validateSafeThinRef_eq_annealValidityHooks_validatePlace

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.memoryState_lifecycle_canary'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms memoryState_lifecycle_canary

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.releaseProtector_canary'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms releaseProtector_canary

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.vtable_salted_canary'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms vtable_salted_canary

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.validityMachine_null_canary'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms validityMachine_null_canary

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.keyedStateRelLM3_1_iff'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms keyedStateRelLM3_1_iff

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.keyedStateRelLM3_2_iff'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms keyedStateRelLM3_2_iff

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.stateRelLM3_1_iff_existsUnique_keyed'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms stateRelLM3_1_iff_existsUnique_keyed

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.stateRelLM3_2_iff_existsUnique_keyed'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms stateRelLM3_2_iff_existsUnique_keyed

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.stateRelLM3_1_livePerm_deadAny'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms stateRelLM3_1_livePerm_deadAny

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.stateRelLM3_2_livePerm_deadAny'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms stateRelLM3_2_livePerm_deadAny

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.stateRelLM3_1_livePerm_deadAny_iff'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms stateRelLM3_1_livePerm_deadAny_iff

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.stateRelLM3_2_livePerm_deadAny_iff'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms stateRelLM3_2_livePerm_deadAny_iff

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.annealMachineToKeyed_eq_of_liveDead_perm'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms annealMachineToKeyed_eq_of_liveDead_perm

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.keyedStateRelLM3_1_liveDead_perm_iff'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms keyedStateRelLM3_1_liveDead_perm_iff

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.keyedStateRelLM3_2_liveDead_perm_iff'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms keyedStateRelLM3_2_liveDead_perm_iff

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.memoryRaceAccess_dealloc_rel_machineDeallocHook'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms memoryRaceAccess_dealloc_rel_machineDeallocHook

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.allocationMachine_deallocate_raceAllocations_eq'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms allocationMachine_deallocate_raceAllocations_eq

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.miri_beforeStackPopWithEnsure_eq_releaseAll'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms miri_beforeStackPopWithEnsure_eq_releaseAll

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.stackPopReleaseAll_simulates_execProtectorEndAccesses'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms stackPopReleaseAll_simulates_execProtectorEndAccesses

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.miri_beforeStackPopWithEnsure_simulates_execFrameExitMiri'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms miri_beforeStackPopWithEnsure_simulates_execFrameExitMiri

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.noAccessReleaseSim'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms noAccessReleaseSim

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.stackPopReleaseAll_singleton'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms stackPopReleaseAll_singleton

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.validatePlace_error_of_root_visit_error'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms validatePlace_error_of_root_visit_error

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.validatePlace_wideDyn_invalidVTable_precedes_dataPtr_at'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms validatePlace_wideDyn_invalidVTable_precedes_dataPtr_at

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.annealValidityHooks_getPtrVTableType_failClosed'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms annealValidityHooks_getPtrVTableType_failClosed

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.annealValidityHooks_not_readsWorld'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms annealValidityHooks_not_readsWorld

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.annealValidityHooks_unsizedRef_validatePlace_failClosed'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms annealValidityHooks_unsizedRef_validatePlace_failClosed

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.deallocRaceStage_canary'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms deallocRaceStage_canary

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.stackPopReleaseAll_canary'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms stackPopReleaseAll_canary

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.wideDyn_invalidVTable_validatePlace_canary'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wideDyn_invalidVTable_validatePlace_canary

/-! ### 4C. Origin of `Classical.choice` in vendored `Miri.*` / `LeanMiriSpec.*` constants

These pins document why the 72 vendored-state bridge theorems in Part 4B inherit
`Classical.choice` solely from the types/definitions of vendored `Miri.*` and
pre-existing `LeanMiriSpec.*` constants (`Std.HashMap` / `KeyedArray`), while
all 114 choice-free theorems in Part 4A remain strictly free of `Classical.choice`. -/

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
