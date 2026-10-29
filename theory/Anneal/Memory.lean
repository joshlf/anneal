import Trusted

namespace Anneal.Memory

open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

/-!
Toolchain-independent Tree Borrows permission model, lifetime protectors, and
operational `MirSemantics` agreement theorems for `theory/Anneal/` (`#100`,
`#101`, `#103`).
-/

/-- Abstract Tree Borrows permission state of a pointer tag. -/
inductive AbstractPerm : Type where
  | active
  | reserved
  | frozen
  | disabled
  deriving DecidableEq, Repr, Inhabited

/-- Whether `perm` permits reading through the associated pointer tag. -/
def permAllowsRead : AbstractPerm → Bool
  | .disabled => false
  | _ => true

/-- Whether `perm` permits writing through the associated pointer tag. -/
def permAllowsWrite : AbstractPerm → Bool
  | .active | .reserved => true
  | .frozen | .disabled => false

/-- Updated permission of the writing tag itself after a self-write. -/
def permAfterSelfWrite : AbstractPerm → AbstractPerm
  | .reserved => .active
  | other => other

/-- Updated permission of a child borrow tag when a parent write occurs. -/
def permAfterParentWrite : AbstractPerm → AbstractPerm
  | .active | .frozen => .disabled
  | .reserved => .reserved
  | .disabled => .disabled

/-- Updated permission of a sibling borrow tag when another tag writes. -/
def permAfterSiblingWrite : AbstractPerm → AbstractPerm
  | _ => .disabled

@[simp] theorem disabled_forbids_read : permAllowsRead .disabled = false := rfl
@[simp] theorem disabled_forbids_write : permAllowsWrite .disabled = false := rfl
@[simp] theorem frozen_allows_read : permAllowsRead .frozen = true := rfl
@[simp] theorem frozen_forbids_write : permAllowsWrite .frozen = false := rfl
@[simp] theorem reserved_activates_on_self_write :
    permAfterSelfWrite .reserved = .active := rfl

@[simp]
theorem self_write_preserves_write_permission (p : AbstractPerm)
    (h : permAllowsWrite p = true) :
    permAllowsWrite (permAfterSelfWrite p) = true := by
  cases p <;> simp_all [permAllowsWrite, permAfterSelfWrite]

@[simp] theorem parent_write_disables_active :
    permAfterParentWrite .active = .disabled := rfl
@[simp] theorem parent_write_disables_frozen :
    permAfterParentWrite .frozen = .disabled := rfl
@[simp] theorem parent_write_preserves_reserved :
    permAfterParentWrite .reserved = .reserved := rfl
@[simp] theorem sibling_write_forbids_subsequent_read (p : AbstractPerm) :
    permAllowsRead (permAfterSiblingWrite p) = false := rfl
@[simp] theorem sibling_write_forbids_subsequent_write (p : AbstractPerm) :
    permAllowsWrite (permAfterSiblingWrite p) = false := rfl

/-! ## Byte-Range Tree Borrows Permissions and Function-Exit Protectors (`'a`) -/

/-- Set of active lifetime / function-exit protector tokens `'a`. -/
structure ProtectorSet : Type where
  activeLifetimes : List Nat := []
  deriving DecidableEq, Repr

def ProtectorSet.empty : ProtectorSet := {}

def ProtectorSet.contains (ps : ProtectorSet) (lft : Nat) : Bool :=
  natListContainsBool ps.activeLifetimes lft

def ProtectorSet.insert (ps : ProtectorSet) (lft : Nat) : ProtectorSet :=
  { activeLifetimes := lft :: ps.activeLifetimes }

@[simp]
theorem ProtectorSet.contains_insert_self (ps : ProtectorSet) (lft : Nat) :
    (ps.insert lft).contains lft = true := by
  simp [ProtectorSet.insert, ProtectorSet.contains, natListContainsBool]

/-- Per-byte-range Tree Borrows permission entry. -/
structure ByteRangePerm : Type where
  tag : Nat
  allocId : Nat
  offset : Nat
  len : Nat
  perm : AbstractPerm
  protector : Option Nat := none
  deriving DecidableEq, Repr

def ByteRangePerm.isProtected (entry : ByteRangePerm) (ps : ProtectorSet) : Bool :=
  match entry.protector with
  | some lft => ps.contains lft
  | none => false

def byteRangeOverlapsWrite
    (entry : ByteRangePerm) (writeAlloc writeOffset writeLen : Nat) : Bool :=
  Nat.beq entry.allocId writeAlloc &&
    byteRangesOverlapBool entry.offset entry.len writeOffset writeLen

/-- Propositional disjointness of two `ByteRangePerm` regions. -/
def ByteRangesDisjoint (a b : ByteRangePerm) : Prop :=
  a.allocId ≠ b.allocId ∨ a.len = 0 ∨ b.len = 0 ∨
    a.offset + a.len ≤ b.offset ∨ b.offset + b.len ≤ a.offset

theorem byteRangesDisjoint_symm {a b : ByteRangePerm}
    (h : ByteRangesDisjoint a b) : ByteRangesDisjoint b a := by
  rcases h with h | h | h | h | h
  · exact .inl h.symm
  · exact .inr (.inr (.inl h))
  · exact .inr (.inl h)
  · exact .inr (.inr (.inr (.inr h)))
  · exact .inr (.inr (.inr (.inl h)))

/-- Transition `entry` under a self-write through `entry.tag`. -/
def stepSelfWriteByteRange (entry : ByteRangePerm) : Option ByteRangePerm :=
  if permAllowsWrite entry.perm then
    some { entry with perm := permAfterSelfWrite entry.perm }
  else
    none

/-- Transition `entry` under a foreign write under active protectors `ps`. -/
def stepForeignWriteByteRange (ps : ProtectorSet) (entry : ByteRangePerm)
    (writeAlloc writeOffset writeLen : Nat) : Option ByteRangePerm :=
  if byteRangeOverlapsWrite entry writeAlloc writeOffset writeLen then
    if entry.isProtected ps then
      match entry.perm with
      | .disabled => some entry
      | _ => none
    else
      some { entry with perm := permAfterParentWrite entry.perm }
  else
    some entry

theorem self_write_preserves_protector (entry entry' : ByteRangePerm)
    (ps : ProtectorSet) (h : stepSelfWriteByteRange entry = some entry') :
    entry'.protector = entry.protector ∧
      entry'.isProtected ps = entry.isProtected ps := by
  unfold stepSelfWriteByteRange at h
  split at h
  · injection h with h_eq; subst h_eq; exact ⟨rfl, rfl⟩
  · nomatch h

theorem protector_forbids_conflicting_foreign_write
    (ps : ProtectorSet) (entry : ByteRangePerm)
    (writeAlloc writeOffset writeLen : Nat)
    (h_overlap : byteRangeOverlapsWrite entry writeAlloc writeOffset writeLen = true)
    (h_prot : entry.isProtected ps = true)
    (h_live : entry.perm ≠ .disabled) :
    stepForeignWriteByteRange ps entry writeAlloc writeOffset writeLen = none := by
  unfold stepForeignWriteByteRange
  rw [h_overlap, h_prot]
  cases hp : entry.perm <;> simp_all

@[simp]
theorem disjoint_byte_range_non_interference
    (ps : ProtectorSet) (entry : ByteRangePerm)
    (writeAlloc writeOffset writeLen : Nat)
    (h_disjoint : byteRangeOverlapsWrite entry writeAlloc writeOffset writeLen = false) :
    stepForeignWriteByteRange ps entry writeAlloc writeOffset writeLen = some entry := by
  simp [stepForeignWriteByteRange, h_disjoint]

theorem different_alloc_foreign_write_non_interference
    (ps : ProtectorSet) (entry : ByteRangePerm)
    (writeAlloc writeOffset writeLen : Nat)
    (h_alloc : Nat.beq entry.allocId writeAlloc = false) :
    stepForeignWriteByteRange ps entry writeAlloc writeOffset writeLen = some entry := by
  simp [stepForeignWriteByteRange, byteRangeOverlapsWrite, h_alloc]

/-! ## Operational Bridge to `Trusted.Rustc.V2026_06_01.MirSemantics` -/

def TreeBorrowPerm.toAbstractPerm : TreeBorrowPerm → AbstractPerm
  | .active => .active
  | .reserved => .reserved
  | .frozen => .frozen
  | .disabled => .disabled

def AbstractPerm.toTreeBorrowPerm : AbstractPerm → TreeBorrowPerm
  | .active => .active
  | .reserved => .reserved
  | .frozen => .frozen
  | .disabled => .disabled

@[simp]
theorem toTreeBorrowPerm_toAbstractPerm (p : TreeBorrowPerm) :
    AbstractPerm.toTreeBorrowPerm (TreeBorrowPerm.toAbstractPerm p) = p := by
  cases p <;> rfl

@[simp]
theorem toAbstractPerm_toTreeBorrowPerm (p : AbstractPerm) :
    TreeBorrowPerm.toAbstractPerm (AbstractPerm.toTreeBorrowPerm p) = p := by
  cases p <;> rfl

def BorrowEntry.toByteRangePerm (entry : BorrowEntry) : ByteRangePerm where
  tag := entry.tag
  allocId := entry.targetLocal
  offset := entry.rangeOffset
  len := entry.rangeLen
  perm := TreeBorrowPerm.toAbstractPerm entry.perm
  protector := entry.protector

def ProtectorSet.ofMemory (m : Memory) : ProtectorSet where
  activeLifetimes := m.activeProtectors

@[simp]
theorem isBorrowProtected_eq_isProtected
    (activeProtectors : List Nat) (entry : BorrowEntry) :
    isBorrowProtected activeProtectors entry =
      (BorrowEntry.toByteRangePerm entry).isProtected
        { activeLifetimes := activeProtectors } := by
  cases entry.protector <;> rfl

@[simp]
theorem isBorrowProtected_eq_ofMemory (m : Memory) (entry : BorrowEntry) :
    isBorrowProtected m.activeProtectors entry =
      (BorrowEntry.toByteRangePerm entry).isProtected (ProtectorSet.ofMemory m) :=
  isBorrowProtected_eq_isProtected m.activeProtectors entry

@[simp]
theorem byteRangeOverlapsWrite_toByteRangePerm
    (entry : BorrowEntry) (writeLocal writeOffset writeLen : Nat) :
    byteRangeOverlapsWrite (BorrowEntry.toByteRangePerm entry)
      writeLocal writeOffset writeLen =
      (Nat.beq entry.targetLocal writeLocal &&
        byteRangesOverlapBool entry.rangeOffset entry.rangeLen
          writeOffset writeLen) := rfl

theorem borrowEntryOverlapsWrite_eq_byteRangesOverlapBool
    (entry : BorrowEntry) (writeProj : List ProjectionElem)
    (writeRangeOff writeRangeLen : Nat)
    (h_entry_len : Nat.beq entry.rangeLen 0 = false)
    (h_write_len : Nat.beq writeRangeLen 0 = false) :
    borrowEntryOverlapsWrite entry writeProj writeRangeOff writeRangeLen =
      byteRangesOverlapBool entry.rangeOffset entry.rangeLen
        writeRangeOff writeRangeLen := by
  simp [borrowEntryOverlapsWrite, h_entry_len, h_write_len]

theorem stepForeignWriteByteRange_none_of_hasProtectedWriteConflict
    (entry : BorrowEntry) (activeProtectors : List Nat)
    (targetLocal : Local) (writeProj : List ProjectionElem)
    (writeRangeOff writeRangeLen : Nat)
    (h_entry_len : Nat.beq entry.rangeLen 0 = false)
    (h_write_len : Nat.beq writeRangeLen 0 = false)
    (h_conflict :
      hasProtectedWriteConflict [entry] activeProtectors targetLocal none
        writeProj writeRangeOff writeRangeLen = true) :
    stepForeignWriteByteRange { activeLifetimes := activeProtectors }
      (BorrowEntry.toByteRangePerm entry) targetLocal
      writeRangeOff writeRangeLen = none := by
  unfold hasProtectedWriteConflict at h_conflict
  rw [borrowEntryOverlapsWrite_eq_byteRangesOverlapBool
    entry writeProj writeRangeOff writeRangeLen h_entry_len h_write_len,
    isBorrowProtected_eq_isProtected] at h_conflict
  unfold stepForeignWriteByteRange
  rw [byteRangeOverlapsWrite_toByteRangePerm]
  cases h_loc : Nat.beq entry.targetLocal targetLocal
  · rw [h_loc] at h_conflict; exact nomatch h_conflict
  · rw [h_loc] at h_conflict
    cases h_ov : byteRangesOverlapBool entry.rangeOffset entry.rangeLen
        writeRangeOff writeRangeLen
    · rw [h_ov] at h_conflict; exact nomatch h_conflict
    · rw [h_ov] at h_conflict
      cases h_prot : (BorrowEntry.toByteRangePerm entry).isProtected
          { activeLifetimes := activeProtectors }
      · rw [h_prot] at h_conflict; exact nomatch h_conflict
      · rw [h_prot] at h_conflict
        dsimp [Bool.and]
        unfold borrowEntryWriteConflicts at h_conflict
        unfold BorrowEntry.toByteRangePerm TreeBorrowPerm.toAbstractPerm
        cases hp : entry.perm
        · rfl
        · rfl
        · rfl
        · rw [hp] at h_conflict; exact nomatch h_conflict

@[simp]
theorem updateBorrowPermAtProj_non_overlapping_unchanged
    (entry : BorrowEntry) (targetLocal : Local)
    (writeProj : List ProjectionElem) (writeRangeOff writeRangeLen : Nat)
    (h_disjoint :
      borrowEntryOverlapsWrite entry writeProj writeRangeOff writeRangeLen = false) :
    updateBorrowPermAtProj entry targetLocal none writeProj
      writeRangeOff writeRangeLen = entry := by
  unfold updateBorrowPermAtProj
  cases Nat.beq entry.targetLocal targetLocal <;> simp [h_disjoint]

theorem stepForeignWriteByteRange_agrees_with_updateBorrowPermAtProj
    (entry : BorrowEntry) (activeProtectors : List Nat)
    (targetLocal : Local) (writeProj : List ProjectionElem)
    (writeRangeOff writeRangeLen : Nat)
    (h_entry_len : Nat.beq entry.rangeLen 0 = false)
    (h_write_len : Nat.beq writeRangeLen 0 = false)
    (h_unprot : isBorrowProtected activeProtectors entry = false) :
    stepForeignWriteByteRange { activeLifetimes := activeProtectors }
      (BorrowEntry.toByteRangePerm entry) targetLocal writeRangeOff writeRangeLen =
      some (BorrowEntry.toByteRangePerm
        (updateBorrowPermAtProj entry targetLocal none writeProj
          writeRangeOff writeRangeLen)) := by
  rw [isBorrowProtected_eq_isProtected] at h_unprot
  unfold stepForeignWriteByteRange updateBorrowPermAtProj
  rw [byteRangeOverlapsWrite_toByteRangePerm,
    borrowEntryOverlapsWrite_eq_byteRangesOverlapBool
      entry writeProj writeRangeOff writeRangeLen h_entry_len h_write_len]
  cases Nat.beq entry.targetLocal targetLocal
  · rfl
  · cases byteRangesOverlapBool entry.rangeOffset entry.rangeLen
        writeRangeOff writeRangeLen
    · rfl
    · dsimp [Bool.and]
      rw [h_unprot]
      rcases entry with ⟨_, _, _, perm, _, _, _⟩
      cases perm <;> rfl

theorem disjoint_byte_range_operational_non_interference
    (entry : BorrowEntry) (activeProtectors : List Nat)
    (targetLocal : Local) (writeProj : List ProjectionElem)
    (writeRangeOff writeRangeLen : Nat)
    (h_entry_len : Nat.beq entry.rangeLen 0 = false)
    (h_write_len : Nat.beq writeRangeLen 0 = false)
    (h_disjoint : byteRangeOverlapsWrite (BorrowEntry.toByteRangePerm entry)
      targetLocal writeRangeOff writeRangeLen = false) :
    stepForeignWriteByteRange { activeLifetimes := activeProtectors }
      (BorrowEntry.toByteRangePerm entry) targetLocal writeRangeOff writeRangeLen =
      some (BorrowEntry.toByteRangePerm entry) ∧
    updateBorrowPermAtProj entry targetLocal none writeProj
      writeRangeOff writeRangeLen = entry := by
  refine ⟨disjoint_byte_range_non_interference _ _ _ _ _ h_disjoint, ?_⟩
  rw [byteRangeOverlapsWrite_toByteRangePerm] at h_disjoint
  unfold updateBorrowPermAtProj
  rw [borrowEntryOverlapsWrite_eq_byteRangesOverlapBool
    entry writeProj writeRangeOff writeRangeLen h_entry_len h_write_len]
  cases h_loc : Nat.beq entry.targetLocal targetLocal
  · rfl
  · rw [h_loc] at h_disjoint
    simp only [Bool.true_and] at h_disjoint
    dsimp only
    rw [h_disjoint]

end Anneal.Memory
