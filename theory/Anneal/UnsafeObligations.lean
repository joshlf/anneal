import Trusted
import Anneal.Memory

namespace Anneal.UnsafeObligations

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

/-!
Structured proof obligations and operational bridge theorems for `unsafe` Rust
pointer operations (`*const T`, `*mut T`, `ptr::offset`,
`intrinsics::copy_nonoverlapping`, slice splitting, unaligned raw-pointer
formation, and array-to-slice casts) (`#100`, `#103`).

Rather than unfolding low-level `MirSemantics` borrow-table and slot lookups at
every `unsafe` dereference or intrinsic call site, proof authors discharge five
named safety preconditions:

1. `AlignedPtr`: pointer offset is a multiple of the pointee alignment.
2. `LiveAllocAt`: target allocation is live and initialized at the pointer's
   offset.
3. `ValidSliceRange`: pointer offset plus slice/offset length lies within the
   allocation bounds.
4. `NonOverlappingPtrs`: source and destination pointer ranges are disjoint (or
   have zero length).
5. `HasTreeBorrowAccess`: the pointer's Tree Borrows provenance tag permits the
   requested read or write access and transitions cleanly to an updated
   `Memory`.
-/

/-- Alias for a MIR stack-frame local slot (`LocalSlot`). -/
abbrev LocalValue : Type := LocalSlot

/--
Raw pointer value pairing an allocation identifier `allocId`, byte or element
`offset`, and Tree Borrows provenance `tag`.
-/
structure RawPtrVal : Type where
  /-- Target allocation or stack-local identifier. -/
  allocId : Nat
  /-- Byte or element offset within `allocId`. -/
  offset : Nat
  /-- Tree Borrows provenance tag (defaults to `allocId`). -/
  tag : Nat := allocId
  deriving DecidableEq, Repr

/-- Project a `RawPtrVal` to `MirAst.ProvenancePtr`. -/
def RawPtrVal.toProvenancePtr (rp : RawPtrVal) : ProvenancePtr :=
  { allocId := rp.allocId, offsetBytes := rp.offset }

/-- Lift a `MirAst.ProvenancePtr` into a `RawPtrVal`. -/
def RawPtrVal.ofProvenancePtr (p : ProvenancePtr) : RawPtrVal :=
  { allocId := p.allocId, offset := p.offsetBytes, tag := p.tag }

/-! ## 1. Five Core `unsafe` Safety Obligation Propositions -/

/-- 1. Alignment obligation: `alignBytes > 0` and `rp.offset % alignBytes = 0`. -/
def AlignedPtr (rp : RawPtrVal) (alignBytes : Nat) : Prop :=
  alignBytes > 0 ∧ rp.offset % alignBytes = 0

/--
Read the initialized `Value` stored in allocation `rp.allocId` at `rp.offset`
from `locals` (at root offset `0` or aggregate element index `rp.offset`).
-/
def readAllocAt? (locals : List LocalValue) (rp : RawPtrVal) : Option Value :=
  match get? locals rp.allocId with
  | some (.init v) =>
    match rp.offset with
    | 0 => some v
    | k + 1 =>
      match v with
      | .aggregate 0 elems => get? elems (k + 1)
      | _ => none
  | _ => none

/-- Write `newVal` into allocation `rp.allocId` at `rp.offset` in `locals`. -/
def writeAllocAt?
    (locals : List LocalValue) (rp : RawPtrVal) (newVal : Value) :
    Option (List LocalValue) :=
  match rp.offset with
  | 0 =>
    match get? locals rp.allocId with
    | some (.init _) | some .uninit => set? locals rp.allocId (.init newVal)
    | _ => none
  | k + 1 =>
    match get? locals rp.allocId with
    | some (.init (.aggregate 0 elems)) =>
      match set? elems (k + 1) newVal with
      | some elems' => set? locals rp.allocId (.init (.aggregate 0 elems'))
      | none => none
    | _ => none

/--
2. Liveness and initialization obligation: allocation `rp.allocId` is live and
initialized at `rp.offset` in either `locals` or `mem.globals`.
-/
def LiveAllocAt
    (mem : Memory) (locals : List LocalValue) (rp : RawPtrVal) : Prop :=
  (∃ v, readAllocAt? locals rp = some v) ∨
  (∃ alloc,
    lookupGlobalAlloc mem.globals rp.allocId = some alloc ∧
    ∃ b, get? alloc.bytes rp.offset = some (some b))

/-- 3. In-bounds slice/offset range obligation: `rp.offset + len ≤ totalLen`. -/
def ValidSliceRange (rp : RawPtrVal) (len totalLen : Nat) : Prop :=
  rp.offset + len ≤ totalLen

/--
4. Non-overlapping pointer ranges obligation for `copy_nonoverlapping`.
-/
def NonOverlappingPtrs (src dst : RawPtrVal) (count : Nat) : Prop :=
  count = 0 ∨
  src.allocId ≠ dst.allocId ∨
  src.offset + count ≤ dst.offset ∨
  dst.offset + count ≤ src.offset

/--
Executable Tree Borrows tag transition for a read (`isWrite = false`) or write
(`isWrite = true`) through `rp`.
-/
def stepTreeBorrowAccess?
    (mem : Memory) (rp : RawPtrVal) (isWrite : Bool) : Option Memory :=
  match lookupBorrow mem.borrows rp.tag with
  | none => none
  | some entry =>
    match isWrite, entry.perm with
    | false, .disabled => none
    | false, _ => some mem
    | true, .active | true, .reserved =>
      some
        { mem with
          borrows :=
            invalidateConflictingBorrows
              mem.borrows entry.targetLocal (some rp.tag) }
    | true, .frozen | true, .disabled => none

/-- 5. Tree Borrows access obligation for read or write through `rp`. -/
def HasTreeBorrowAccess
    (mem : Memory) (rp : RawPtrVal) (isWrite : Bool) : Prop :=
  ∃ mem', stepTreeBorrowAccess? mem rp isWrite = some mem'

/-! ## 2. Operational Raw-Pointer Helpers and `MirSemantics` Bridges -/

/-- Executable alignment check corresponding to `AlignedPtr rp alignBytes`. -/
def checkAlignedBool (rp : RawPtrVal) (alignBytes : Nat) : Bool :=
  Nat.ble 1 alignBytes && (rp.offset % alignBytes == 0)

/-- Evaluate a raw-pointer load (`*rp`) under Tree Borrows and alignment checks. -/
def evalLoadRawPtr
    (mem : Memory) (locals : List LocalValue) (rp : RawPtrVal)
    (alignBytes : Nat := 1) : Option (Value × Memory) :=
  if checkAlignedBool rp alignBytes then
    match stepTreeBorrowAccess? mem rp false, readAllocAt? locals rp with
    | some mem', some v => some (v, mem')
    | _, _ => none
  else
    none

/-- Evaluate a raw-pointer store (`*rp = newVal`). -/
def evalStoreRawPtr
    (mem : Memory) (locals : List LocalValue) (rp : RawPtrVal)
    (newVal : Value) (alignBytes : Nat := 1) :
    Option (List LocalValue × Memory) :=
  if checkAlignedBool rp alignBytes then
    match stepTreeBorrowAccess? mem rp true, writeAllocAt? locals rp newVal with
    | some mem', some locals' => some (locals', mem')
    | _, _ => none
  else
    none

/-- Evaluate an in-bounds pointer offset (`rp.add(delta)`) within `totalLen`. -/
def evalPtrOffset (rp : RawPtrVal) (delta totalLen : Nat) : Option RawPtrVal :=
  if Nat.ble (rp.offset + delta) totalLen then
    some { rp with offset := rp.offset + delta }
  else
    none

theorem checkAlignedBool_of_alignedPtr
    {rp : RawPtrVal} {alignBytes : Nat}
    (h : AlignedPtr rp alignBytes) :
    checkAlignedBool rp alignBytes = true := by
  rcases h with ⟨hPos, hMod⟩
  simp [checkAlignedBool, Nat.ble_eq_true_of_le hPos, hMod]

theorem evalLoadRawPtr_of_obligations
    (mem : Memory) (locals : List LocalValue) (rp : RawPtrVal)
    (alignBytes : Nat) (v : Value)
    (hAlign : AlignedPtr rp alignBytes)
    (hTb : HasTreeBorrowAccess mem rp false)
    (hLive : readAllocAt? locals rp = some v) :
    ∃ mem', evalLoadRawPtr mem locals rp alignBytes = some (v, mem') := by
  rcases hTb with ⟨mem', hStep⟩
  exact ⟨mem', by simp [evalLoadRawPtr, checkAlignedBool_of_alignedPtr hAlign, hStep, hLive]⟩

theorem evalOperand_deref_of_obligations
    (mem : Memory) (locals : List LocalValue) (ptrLocal : Local)
    (rp : RawPtrVal) (sz : Nat) (entry : BorrowEntry) (v : Value)
    (hPtr : get? locals ptrLocal = some (.init (.ptr rp.toProvenancePtr sz)))
    (hLookup : lookupBorrow mem.borrows rp.toProvenancePtr.tag = some entry)
    (hNotDis : entry.perm ≠ .disabled)
    (hProj : entry.targetProjection = [])
    (hTarget : get? locals entry.targetLocal = some (.init v)) :
    evalOperand
      locals (.copy { local_ := ptrLocal, projection := [.deref] })
      mem.borrows mem.globals = .ok v locals := by
  unfold evalOperand
  simp only [hPtr, hLookup, hTarget, hProj]
  cases hPerm : entry.perm <;> simp_all [readProjectedValue]

theorem evalStoreRawPtr_of_obligations
    (mem : Memory) (locals locals' : List LocalValue) (rp : RawPtrVal)
    (newVal : Value) (alignBytes : Nat)
    (hAlign : AlignedPtr rp alignBytes)
    (hTb : HasTreeBorrowAccess mem rp true)
    (hWrite : writeAllocAt? locals rp newVal = some locals') :
    ∃ mem', evalStoreRawPtr mem locals rp newVal alignBytes = some (locals', mem') := by
  rcases hTb with ⟨mem', hStep⟩
  exact ⟨mem', by simp [evalStoreRawPtr, checkAlignedBool_of_alignedPtr hAlign, hStep, hWrite]⟩

theorem writePlaceValue_deref_of_obligations
    (mem : Memory) (locals locals' : List LocalValue) (ptrLocal : Local)
    (rp : RawPtrVal) (sz : Nat) (entry : BorrowEntry) (oldVal newVal : Value)
    (hPtr : get? locals ptrLocal = some (.init (.ptr rp.toProvenancePtr sz)))
    (hLookup : lookupBorrow mem.borrows rp.toProvenancePtr.tag = some entry)
    (hWritable : entry.perm = .active ∨ entry.perm = .reserved)
    (hProj : entry.targetProjection = [])
    (hTarget : get? locals entry.targetLocal = some (.init oldVal))
    (hSet : set? locals entry.targetLocal (.init newVal) = some locals') :
    writePlaceValue
      locals mem.borrows { local_ := ptrLocal, projection := [.deref] }
      newVal = .ok locals' := by
  unfold writePlaceValue
  rcases hWritable with hAct | hRes
  · simp [hPtr, hLookup, hAct, hProj, hTarget, hSet]
  · simp [hPtr, hLookup, hRes, hProj, hTarget, hSet]

theorem evalPtrOffset_of_validSliceRange
    (rp : RawPtrVal) (delta totalLen : Nat)
    (hRange : ValidSliceRange rp delta totalLen) :
    evalPtrOffset rp delta totalLen =
      some { rp with offset := rp.offset + delta } := by
  simp [evalPtrOffset, Nat.ble_eq_true_of_le hRange]

theorem evalRvalue_offset_of_validSliceRange
    (locals : List LocalValue) (mem : Memory) (localDecls : List LocalDecl)
    (lhsOp rhsOp : Operand) (rp : RawPtrVal) (sz delta totalLen : Nat)
    (hRange : ValidSliceRange rp delta totalLen)
    (hLhs :
      evalOperand locals lhsOp mem.borrows mem.globals emptyLayoutTable mem.callerLocals =
        .ok (.ptr rp.toProvenancePtr sz) locals)
    (hRhs :
      evalOperand locals rhsOp mem.borrows mem.globals emptyLayoutTable mem.callerLocals =
        .ok (.scalar ⟨delta, 8⟩) locals) :
    evalRvalue locals (.binaryOp .offset lhsOp rhsOp) mem localDecls =
      .ok (.ptr { rp.toProvenancePtr with
                  offsetBytes := rp.toProvenancePtr.offsetBytes + delta } sz)
          locals mem ∧
    rp.offset + delta ≤ totalLen := by
  refine ⟨?_, hRange⟩
  unfold evalRvalue
  simp [hLhs, hRhs]

theorem nonOverlappingPtrs_zero (src dst : RawPtrVal) :
    NonOverlappingPtrs src dst 0 :=
  Or.inl rfl

theorem nonOverlappingPtrs_of_ne_alloc
    {src dst : RawPtrVal} (count : Nat) (hNe : src.allocId ≠ dst.allocId) :
    NonOverlappingPtrs src dst count :=
  Or.inr (Or.inl hNe)

/--
Bridge theorem connecting `NonOverlappingPtrs src dst 0` directly to
`MirSemantics.evalCopyNonOverlapping` when `count` evaluates to `0`.
-/
theorem evalCopyNonOverlapping_zero_of_obligations
    (s : MachineState) (srcOp dstOp countOp : Operand)
    (src dst : RawPtrVal) (srcVal dstVal : Value)
    (hNonoverlap : NonOverlappingPtrs src dst 0)
    (hSrc :
      evalOperand s.frame.locals srcOp s.memory.borrows s.memory.globals emptyLayoutTable s.memory.callerLocals =
        .ok srcVal s.frame.locals)
    (hDst :
      evalOperand s.frame.locals dstOp s.memory.borrows s.memory.globals emptyLayoutTable s.memory.callerLocals =
        .ok dstVal s.frame.locals)
    (hCnt :
      evalOperand s.frame.locals countOp s.memory.borrows s.memory.globals emptyLayoutTable s.memory.callerLocals =
        .ok (.scalar ⟨0, 8⟩) s.frame.locals) :
    evalCopyNonOverlapping s srcOp dstOp countOp =
      MirStepNode.step (advanceStmt s s.frame.locals) ∧
    NonOverlappingPtrs src dst 0 := by
  refine ⟨?_, hNonoverlap⟩
  unfold evalCopyNonOverlapping evalCopyNonOverlappingWithCount
  simp [hSrc, hDst, hCnt]

/--
Bridge theorem connecting `NonOverlappingPtrs`, `HasTreeBorrowAccess`, and
`LiveAllocAt` directly to `MirSemantics.evalCopyNonOverlapping` for `count = 1`
at base offset `0`.
-/
theorem evalCopyNonOverlapping_one_of_obligations
    (s : MachineState) (srcOp dstOp countOp : Operand)
    (src dst : RawPtrVal) (sz : Nat) (srcEntry dstEntry : BorrowEntry)
    (copiedVal oldDstVal : Value) (locals' : List LocalValue)
    (hNonoverlap : NonOverlappingPtrs src dst 1)
    (hSrcOff : src.offset = 0)
    (hDstOff : dst.offset = 0)
    (hSrc :
      evalOperand s.frame.locals srcOp s.memory.borrows s.memory.globals emptyLayoutTable s.memory.callerLocals =
        .ok (.ptr src.toProvenancePtr sz) s.frame.locals)
    (hDst :
      evalOperand s.frame.locals dstOp s.memory.borrows s.memory.globals emptyLayoutTable s.memory.callerLocals =
        .ok (.ptr dst.toProvenancePtr sz) s.frame.locals)
    (hCnt :
      evalOperand s.frame.locals countOp s.memory.borrows s.memory.globals emptyLayoutTable s.memory.callerLocals =
        .ok (.scalar ⟨1, 8⟩) s.frame.locals)
    (hSrcPt : operandPointeeTy [] emptyLayoutTable srcOp = none)
    (hSrcLookup :
      lookupBorrow s.memory.borrows src.toProvenancePtr.tag = some srcEntry)
    (hDstLookup :
      lookupBorrow s.memory.borrows dst.toProvenancePtr.tag = some dstEntry)
    (hSrcPerm : srcEntry.perm = .frozen)
    (hDstPerm : dstEntry.perm = .active)
    (hTagNe : Nat.beq src.toProvenancePtr.tag dst.toProvenancePtr.tag = false)
    (hLocNe : Nat.beq srcEntry.targetLocal dstEntry.targetLocal = false)
    (hSrcProj : srcEntry.targetProjection = [])
    (hDstProj : dstEntry.targetProjection = [])
    (hSrcVal : get? s.frame.locals srcEntry.targetLocal = some (.init copiedVal))
    (hDstVal : get? s.frame.locals dstEntry.targetLocal = some (.init oldDstVal))
    (hWrite :
      set? s.frame.locals dstEntry.targetLocal (.init copiedVal) =
        some locals') :
    evalCopyNonOverlapping s srcOp dstOp countOp =
      MirStepNode.step
        (advanceStmt s locals'
          { s.memory with
            borrows :=
              invalidateConflictingBorrows
                s.memory.borrows dstEntry.targetLocal
                (some dst.toProvenancePtr.tag) }) ∧
    NonOverlappingPtrs src dst 1 := by
  refine ⟨?_, hNonoverlap⟩
  have hSrcZero : src.toProvenancePtr.offsetBytes = 0 := hSrcOff
  have hDstZero : dst.toProvenancePtr.offsetBytes = 0 := hDstOff
  unfold evalCopyNonOverlapping evalCopyNonOverlappingWithCount
    evalCopySingleDirect writePlaceValue
  simp [hSrc, hDst, hCnt, hSrcLookup, hDstLookup, hSrcPerm, hDstPerm,
        hSrcZero, hDstZero, hTagNe, hLocNe, hSrcVal, hSrcProj, hSrcPt,
        hDstProj, hDstVal, hWrite, readProjectedValue]

/-! ## 3. Slice-Split, Unaligned Raw-Pointer, and Array-to-Slice Obligations -/

/--
Right sub-slice raw pointer produced by `split_at_unchecked(mid)`: advances
`rp.offset` by `mid * elemSize` bytes while preserving `allocId` and `tag`.
-/
def sliceSplitRightPtr (rp : RawPtrVal) (elemSize mid : Nat) : RawPtrVal :=
  { allocId := rp.allocId, offset := rp.offset + mid * elemSize, tag := rp.tag }

/-- Safety precondition obligation for splitting a slice at `mid`. -/
def ValidSliceSplit
    (rp : RawPtrVal) (elemSize totalLen mid rightLen : Nat) : Prop :=
  ValidSliceRange rp (totalLen * elemSize) (rp.offset + totalLen * elemSize) ∧
  mid + rightLen = totalLen ∧
  ValidSliceRange rp (mid * elemSize) (rp.offset + totalLen * elemSize) ∧
  ValidSliceRange (sliceSplitRightPtr rp elemSize mid)
    (rightLen * elemSize) (rp.offset + totalLen * elemSize)

theorem validSliceSplit_full
    {rp : RawPtrVal} {elemSize totalLen mid rightLen : Nat}
    (h : ValidSliceSplit rp elemSize totalLen mid rightLen) :
    ValidSliceRange rp (totalLen * elemSize) (rp.offset + totalLen * elemSize) :=
  h.1

theorem validSliceSplit_partition
    {rp : RawPtrVal} {elemSize totalLen mid rightLen : Nat}
    (h : ValidSliceSplit rp elemSize totalLen mid rightLen) :
    mid + rightLen = totalLen :=
  h.2.1

theorem validSliceSplit_left
    {rp : RawPtrVal} {elemSize totalLen mid rightLen : Nat}
    (h : ValidSliceSplit rp elemSize totalLen mid rightLen) :
    ValidSliceRange rp (mid * elemSize) (rp.offset + totalLen * elemSize) :=
  h.2.2.1

theorem validSliceSplit_right
    {rp : RawPtrVal} {elemSize totalLen mid rightLen : Nat}
    (h : ValidSliceSplit rp elemSize totalLen mid rightLen) :
    ValidSliceRange (sliceSplitRightPtr rp elemSize mid)
      (rightLen * elemSize) (rp.offset + totalLen * elemSize) :=
  h.2.2.2

theorem evalPtrOffset_of_validSliceSplit
    {rp : RawPtrVal} {elemSize totalLen mid rightLen : Nat}
    (h : ValidSliceSplit rp elemSize totalLen mid rightLen) :
    evalPtrOffset rp (mid * elemSize) (rp.offset + totalLen * elemSize) =
      some (sliceSplitRightPtr rp elemSize mid) :=
  evalPtrOffset_of_validSliceRange _ _ _ (validSliceSplit_left h)

theorem validSliceSplit_disjoint
    {rp : RawPtrVal} {elemSize totalLen mid rightLen : Nat}
    (_h : ValidSliceSplit rp elemSize totalLen mid rightLen) :
    NonOverlappingPtrs rp (sliceSplitRightPtr rp elemSize mid) (mid * elemSize) :=
  Or.inr (Or.inr (Or.inl (Nat.le_refl _)))

theorem validSliceSplit_disjoint_symm
    {rp : RawPtrVal} {elemSize totalLen mid rightLen : Nat}
    (_h : ValidSliceSplit rp elemSize totalLen mid rightLen) :
    NonOverlappingPtrs (sliceSplitRightPtr rp elemSize mid) rp (mid * elemSize) :=
  Or.inr (Or.inr (Or.inr (Nat.le_refl _)))

/--
Safety precondition obligation for forming an unaligned raw pointer via
`Unalign::<T>::{get_ptr, get_mut_ptr}`.
-/
def UnalignRawPtrSafe (rp : RawPtrVal) (innerSize allocLen : Nat) : Prop :=
  AlignedPtr rp 1 ∧ ValidSliceRange rp innerSize allocLen

theorem alignedPtr_one (rp : RawPtrVal) : AlignedPtr rp 1 :=
  ⟨by omega, Nat.mod_one rp.offset⟩

theorem unalignRawPtrSafe_of_validSliceRange
    {rp : RawPtrVal} {innerSize allocLen : Nat}
    (hRange : ValidSliceRange rp innerSize allocLen) :
    UnalignRawPtrSafe rp innerSize allocLen :=
  ⟨alignedPtr_one rp, hRange⟩

theorem evalPtrOffset_zero_of_unalignRawPtrSafe
    {rp : RawPtrVal} {innerSize allocLen : Nat}
    (hSafe : UnalignRawPtrSafe rp innerSize allocLen) :
    evalPtrOffset rp 0 allocLen = some rp :=
  evalPtrOffset_of_validSliceRange rp 0 allocLen (by
    have := hSafe.2; unfold ValidSliceRange at *; omega)

/--
Safety precondition obligation for casting a thin array pointer `[T; arrayLen]`
into a wide slice pointer (`PtrInner::<[T; N]>::as_slice`).
-/
def ValidArrayToSliceCast
    (rp : RawPtrVal) (elemSize elemAlign arrayLen allocLen : Nat) : Prop :=
  AlignedPtr rp elemAlign ∧
  ValidSliceRange rp (arrayLen * elemSize) allocLen

def arrayToSliceWidePtr (rp : RawPtrVal) (arrayLen : Nat) : Value :=
  .ptr rp.toProvenancePtr arrayLen

theorem validArrayToSliceCast_aligned
    {rp : RawPtrVal} {elemSize elemAlign arrayLen allocLen : Nat}
    (h : ValidArrayToSliceCast rp elemSize elemAlign arrayLen allocLen) :
    AlignedPtr rp elemAlign :=
  h.1

theorem validArrayToSliceCast_inBounds
    {rp : RawPtrVal} {elemSize elemAlign arrayLen allocLen : Nat}
    (h : ValidArrayToSliceCast rp elemSize elemAlign arrayLen allocLen) :
    ValidSliceRange rp (arrayLen * elemSize) allocLen :=
  h.2

theorem evalPtrOffset_end_of_validArrayToSliceCast
    {rp : RawPtrVal} {elemSize elemAlign arrayLen allocLen : Nat}
    (h : ValidArrayToSliceCast rp elemSize elemAlign arrayLen allocLen) :
    evalPtrOffset rp (arrayLen * elemSize) allocLen =
      some { rp with offset := rp.offset + arrayLen * elemSize } :=
  evalPtrOffset_of_validSliceRange _ _ _ (validArrayToSliceCast_inBounds h)

end Anneal.UnsafeObligations
