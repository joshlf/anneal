import Trusted
import Anneal.Memory
import Anneal.FaultSiteCensus

namespace Anneal.UnsafeObligations

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Anneal.FaultSiteCensus

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
(`isWrite = true`) through `rp`. A write invalidates conflicting borrows of the
written local in the frame that owns it (`entry.targetFrameDepth`).
-/
def stepTreeBorrowAccess?
    (mem : Memory) (rp : RawPtrVal) (isWrite : Bool) : Option Memory :=
  match lookupBorrow mem.borrows rp.tag with
  | none => none
  | some entry =>
    match isWrite, entry.perm with
    | false, .disabled => none
    | false, _ => some mem
    | true, .frozen | true, .disabled => none
    | true, _ =>
      some
        { mem with
          borrows :=
            invalidateConflictingBorrows
              mem.borrows entry.targetLocal (some rp.tag) entry.targetFrameDepth }

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
  unfold checkAlignedBool
  rw [Nat.ble_eq_true_of_le hPos, Bool.true_and, beq_iff_eq]
  exact hMod

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
  simp only [hPtr, hLookup, hProj]
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
      evalOperand locals lhsOp mem.borrows mem.globals emptyLayoutTable mem.callerLocals localDecls
          mem.callStack =
        .ok (.ptr rp.toProvenancePtr sz) locals)
    (hRhs :
      evalOperand locals rhsOp mem.borrows mem.globals emptyLayoutTable mem.callerLocals localDecls
          mem.callStack =
        .ok (.scalar ⟨delta, 8⟩) locals)
    (hStride : pointeeElemByteStride localDecls emptyLayoutTable lhsOp = .some 1)
    (hOffset :
      evalBinOpOffset rp.toProvenancePtr sz ⟨delta, 8⟩ 1
        (ptrAllocByteBound? locals mem localDecls emptyLayoutTable rp.toProvenancePtr) =
        .some { rp.toProvenancePtr with
                offsetBytes := rp.toProvenancePtr.offsetBytes + delta }) :
    evalRvalue locals (.binaryOp .offset lhsOp rhsOp) mem localDecls =
      .ok (.ptr { rp.toProvenancePtr with
                  offsetBytes := rp.toProvenancePtr.offsetBytes + delta } sz)
          locals mem ∧
    rp.offset + delta ≤ totalLen := by
  refine ⟨?_, hRange⟩
  unfold evalRvalue evalPtrOffsetBinOp
  simp [hLhs, hRhs, hStride, hOffset]

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
      evalOperand s.frame.locals srcOp s.memory.borrows s.memory.globals emptyLayoutTable s.memory.callerLocals
          (callStack := s.memory.callStack) =
        .ok srcVal s.frame.locals)
    (hDst :
      evalOperand s.frame.locals dstOp s.memory.borrows s.memory.globals emptyLayoutTable s.memory.callerLocals
          (callStack := s.memory.callStack) =
        .ok dstVal s.frame.locals)
    (hCnt :
      evalOperand s.frame.locals countOp s.memory.borrows s.memory.globals emptyLayoutTable s.memory.callerLocals
          (callStack := s.memory.callStack) =
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

`hFrame` requires both borrow targets to lie in the active frame
(`copyEntriesTargetActiveFrame`, which holds trivially when the root frame is
active, i.e. `s.memory.callStack = []`); a copy through a tag minted in a
suspended caller frame fails closed with `.unsupported`
(`DIV-MR-CALL-TARGET-LOCAL`). The destination invalidation is scoped to the
active frame depth `length s.memory.callStack`.
-/
theorem evalCopyNonOverlapping_one_of_obligations
    (s : MachineState) (srcOp dstOp countOp : Operand)
    (src dst : RawPtrVal) (sz : Nat) (srcEntry dstEntry : BorrowEntry)
    (copiedVal oldDstVal : Value) (locals' : List LocalValue)
    (hNonoverlap : NonOverlappingPtrs src dst 1)
    (hSrcOff : src.offset = 0)
    (hDstOff : dst.offset = 0)
    (hSrc :
      evalOperand s.frame.locals srcOp s.memory.borrows s.memory.globals emptyLayoutTable s.memory.callerLocals
          (callStack := s.memory.callStack) =
        .ok (.ptr src.toProvenancePtr sz) s.frame.locals)
    (hDst :
      evalOperand s.frame.locals dstOp s.memory.borrows s.memory.globals emptyLayoutTable s.memory.callerLocals
          (callStack := s.memory.callStack) =
        .ok (.ptr dst.toProvenancePtr sz) s.frame.locals)
    (hCnt :
      evalOperand s.frame.locals countOp s.memory.borrows s.memory.globals emptyLayoutTable s.memory.callerLocals
          (callStack := s.memory.callStack) =
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
        some locals')
    (hFrame :
      copyEntriesTargetActiveFrame s.memory.callStack srcEntry dstEntry = true) :
    evalCopyNonOverlapping s srcOp dstOp countOp =
      MirStepNode.step
        (advanceStmt s locals'
          { s.memory with
            borrows :=
              invalidateConflictingBorrows
                s.memory.borrows dstEntry.targetLocal
                (some dst.toProvenancePtr.tag)
                (length s.memory.callStack) }) ∧
    NonOverlappingPtrs src dst 1 := by
  refine ⟨?_, hNonoverlap⟩
  have hSrcZero : src.toProvenancePtr.offsetBytes = 0 := hSrcOff
  have hDstZero : dst.toProvenancePtr.offsetBytes = 0 := hDstOff
  unfold evalCopyNonOverlapping evalCopyNonOverlappingWithCount
    evalCopyNonOverlappingPermOk evalCopySingleDirect writePlaceValue
  simp [hSrc, hDst, hCnt, hSrcLookup, hDstLookup, hSrcPerm, hDstPerm,
        hSrcZero, hDstZero, hTagNe, hLocNe, hSrcVal, hSrcProj, hSrcPt,
        hDstProj, hDstVal, hWrite, hFrame, readProjectedValue]

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

/-! ## 4. `MirFaultClass` Taxonomy & Fault-Site Coverage Bridge Theorems -/

/--
Enumeration of the five named `unsafe` safety obligations in `Anneal.UnsafeObligations`.
-/
inductive UnsafeObligationKind : Type where
  /-- 1. `AlignedPtr`: pointer offset is aligned for the pointee layout. -/
  | alignedPtr : UnsafeObligationKind
  /-- 2. `LiveAllocAt`: target allocation is live and initialized at the pointer offset. -/
  | liveAllocAt : UnsafeObligationKind
  /-- 3. `ValidSliceRange`: pointer offset plus slice/offset length lies in bounds. -/
  | validSliceRange : UnsafeObligationKind
  /-- 4. `NonOverlappingPtrs`: source and destination pointer ranges are disjoint. -/
  | nonOverlappingPtrs : UnsafeObligationKind
  /-- 5. `HasTreeBorrowAccess`: Tree Borrows provenance tag permits the access. -/
  | hasTreeBorrowAccess : UnsafeObligationKind
  deriving DecidableEq, Repr, BEq, Inhabited

/--
Canonical mapping from each of the five `unsafe` safety obligation kinds to the
`MirFaultClass` categories in `Anneal.FaultSiteCensus` that it discharges.
-/
def unsafeObligationFaultClasses : UnsafeObligationKind → List MirFaultClass
  | .alignedPtr => [.ptrAlignMismatch]
  | .liveAllocAt => [.ptrDerefInvalid, .uninitRead, .storageLiveProtected]
  | .validSliceRange => [.arithOverflow, .boundsCheck]
  | .nonOverlappingPtrs => [.ptrDerefInvalid, .treeBorrowsViolation]
  | .hasTreeBorrowAccess => [.treeBorrowsViolation]

/--
Every `MirFaultClass` emitted by `censusProjectionElemFaultClasses .deref`
is covered by `{.alignedPtr, .liveAllocAt, .hasTreeBorrowAccess}`.
-/
theorem deref_faultClasses_subset_unsafeObligations :
    ∀ cls ∈ censusProjectionElemFaultClasses .deref,
      cls ∈ unsafeObligationFaultClasses .alignedPtr ++
            unsafeObligationFaultClasses .liveAllocAt ++
            unsafeObligationFaultClasses .hasTreeBorrowAccess := by
  decide

/--
Every `MirFaultClass` emitted by `censusBinOpFaultClasses .offset`
is covered by `{.validSliceRange, .liveAllocAt, .hasTreeBorrowAccess}`.
-/
theorem offset_faultClasses_subset_unsafeObligations :
    ∀ cls ∈ censusBinOpFaultClasses .offset,
      cls ∈ unsafeObligationFaultClasses .validSliceRange ++
            unsafeObligationFaultClasses .liveAllocAt ++
            unsafeObligationFaultClasses .hasTreeBorrowAccess := by
  decide

/--
Bridge theorem tying `evalOperand_deref_of_obligations` to non-`.ub` execution
and the exact fault-class census of a dereferencing operand read
(`Operand.copy { local_ := ptrLocal, projection := [.deref] }`).
-/
theorem evalOperand_deref_ne_ub_and_census_of_obligations
    (mem : Memory) (locals : List LocalValue) (ptrLocal : Local)
    (rp : RawPtrVal) (sz : Nat) (entry : BorrowEntry) (v : Value)
    (hPtr : get? locals ptrLocal = some (.init (.ptr rp.toProvenancePtr sz)))
    (hLookup : lookupBorrow mem.borrows rp.toProvenancePtr.tag = some entry)
    (hNotDis : entry.perm ≠ .disabled)
    (hProj : entry.targetProjection = [])
    (hTarget : get? locals entry.targetLocal = some (.init v)) :
    let op : Operand := .copy { local_ := ptrLocal, projection := [.deref] }
    evalOperand locals op mem.borrows mem.globals ≠ .ub ∧
    dedupFaultClasses (censusOperandFaultClasses op) =
      [.ptrDerefInvalid, .ptrAlignMismatch, .treeBorrowsViolation, .uninitRead] := by
  have hOk := evalOperand_deref_of_obligations
    mem locals ptrLocal rp sz entry v hPtr hLookup hNotDis hProj hTarget
  refine ⟨?_, rfl⟩
  rw [hOk]
  intro hUb
  nomatch hUb

/--
Bridge theorem tying `writePlaceValue_deref_of_obligations` to non-`.ub` execution
and the exact fault-class census of a dereferencing place write
(`{ local_ := ptrLocal, projection := [.deref] }`).
-/
theorem writePlaceValue_deref_ne_ub_and_census_of_obligations
    (mem : Memory) (locals locals' : List LocalValue) (ptrLocal : Local)
    (rp : RawPtrVal) (sz : Nat) (entry : BorrowEntry) (oldVal newVal : Value)
    (hPtr : get? locals ptrLocal = some (.init (.ptr rp.toProvenancePtr sz)))
    (hLookup : lookupBorrow mem.borrows rp.toProvenancePtr.tag = some entry)
    (hWritable : entry.perm = .active ∨ entry.perm = .reserved)
    (hProj : entry.targetProjection = [])
    (hTarget : get? locals entry.targetLocal = some (.init oldVal))
    (hSet : set? locals entry.targetLocal (.init newVal) = some locals') :
    let dst : Place := { local_ := ptrLocal, projection := [.deref] }
    writePlaceValue locals mem.borrows dst newVal ≠ .ub ∧
    dedupFaultClasses (censusPlaceWriteFaultClasses dst) =
      [.ptrDerefInvalid, .ptrAlignMismatch, .treeBorrowsViolation, .uninitRead,
       .storageLiveProtected] := by
  have hOk := writePlaceValue_deref_of_obligations
    mem locals locals' ptrLocal rp sz entry oldVal newVal
    hPtr hLookup hWritable hProj hTarget hSet
  refine ⟨?_, rfl⟩
  rw [hOk]
  intro hUb
  nomatch hUb

/--
Bridge theorem tying `evalRvalue_offset_of_validSliceRange` to non-`.ub` execution
and the exact `BinOp.offset` fault-class census.
-/
theorem evalRvalue_offset_ne_ub_and_census_of_validSliceRange
    (locals : List LocalValue) (mem : Memory) (localDecls : List LocalDecl)
    (lhsOp rhsOp : Operand) (rp : RawPtrVal) (sz delta totalLen : Nat)
    (hRange : ValidSliceRange rp delta totalLen)
    (hLhs :
      evalOperand locals lhsOp mem.borrows mem.globals emptyLayoutTable mem.callerLocals localDecls
          mem.callStack =
        .ok (.ptr rp.toProvenancePtr sz) locals)
    (hRhs :
      evalOperand locals rhsOp mem.borrows mem.globals emptyLayoutTable mem.callerLocals localDecls
          mem.callStack =
        .ok (.scalar ⟨delta, 8⟩) locals)
    (hStride : pointeeElemByteStride localDecls emptyLayoutTable lhsOp = .some 1)
    (hOffset :
      evalBinOpOffset rp.toProvenancePtr sz ⟨delta, 8⟩ 1
        (ptrAllocByteBound? locals mem localDecls emptyLayoutTable rp.toProvenancePtr) =
        .some { rp.toProvenancePtr with
                offsetBytes := rp.toProvenancePtr.offsetBytes + delta }) :
    evalRvalue locals (.binaryOp .offset lhsOp rhsOp) mem localDecls ≠ .ub ∧
    ValidSliceRange rp delta totalLen ∧
    censusBinOpFaultClasses .offset =
      [.arithOverflow, .boundsCheck, .ptrDerefInvalid, .treeBorrowsViolation] := by
  have hEv := (evalRvalue_offset_of_validSliceRange
    locals mem localDecls lhsOp rhsOp rp sz delta totalLen
    hRange hLhs hRhs hStride hOffset).1
  refine ⟨?_, hRange, rfl⟩
  rw [hEv]
  intro hUb
  nomatch hUb

/--
`[adv ep1-B3]` Statement-level bridge theorem tying `evalOperand_deref_of_obligations`
to `evalOperand ≠ .ub` and `reconcileFaultCoverageWithRegistry` discharge of all
deref-load and destination-write `MirFaultClass`es at `(blockIdx, stmtIdx)`.
-/
theorem evalOperand_deref_reconciled_of_obligations
    (mem : Memory) (locals : List LocalValue) (dstLocal ptrLocal : Local) (span : String)
    (blockIdx : BasicBlockIdx) (stmtIdx : Nat)
    (registry : PropertyRegistry) (discharged : List FaultSite)
    (rp : RawPtrVal) (sz : Nat) (entry : BorrowEntry) (v : Value)
    (hPtr : get? locals ptrLocal = some (.init (.ptr rp.toProvenancePtr sz)))
    (hLookup : lookupBorrow mem.borrows rp.toProvenancePtr.tag = some entry)
    (hNotDis : entry.perm ≠ .disabled)
    (hProj : entry.targetProjection = [])
    (hTarget : get? locals entry.targetLocal = some (.init v))
    (hRec :
      reconcileFaultCoverageWithRegistry registry
        (censusStmtFaultSites blockIdx stmtIdx
          ⟨.assign { local_ := dstLocal, projection := [] }
            (.use (.copy { local_ := ptrLocal, projection := [.deref] })), span⟩)
        discharged = .verified) :
    evalOperand locals (.copy { local_ := ptrLocal, projection := [.deref] })
      mem.borrows mem.globals ≠ .ub ∧
    ∀ cls ∈ [MirFaultClass.ptrDerefInvalid, .ptrAlignMismatch, .treeBorrowsViolation,
              .uninitRead, .storageLiveProtected],
      (blockIdx, stmtIdx, cls) ∈ discharged ∧ registry cls = .emittedAndVerified := by
  have hNeUb := (evalOperand_deref_ne_ub_and_census_of_obligations
    mem locals ptrLocal rp sz entry v hPtr hLookup hNotDis hProj hTarget).1
  refine ⟨hNeUb, ?_⟩
  intro cls hCls
  have hInStmt : cls ∈ censusStmtFaultClasses
      (.assign { local_ := dstLocal, projection := [] }
        (.use (.copy { local_ := ptrLocal, projection := [.deref] }))) := by
    have hEq : censusStmtFaultClasses
        (.assign { local_ := dstLocal, projection := [] }
          (.use (.copy { local_ := ptrLocal, projection := [.deref] }))) =
        [.ptrDerefInvalid, .ptrAlignMismatch, .treeBorrowsViolation,
         .scalarNicheInvalid, .uninitRead, .storageLiveProtected] := rfl
    rw [hEq]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hCls
    rcases hCls with rfl | rfl | rfl | rfl | rfl <;> decide
  have hInSites : (blockIdx, stmtIdx, cls) ∈
      censusStmtFaultSites blockIdx stmtIdx
        ⟨.assign { local_ := dstLocal, projection := [] }
          (.use (.copy { local_ := ptrLocal, projection := [.deref] })), span⟩ := by
    simp only [censusStmtFaultSites, List.mem_map]
    exact ⟨cls, hInStmt, rfl⟩
  exact (reconcileFaultCoverageWithRegistry_verified_iff registry _ discharged).mp
    hRec (blockIdx, stmtIdx, cls) hInSites

/--
`[adv ep1-B3]` Statement-level bridge theorem tying `writePlaceValue_deref_of_obligations`
to `writePlaceValue ≠ .ub` and `reconcileFaultCoverageWithRegistry` discharge of all
deref-store `MirFaultClass`es at `(blockIdx, stmtIdx)`.
-/
theorem writePlaceValue_deref_reconciled_of_obligations
    (mem : Memory) (locals locals' : List LocalValue) (ptrLocal : Local)
    (rv : Rvalue) (span : String)
    (blockIdx : BasicBlockIdx) (stmtIdx : Nat)
    (registry : PropertyRegistry) (discharged : List FaultSite)
    (rp : RawPtrVal) (sz : Nat) (entry : BorrowEntry) (oldVal newVal : Value)
    (hEvalRv : rvalueUnevaluated rv = false)
    (hPtr : get? locals ptrLocal = some (.init (.ptr rp.toProvenancePtr sz)))
    (hLookup : lookupBorrow mem.borrows rp.toProvenancePtr.tag = some entry)
    (hWritable : entry.perm = .active ∨ entry.perm = .reserved)
    (hProj : entry.targetProjection = [])
    (hTarget : get? locals entry.targetLocal = some (.init oldVal))
    (hSet : set? locals entry.targetLocal (.init newVal) = some locals')
    (hRec :
      reconcileFaultCoverageWithRegistry registry
        (censusStmtFaultSites blockIdx stmtIdx
          ⟨.assign { local_ := ptrLocal, projection := [.deref] } rv, span⟩)
        discharged = .verified) :
    writePlaceValue locals mem.borrows { local_ := ptrLocal, projection := [.deref] } newVal ≠ .ub ∧
    ∀ cls ∈ [MirFaultClass.ptrDerefInvalid, .ptrAlignMismatch, .treeBorrowsViolation,
              .uninitRead, .storageLiveProtected],
      (blockIdx, stmtIdx, cls) ∈ discharged ∧ registry cls = .emittedAndVerified := by
  have hNeUb := (writePlaceValue_deref_ne_ub_and_census_of_obligations
    mem locals locals' ptrLocal rp sz entry oldVal newVal
    hPtr hLookup hWritable hProj hTarget hSet).1
  refine ⟨hNeUb, ?_⟩
  intro cls hCls
  have hInWrite : cls ∈ censusPlaceWriteFaultClasses
      { local_ := ptrLocal, projection := [.deref] } := by
    dsimp only [censusPlaceWriteFaultClasses, censusProjectionElemFaultClasses]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hCls
    rcases hCls with rfl | rfl | rfl | rfl | rfl <;> decide
  have hInStmt : cls ∈ censusStmtFaultClasses
      (.assign { local_ := ptrLocal, projection := [.deref] } rv) := by
    dsimp only [censusStmtFaultClasses]
    rw [hEvalRv, mem_dedupFaultClasses_iff]
    exact List.mem_append_left _ hInWrite
  have hInSites : (blockIdx, stmtIdx, cls) ∈
      censusStmtFaultSites blockIdx stmtIdx
        ⟨.assign { local_ := ptrLocal, projection := [.deref] } rv, span⟩ := by
    simp only [censusStmtFaultSites, List.mem_map]
    exact ⟨cls, hInStmt, rfl⟩
  exact (reconcileFaultCoverageWithRegistry_verified_iff registry _ discharged).mp
    hRec (blockIdx, stmtIdx, cls) hInSites

/--
`[adv ep1-B3]` Statement-level bridge theorem tying `evalRvalue_offset_of_validSliceRange`
to non-`.ub` statement execution (`¬ StepNodeExposesUb`) and `reconcileFaultCoverageWithRegistry`
discharge of all pointer-offset and destination-write `MirFaultClass`es at `(blockIdx, stmtIdx)`.
-/
theorem evalStmt_offset_reconciled_of_validSliceRange
    (s : MachineState) (localDecls : List LocalDecl) (dstLocal : Local)
    (lhsOp rhsOp : Operand) (span : String)
    (blockIdx : BasicBlockIdx) (stmtIdx : Nat)
    (registry : PropertyRegistry) (discharged : List FaultSite)
    (rp : RawPtrVal) (sz delta totalLen : Nat) (locals' : List LocalValue)
    (hRange : ValidSliceRange rp delta totalLen)
    (hLhs :
      evalOperand s.frame.locals lhsOp s.memory.borrows s.memory.globals emptyLayoutTable
          s.memory.callerLocals localDecls s.memory.callStack =
        .ok (.ptr rp.toProvenancePtr sz) s.frame.locals)
    (hRhs :
      evalOperand s.frame.locals rhsOp s.memory.borrows s.memory.globals emptyLayoutTable
          s.memory.callerLocals localDecls s.memory.callStack =
        .ok (.scalar ⟨delta, 8⟩) s.frame.locals)
    (hStride : pointeeElemByteStride localDecls emptyLayoutTable lhsOp = .some 1)
    (hOffset :
      evalBinOpOffset rp.toProvenancePtr sz ⟨delta, 8⟩ 1
        (ptrAllocByteBound? s.frame.locals s.memory localDecls emptyLayoutTable rp.toProvenancePtr) =
        .some { rp.toProvenancePtr with
                offsetBytes := rp.toProvenancePtr.offsetBytes + delta })
    (hDstSlot : get? s.frame.locals dstLocal = some .uninit)
    (hSet :
      set? s.frame.locals dstLocal
        (.init (.ptr { rp.toProvenancePtr with
                       offsetBytes := rp.toProvenancePtr.offsetBytes + delta } sz)) =
        some locals')
    (hNoProt : s.memory.activeProtectors = [])
    (hRec :
      reconcileFaultCoverageWithRegistry registry
        (censusStmtFaultSites blockIdx stmtIdx
          ⟨.assign { local_ := dstLocal, projection := [] } (.binaryOp .offset lhsOp rhsOp), span⟩)
        discharged = .verified) :
    ¬ StepNodeExposesUb
        (evalStmt s
          ⟨.assign { local_ := dstLocal, projection := [] } (.binaryOp .offset lhsOp rhsOp), span⟩
          localDecls emptyLayoutTable) ∧
    ValidSliceRange rp delta totalLen ∧
    ∀ cls ∈ [MirFaultClass.arithOverflow, .boundsCheck, .ptrDerefInvalid,
              .treeBorrowsViolation, .storageLiveProtected],
      (blockIdx, stmtIdx, cls) ∈ discharged ∧ registry cls = .emittedAndVerified := by
  have hRv := (evalRvalue_offset_of_validSliceRange
    s.frame.locals s.memory localDecls lhsOp rhsOp rp sz delta totalLen
    hRange hLhs hRhs hStride hOffset).1
  refine ⟨?_, hRange, ?_⟩
  · dsimp only [evalStmt]
    rw [hRv]
    dsimp only []
    rw [hDstSlot]
    dsimp only []
    rw [hSet]
    dsimp only []
    rw [hNoProt]
    intro hUb
    nomatch hUb
  · intro cls hCls
    have hInStmt : cls ∈ censusStmtFaultClasses
        (.assign { local_ := dstLocal, projection := [] } (.binaryOp .offset lhsOp rhsOp)) := by
      dsimp only [censusStmtFaultClasses, rvalueUnevaluated, censusPlaceWriteFaultClasses,
        censusRvalueFaultClasses, censusBinOpFaultClasses]
      rw [mem_dedupFaultClasses_iff]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hCls
      rcases hCls with rfl | rfl | rfl | rfl | rfl
      · exact List.mem_append_right _ (List.mem_append_right _ (by decide))
      · exact List.mem_append_right _ (List.mem_append_right _ (by decide))
      · exact List.mem_append_right _ (List.mem_append_right _ (by decide))
      · exact List.mem_append_left _ (by decide)
      · exact List.mem_append_left _ (by decide)
    have hInSites : (blockIdx, stmtIdx, cls) ∈
        censusStmtFaultSites blockIdx stmtIdx
          ⟨.assign { local_ := dstLocal, projection := [] } (.binaryOp .offset lhsOp rhsOp), span⟩ := by
      simp only [censusStmtFaultSites, List.mem_map]
      exact ⟨cls, hInStmt, rfl⟩
    exact (reconcileFaultCoverageWithRegistry_verified_iff registry _ discharged).mp
      hRec (blockIdx, stmtIdx, cls) hInSites

/--
Bridge theorem tying `evalCopyNonOverlapping_one_of_obligations` to non-`.ub`
statement execution (`¬ StepNodeExposesUb`) and `reconcileFaultCoverageWithRegistry`
discharge of the `copyNonOverlapping` intrinsic fault sites at `(blockIdx, stmtIdx)`.
-/
theorem evalCopyNonOverlapping_one_not_exposesUb_and_census_of_obligations
    (s : MachineState) (srcOp dstOp countOp : Operand) (span : String)
    (blockIdx : BasicBlockIdx) (stmtIdx : Nat)
    (registry : PropertyRegistry) (discharged : List FaultSite)
    (src dst : RawPtrVal) (sz : Nat) (srcEntry dstEntry : BorrowEntry)
    (copiedVal oldDstVal : Value) (locals' : List LocalValue)
    (hNonoverlap : NonOverlappingPtrs src dst 1)
    (hSrcOff : src.offset = 0)
    (hDstOff : dst.offset = 0)
    (hSrc :
      evalOperand s.frame.locals srcOp s.memory.borrows s.memory.globals emptyLayoutTable s.memory.callerLocals
          (callStack := s.memory.callStack) =
        .ok (.ptr src.toProvenancePtr sz) s.frame.locals)
    (hDst :
      evalOperand s.frame.locals dstOp s.memory.borrows s.memory.globals emptyLayoutTable s.memory.callerLocals
          (callStack := s.memory.callStack) =
        .ok (.ptr dst.toProvenancePtr sz) s.frame.locals)
    (hCnt :
      evalOperand s.frame.locals countOp s.memory.borrows s.memory.globals emptyLayoutTable s.memory.callerLocals
          (callStack := s.memory.callStack) =
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
        some locals')
    (hFrame :
      copyEntriesTargetActiveFrame s.memory.callStack srcEntry dstEntry = true)
    (hRec :
      reconcileFaultCoverageWithRegistry registry
        (censusStmtFaultSites blockIdx stmtIdx
          ⟨.intrinsic (.copyNonOverlapping srcOp dstOp countOp), span⟩)
        discharged = .verified) :
    ¬ StepNodeExposesUb
        (evalStmt s ⟨.intrinsic (.copyNonOverlapping srcOp dstOp countOp), span⟩
          [] emptyLayoutTable) ∧
    NonOverlappingPtrs src dst 1 ∧
    ∀ cls ∈ [MirFaultClass.arithOverflow, .boundsCheck, .ptrDerefInvalid,
              .ptrAlignMismatch, .treeBorrowsViolation, .scalarNicheInvalid, .uninitRead],
      (blockIdx, stmtIdx, cls) ∈ discharged ∧ registry cls = .emittedAndVerified := by
  have hStep := (evalCopyNonOverlapping_one_of_obligations
    s srcOp dstOp countOp src dst sz srcEntry dstEntry copiedVal oldDstVal locals'
    hNonoverlap hSrcOff hDstOff hSrc hDst hCnt hSrcPt hSrcLookup hDstLookup
    hSrcPerm hDstPerm hTagNe hLocNe hSrcProj hDstProj hSrcVal hDstVal hWrite hFrame).1
  refine ⟨?_, hNonoverlap, ?_⟩
  · dsimp only [evalStmt]
    rw [hStep]
    intro hUb
    nomatch hUb
  · intro cls hCls
    have hInStmt : cls ∈ censusStmtFaultClasses
        (.intrinsic (.copyNonOverlapping srcOp dstOp countOp)) := by
      simp only [censusStmtFaultClasses, censusIntrinsicFaultClasses,
        mem_dedupFaultClasses_iff, List.mem_append]
      exact Or.inr hCls
    have hInSites : (blockIdx, stmtIdx, cls) ∈
        censusStmtFaultSites blockIdx stmtIdx
          ⟨.intrinsic (.copyNonOverlapping srcOp dstOp countOp), span⟩ := by
      simp only [censusStmtFaultSites, List.mem_map]
      exact ⟨cls, hInStmt, rfl⟩
    exact (reconcileFaultCoverageWithRegistry_verified_iff registry _ discharged).mp
      hRec (blockIdx, stmtIdx, cls) hInSites

end Anneal.UnsafeObligations
