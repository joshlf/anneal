import Trusted.Effect
import Trusted.ITree
import Trusted.Sequence
import Trusted.Rustc.V2026_06_01.Layout
import Trusted.Rustc.V2026_06_01.MirAst.Types
import Trusted.Rustc.V2026_06_01.MirAst.Places
import Trusted.Rustc.V2026_06_01.MirAst.Rvalues
import Trusted.Rustc.V2026_06_01.MirAst.Statements
import Trusted.Rustc.V2026_06_01.MirAst.Body
import Trusted.Rustc.V2026_06_01.MirSemantics.State
import Trusted.Rustc.V2026_06_01.MirSemantics.Scalars
import Trusted.Rustc.V2026_06_01.MirSemantics.Bytes
import Trusted.Rustc.V2026_06_01.MirSemantics.Places

namespace Trusted.Rustc.V2026_06_01.MirSemantics

open Trusted.Effect
open Trusted.ITree
open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst

/-!
Small-step interaction-tree execution of MIR `Statement`s (`advanceStmt`,
`evalStmt`) for `Runtime(PostCleanup)` MIR at
`rustc 1.98.0-nightly (14210df0e 2026-05-31)` (`#88`, `#100`, `#102`).

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L303-L420>

> "pub enum StatementKind<'tcx> {
>     Assign(Box<(Place<'tcx>, Rvalue<'tcx>)>),
>     FakeRead(Box<(FakeReadCause, Place<'tcx>)>),
>     SetDiscriminant { place: Box<Place<'tcx>>, variant_index: VariantIdx },
>     Deinit(Box<Place<'tcx>>),
>     StorageLive(Local),
>     StorageDead(Local),
>     Retag(RetagKind, Box<Place<'tcx>>),
>     PlaceMention(Box<Place<'tcx>>),
>     AscribeUserType(Box<(Place<'tcx>, UserTypeProjection)>, Variance),
>     Coverage(CoverageKind),
>     Intrinsic(Box<NonDivergingIntrinsic<'tcx>>),
>     ConstEvalCounter,
>     Nop,
>     BackwardIncompatibleDropHint { place: Box<Place<'tcx>>, reason: BackwardIncompatibleDropReason },
> }"
-/

/--
Advance the program counter to the next statement in the current basic block.
-/
def advanceStmt
    (s : MachineState)
    (locals' : List LocalSlot)
    (mem' : Memory := s.memory) :
    MachineState :=
  { s with
    frame := {
      s.frame with
      stmtIdx := Nat.add s.frame.stmtIdx 1
      locals := locals'
    }
    memory := mem'
  }

/--
Concatenate two `List Value` sequences.
-/
@[reducible]
def appendValues : List Value → List Value → List Value
  | .nil, ys => ys
  | x :: xs, ys => x :: appendValues xs ys

/--
Replace `length srcSlice` elements in `dstElems` starting at index `dstStart`
with `srcSlice`.
-/
@[reducible]
def spliceValues
    (srcSlice : List Value)
    (dstStart : Nat)
    (dstElems : List Value) :
    List Value :=
  let n := length srcSlice
  appendValues
    (takeValues dstStart dstElems)
    (appendValues srcSlice (dropValues (Nat.add dstStart n) dstElems))

/--
Test whether two `RigidTy` constructors share the same runtime `Value` shape
so a single-element `copy_nonoverlapping` can transfer the `Value` directly
without re-encoding through `AbstractByte`s.
-/
@[reducible]
def sameRigidTyShape (k₁ k₂ : RigidTy) : Bool :=
  match k₁, k₂ with
  | .bool, .bool => true
  | .char, .char => true
  | .uint _, .uint _ =>
    match intCastTargetBytes k₁, intCastTargetBytes k₂ with
    | .some n₁, .some n₂ => Nat.beq n₁ n₂
    | _, _ => false
  | .int _, .int _ =>
    match intCastTargetBytes k₁, intCastTargetBytes k₂ with
    | .some n₁, .some n₂ => Nat.beq n₁ n₂
    | _, _ => false
  | .uint _, .int _ =>
    match intCastTargetBytes k₁, intCastTargetBytes k₂ with
    | .some n₁, .some n₂ => Nat.beq n₁ n₂
    | _, _ => false
  | .int _, .uint _ =>
    match intCastTargetBytes k₁, intCastTargetBytes k₂ with
    | .some n₁, .some n₂ => Nat.beq n₁ n₂
    | _, _ => false
  | .array e₁ n₁, .array e₂ n₂ =>
    match Nat.beq n₁ n₂ with
    | false => false
    | true =>
      match rigidTyKindByteSize e₁, rigidTyKindByteSize e₂ with
      | .some s₁, .some s₂ => Nat.beq s₁ s₂
      | _, _ => false
  | .tuple ks₁, .tuple ks₂ => Nat.beq (length ks₁) (length ks₂)
  | .adt p₁ _, .adt p₂ _ => stringEq p₁ p₂
  | .ref _ _, .ref _ _ => true
  | .rawPtr _ _, .rawPtr _ _ => true
  | _, _ => false

/--
Resolve the pointee `Ty` of a pointer `Operand` using `operandTy` and
`pointeeTyOf`.
-/
@[reducible]
def operandPointeeTy
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (op : Operand) :
    Option Ty :=
  match operandTy localDecls layouts op with
  | .some ptrTy => pointeeTyOf ptrTy
  | .none => .none

/--
Evaluate the single-element direct value copy branch (`count == 1` and
`srcStart == 0` and `dstStart == 0`) of `evalCopyNonOverlapping`.
-/
def evalCopySingleDirect
    (s : MachineState)
    (src dst : Operand)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (srcPtr dstPtr : ProvenancePtr)
    (srcEntry dstEntry : BorrowEntry)
    (locals₃ : List LocalSlot) :
    MirStepNode :=
  let overlaps :=
    match Nat.beq srcPtr.tag dstPtr.tag with
    | true => true
    | false =>
      match
        Nat.beq srcEntry.targetLocal dstEntry.targetLocal
      with
      | false => false
      | true =>
        projectionsOverlap
          srcEntry.targetProjection
          dstEntry.targetProjection
  match overlaps with
  | true => MirStepNode.fail .ub
  | false =>
    let srcRootSlot : Option LocalSlot :=
      match get? locals₃ srcEntry.targetLocal with
      | .some slot => .some slot
      | .none =>
        match get? s.memory.callerLocals srcEntry.targetLocal with
        | .some slot => .some slot
        | .none =>
          get?
            s.memory.callerLocals
            (Nat.sub srcEntry.targetLocal (length locals₃))
    match srcRootSlot with
    | .some (.init srcRootVal) =>
      match
        readProjectedValue
          locals₃
          srcRootVal
          srcEntry.targetProjection
      with
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
              match
                rigidTyByteSize layouts srcPt,
                rigidTyByteSize layouts dstPt
              with
              | .some sSz, .some dSz =>
                match Nat.beq sSz dSz with
                | false => .none
                | true =>
                  match
                    encodeValueToBytes
                      defaultCodecFuel
                      layouts
                      srcPt
                      copiedVal
                  with
                  | .some bs =>
                    decodeValueFromBytes
                      defaultCodecFuel
                      layouts
                      dstPt
                      bs
                  | .none => .none
              | _, _ => .some copiedVal
          | _, _ => .some copiedVal
        match convertedOpt with
        | .none => MirStepNode.fail .ub
        | .some finalVal =>
          match
            writePlaceValue
              locals₃
              s.memory.borrows
              dstPlace
              finalVal
          with
          | .ok locals₄ =>
            let borrows' :=
              invalidateConflictingBorrows
                s.memory.borrows
                dstEntry.targetLocal
                (.some dstPtr.tag)
            MirStepNode.step
              (advanceStmt
                s
                locals₄
                { s.memory with borrows := borrows' })
          | .unsupported => MirStepNode.unsupported
          | .ub =>
            match get? locals₃ dstPlace.local_ with
            | .some _ => MirStepNode.fail .ub
            | .none =>
              let callerIdx :=
                match get? s.memory.callerLocals dstPlace.local_ with
                | .some _ => dstPlace.local_
                | .none => Nat.sub dstPlace.local_ (length locals₃)
              let coerceToCallerDst (oldVal : Value) : Value :=
                match oldVal, finalVal with
                | .aggregate 0 dstElems, .scalar sc =>
                  match
                    Bool.and
                      (Bool.not (Nat.beq sc.sizeBytes 1))
                      (Nat.ble sc.sizeBytes (length dstElems))
                  with
                  | false => finalVal
                  | true =>
                    match
                      encodeUntypedValueToBytes defaultCodecFuel finalVal
                    with
                    | .none => finalVal
                    | .some bs =>
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
                        .aggregate 0 (spliceValues copiedBytes 0 dstElems)
                      | .none => finalVal
                | _, _ => finalVal
              let callerWriteRes : PlaceWriteResult :=
                match dstPlace.projection with
                | .nil =>
                  match get? s.memory.callerLocals callerIdx with
                  | .some .dead => .ub
                  | .some (.init oldVal) =>
                    let coercedVal := coerceToCallerDst oldVal
                    match
                      set? s.memory.callerLocals callerIdx (.init coercedVal)
                    with
                    | .some callerLocals' => .ok callerLocals'
                    | .none => .ub
                  | .some .uninit =>
                    match
                      set? s.memory.callerLocals callerIdx (.init finalVal)
                    with
                    | .some callerLocals' => .ok callerLocals'
                    | .none => .ub
                  | .none => .ub
                | .deref :: _ => .ub
                | proj :: rest =>
                  match get? s.memory.callerLocals callerIdx with
                  | .some (.init rootVal) =>
                    let coercedVal :=
                      match
                        readProjectedValue locals₃ rootVal (proj :: rest)
                      with
                      | .ok oldSubVal => coerceToCallerDst oldSubVal
                      | _ => finalVal
                    match
                      writeProjectedValue
                        locals₃
                        rootVal
                        (proj :: rest)
                        coercedVal
                    with
                    | .ok rootVal' =>
                      match
                        set? s.memory.callerLocals callerIdx (.init rootVal')
                      with
                      | .some callerLocals' => .ok callerLocals'
                      | .none => .ub
                    | .ub => .ub
                    | .unsupported => .unsupported
                  | _ => .ub
              match callerWriteRes with
              | .ub => MirStepNode.fail .ub
              | .unsupported => MirStepNode.unsupported
              | .ok callerLocals' =>
                let borrows' :=
                  invalidateConflictingBorrows
                    s.memory.borrows
                    dstEntry.targetLocal
                    (.some dstPtr.tag)
                MirStepNode.step
                  (advanceStmt
                    s
                    locals₃
                    { s.memory with
                      borrows := borrows'
                      callerLocals := callerLocals' })
    | _ => MirStepNode.fail .ub

/--
ABI alignment in bytes on a 64-bit x86-64 target for a `RigidTy` whose
alignment is determined structurally without consulting `LayoutTable`:
`bool` and `()` / zero-sized function items have alignment `1`, `char` has
alignment `4`, primitive integers (`u8`..`u128`, `usize`, `i8`..`i128`,
`isize`) have alignment equal to their byte width (`1, 2, 4, 8, 16`), thin and
wide pointers/references have alignment `8`, and `[T; N]` has the alignment of
`T`.

Reference (The Rust Reference, "Type Layout — Size and Alignment", Rust 1.98.0):
<https://doc.rust-lang.org/1.98.0/reference/type-layout.html#size-and-alignment>

> "The alignment of primitives is platform-specific. In most cases, their
> alignment is equal to their size, although it may be less. In particular,
> `i128` and `u128` are often aligned to 4 or 8 bytes even though their size is
> 16, and on many 32-bit platforms `i64`, `u64`, and `f64` are only aligned to
> 4 bytes, not 8."
>
> "Pointers to sized types have the same size and alignment as `usize`."
>
> "An array of `[T; N]` has a size of `size_of::<T>() * N` and the same
> alignment of `T`."
-/
@[reducible]
def rigidTyKindAlignBytes : RigidTy → Option Nat
  | .bool => .some 1
  | .char => .some 4
  | .uint w => intCastTargetBytes (.uint w)
  | .int w => intCastTargetBytes (.int w)
  | .tuple .nil => .some 1
  | .fnDef _ _ => .some 1
  | .fnPtr _ _ _ _ => .some 8
  | .ref _ _ => .some 8
  | .rawPtr _ _ => .some 8
  | .array elemKind _ => rigidTyKindAlignBytes elemKind
  | _ => .none

/--
Determine the ABI alignment in bytes of `ty` using `rigidTyKindAlignBytes` for
primitives, pointers, and homogeneous arrays, or `LayoutTable.lookup layouts
ty.layoutIdx` for ADTs and layout-indexed aggregates.
-/
@[reducible]
def rigidTyAlignBytes (layouts : LayoutTable) (ty : Ty) : Option Nat :=
  match rigidTyKindAlignBytes ty.kind with
  | .some al => .some al
  | .none =>
    match LayoutTable.lookup layouts ty.layoutIdx with
    | .some l => .some l.align.bytes
    | .none => .none

/--
Outcome of `copy_nonoverlapping` size-overflow, alignment, and zero-byte
prechecks prior to live-allocation dereference.
-/
inductive CopyPrecheckResult where
  | ub
  | zero
  | nonZero (totalBytesOpt : Option Nat)

/--
Test whether runtime pointer operand `v` satisfies byte alignment `elemAlign`
(either as a provenance-carrying `ProvenancePtr` at aligned `offsetBytes` or as
an 8-byte provenance-free integer scalar at aligned `bits`).
-/
@[reducible]
def ptrValueAligned (elemAlign : Nat) : Value → Bool
  | .ptr p _ =>
    Bool.or (Nat.beq elemAlign 0) (Nat.beq (Nat.mod p.offsetBytes elemAlign) 0)
  | .scalar sc =>
    Bool.and
      (Nat.beq sc.sizeBytes 8)
      (Bool.or (Nat.beq elemAlign 0) (Nat.beq (Nat.mod sc.bits elemAlign) 0))
  | _ => false

/--
Check `count * size_of::<T>() <= isize::MAX` (`9223372036854775807`), pointer
alignment of both `srcVal` and `dstVal` to `align_of::<T>()` (including when
`count == 0`), and zero-byte short-circuiting (`count == 0` or `size_of::<T>()
== 0`).
-/
@[reducible]
def copyPrecheck
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (src : Operand)
    (srcVal dstVal : Value)
    (countBits : Nat) :
    CopyPrecheckResult :=
  match operandPointeeTy localDecls layouts src with
  | .none =>
    match Nat.beq countBits 0 with
    | true => .zero
    | false => .nonZero .none
  | .some srcPt =>
    let totalRes : Option (Option Nat) :=
      match rigidTyByteSize layouts srcPt with
      | .none => .some .none
      | .some elemBytes =>
        let totalBytes := Nat.mul countBits elemBytes
        match Nat.ble totalBytes 9223372036854775807 with
        | false => .none
        | true => .some (.some totalBytes)
    match totalRes with
    | .none => .ub
    | .some totalBytesOpt =>
      let alignOk : Bool :=
        match rigidTyAlignBytes layouts srcPt with
        | .some elemAlign =>
          Bool.and
            (ptrValueAligned elemAlign srcVal)
            (ptrValueAligned elemAlign dstVal)
        | .none => true
      match alignOk with
      | false => .ub
      | true =>
        match Nat.beq countBits 0 with
        | true => .zero
        | false =>
          match totalBytesOpt with
          | .some 0 => .zero
          | _ => .nonZero totalBytesOpt

/--
Check that a borrow access of `totalBytes` starting at `ptr.offsetBytes` targets
a declared local in `localDecls` and, for a root-local borrow whose byte size
`layouts` resolves, fits within that local's byte size.
-/
@[reducible]
def copyBorrowInRootBounds
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (ptr : ProvenancePtr)
    (entry : BorrowEntry)
    (totalBytesOpt : Option Nat) :
    Bool :=
  match totalBytesOpt with
  | .none => true
  | .some totalBytes =>
    match get? localDecls entry.targetLocal with
    | .none => false
    | .some decl =>
      match entry.targetProjection with
      | .nil =>
        match rigidTyByteSize layouts decl.ty with
        | .some localBytes =>
          Nat.ble (Nat.add ptr.offsetBytes totalBytes) localBytes
        | .none => true
      | _ :: _ => true

/--
Look up `ptr.tag` in `borrows` and verify `copyBorrowInRootBounds` for
`totalBytesOpt`.
-/
@[reducible]
def lookupCopyBorrowChecked
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (borrows : List BorrowEntry)
    (ptr : ProvenancePtr)
    (totalBytesOpt : Option Nat) :
    Option BorrowEntry :=
  match lookupBorrow borrows ptr.tag with
  | .none => .none
  | .some entry =>
    match copyBorrowInRootBounds localDecls layouts ptr entry totalBytesOpt with
    | true => .some entry
    | false => .none

/--
Extract `totalBytes` little-endian bytes starting at byte offset `srcStart` from
canonicalized `srcBytes`-byte unsigned integer `srcBits`:
`(wrapScalarBits srcBits (scalarModulus srcBytes) / scalarModulus srcStart) %
scalarModulus totalBytes`.
-/
@[reducible]
def sliceScalarBytes (srcBits srcBytes srcStart totalBytes : Nat) : Nat :=
  Nat.mod
    (Nat.div
      (wrapScalarBits srcBits (scalarModulus srcBytes))
      (scalarModulus srcStart))
    (scalarModulus totalBytes)

/--
Splice `totalBytes`-byte little-endian integer `chunkBits`
(`chunkBits < scalarModulus totalBytes`) into `dstBytes`-byte unsigned integer
`dstBits` at byte offset `dstStart` (`dstStart + totalBytes <= dstBytes`),
preserving bytes `[0, dstStart)` and `[dstStart + totalBytes, dstBytes)`.
-/
@[reducible]
def spliceScalarBytes
    (dstBits chunkBits dstStart totalBytes dstBytes : Nat) : Nat :=
  let lowMod := scalarModulus dstStart
  let highMod := scalarModulus (Nat.add dstStart totalBytes)
  let old := wrapScalarBits dstBits (scalarModulus dstBytes)
  Nat.add (Nat.mod old lowMod)
    (Nat.add (Nat.mul chunkBits lowMod)
      (Nat.mul (Nat.div old highMod) highMod))

/--
Look up a root-local `LocalSlot` for `copy_nonoverlapping` in `locals₃`, falling
back to `s.memory.callerLocals` when `targetLocal` names a caller slot.
-/
@[reducible]
def lookupCopyRootSlot
    (s : MachineState)
    (locals₃ : List LocalSlot)
    (targetLocal : Local) :
    Option LocalSlot :=
  match get? locals₃ targetLocal with
  | .some slot => .some slot
  | .none =>
    match get? s.memory.callerLocals targetLocal with
    | .some slot => .some slot
    | .none =>
      get? s.memory.callerLocals (Nat.sub targetLocal (length locals₃))

/--
Write `newSlot` to root local `dstLocal` (in `locals₃` or `callerLocals`),
invalidate conflicting borrows on `dstLocal` relative to `dstPtr.tag`, and
advance the current statement.
-/
def writeCopyRootSlot
    (s : MachineState)
    (locals₃ : List LocalSlot)
    (dstPtr : ProvenancePtr)
    (dstLocal : Local)
    (newSlot : LocalSlot) :
    MirStepNode :=
  match get? locals₃ dstLocal with
  | .some .dead => MirStepNode.fail .ub
  | .some _ =>
    match set? locals₃ dstLocal newSlot with
    | .some locals₄ =>
      let borrows' :=
        invalidateConflictingBorrows
          s.memory.borrows
          dstLocal
          (.some dstPtr.tag)
      MirStepNode.step
        (advanceStmt
          s
          locals₄
          { s.memory with borrows := borrows' })
    | .none => MirStepNode.fail .ub
  | .none =>
    let callerIdx :=
      match get? s.memory.callerLocals dstLocal with
      | .some _ => dstLocal
      | .none => Nat.sub dstLocal (length locals₃)
    match get? s.memory.callerLocals callerIdx with
    | .some .dead => MirStepNode.fail .ub
    | .some _ =>
      match set? s.memory.callerLocals callerIdx newSlot with
      | .some callerLocals' =>
        let borrows' :=
          invalidateConflictingBorrows
            s.memory.borrows
            dstLocal
            (.some dstPtr.tag)
        MirStepNode.step
          (advanceStmt
            s
            locals₃
            { s.memory with
              borrows := borrows'
              callerLocals := callerLocals' })
      | .none => MirStepNode.fail .ub
    | .none => MirStepNode.fail .ub

/--
Evaluate a positive-byte `copy_nonoverlapping` of `totalBytes` bytes between two
root-local primitive integer locals (`srcBytes`, `dstBytes`) once in-bounds and
permission checks have passed:
1. Dead or out-of-frame source or destination locals, or an uninitialized source
   local, are undefined behavior.
2. Same-local overlapping byte ranges (`srcStart < dstStart + totalBytes` and
   `dstStart < srcStart + totalBytes`) are undefined behavior, whereas disjoint
   sub-ranges of the same local succeed.
3. Slices `totalBytes` little-endian bytes at `srcStart` via `sliceScalarBytes`
   and either initializes/overwrites all `dstBytes` bytes of `dst` when
   `dstStart == 0 && totalBytes == dstBytes` (even when `dst` was `.uninit`),
   splices them into an initialized destination scalar via `spliceScalarBytes`,
   or leaves a partially written `.uninit` destination `.uninit` (matching
   `evalWriteBytesCall`).
-/
def evalCopyRootIntScalars
    (s : MachineState)
    (locals₃ : List LocalSlot)
    (srcPtr dstPtr : ProvenancePtr)
    (srcEntry dstEntry : BorrowEntry)
    (srcBytes dstBytes totalBytes : Nat) :
    MirStepNode :=
  let srcStart := srcPtr.offsetBytes
  let dstStart := dstPtr.offsetBytes
  match
    lookupCopyRootSlot s locals₃ srcEntry.targetLocal,
    lookupCopyRootSlot s locals₃ dstEntry.targetLocal
  with
  | .none, _ => MirStepNode.fail .ub
  | .some .dead, _ => MirStepNode.fail .ub
  | _, .none => MirStepNode.fail .ub
  | _, .some .dead => MirStepNode.fail .ub
  | .some .uninit, _ => MirStepNode.fail .ub
  | .some (.init (.scalar srcSc)), .some dstSlot =>
    match Nat.beq srcSc.sizeBytes srcBytes with
    | false => MirStepNode.unsupported
    | true =>
      let overlaps : Bool :=
        Bool.and
          (Nat.beq srcEntry.targetLocal dstEntry.targetLocal)
          (Bool.not
            (Bool.or
              (Nat.ble (Nat.add srcStart totalBytes) dstStart)
              (Nat.ble (Nat.add dstStart totalBytes) srcStart)))
      match overlaps with
      | true => MirStepNode.fail .ub
      | false =>
        let chunk := sliceScalarBytes srcSc.bits srcBytes srcStart totalBytes
        match Bool.and (Nat.beq dstStart 0) (Nat.beq totalBytes dstBytes) with
        | true =>
          writeCopyRootSlot
            s
            locals₃
            dstPtr
            dstEntry.targetLocal
            (.init (.scalar { bits := chunk, sizeBytes := dstBytes }))
        | false =>
          match dstSlot with
          | .dead => MirStepNode.fail .ub
          | .uninit =>
            writeCopyRootSlot s locals₃ dstPtr dstEntry.targetLocal .uninit
          | .init (.scalar dstSc) =>
            match Nat.beq dstSc.sizeBytes dstBytes with
            | false => MirStepNode.unsupported
            | true =>
              let spliced :=
                spliceScalarBytes
                  dstSc.bits chunk dstStart totalBytes dstBytes
              writeCopyRootSlot
                s
                locals₃
                dstPtr
                dstEntry.targetLocal
                (.init (.scalar { bits := spliced, sizeBytes := dstBytes }))
          | .init _ => MirStepNode.unsupported
  | .some (.init _), _ => MirStepNode.unsupported

/--
Evaluate `copy_nonoverlapping` once `srcVal`, `dstVal`, and scalar `countBits`
have been evaluated into `locals₃`, enforcing `count * size_of::<T>() <=
isize::MAX`, pointer alignment to `align_of::<T>()` (including when `count ==
0`), and root-local byte bounds when `localDecls` / `layouts` resolve `T`, and
supporting direct element copies, byte-encoded copies into initialized or union
destinations, and untyped copies of uninitialized union bytes
(`FieldsShape.union`) into a union destination.

Reference (`core::intrinsics::copy_nonoverlapping`, Rust 1.98.0):
<https://doc.rust-lang.org/1.98.0/core/intrinsics/fn.copy_nonoverlapping.html>

> "Behavior is undefined if any of the following conditions are violated:
>
> - `src` must be valid for reads of `count * size_of::<T>()` bytes, and must
>   remain valid even when `dst` is written for `count * size_of::<T>()` bytes.
>   (This means if the memory ranges overlap, the two pointers must not be
>   subject to aliasing restrictions relative to each other.)
> - `dst` must be valid for writes of `count * size_of::<T>()` bytes, and must
>   remain valid even when `src` is read for `count * size_of::<T>()` bytes.
> - Both `src` and `dst` must be properly aligned.
> - The region of memory beginning at `src` with a size of `count *
>   size_of::<T>()` bytes must *not* overlap with the region of memory
>   beginning at `dst` with the same size."

Reference (The Rust Reference, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "The following is a non-exhaustive list of invalid values:
> - A value of any type, other than a union or raw pointer, with uninitialized
>   bytes (except for padding bytes, which may be uninitialized)."
-/
def evalCopyNonOverlappingWithCount
    (s : MachineState)
    (src dst : Operand)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (srcVal dstVal : Value)
    (countBits : Nat)
    (locals₃ : List LocalSlot) :
    MirStepNode :=
  match copyPrecheck localDecls layouts src srcVal dstVal countBits with
  | .ub => MirStepNode.fail .ub
  | .zero => MirStepNode.step (advanceStmt s locals₃)
  | .nonZero totalBytesOpt =>
    match srcVal, dstVal with
    | .ptr srcPtr _, .ptr dstPtr _ =>
      match
        lookupCopyBorrowChecked
          localDecls layouts s.memory.borrows srcPtr totalBytesOpt,
        lookupCopyBorrowChecked
          localDecls layouts s.memory.borrows dstPtr totalBytesOpt
      with
      | .some srcEntry, .some dstEntry =>
        match srcEntry.perm, dstEntry.perm with
        | .disabled, _ => MirStepNode.fail .ub
        | _, .frozen => MirStepNode.fail .ub
        | _, .disabled => MirStepNode.fail .ub
        | _, _ =>
          let rootIntStep? : Option MirStepNode :=
            match
              totalBytesOpt,
              srcEntry.targetProjection,
              dstEntry.targetProjection
            with
            | .some totalBytes, .nil, .nil =>
              match
                get? localDecls srcEntry.targetLocal,
                get? localDecls dstEntry.targetLocal
              with
              | .some srcDecl, .some dstDecl =>
                match
                  intCastTargetBytes srcDecl.ty.kind,
                  intCastTargetBytes dstDecl.ty.kind
                with
                | .some srcBytes, .some dstBytes =>
                  .some
                    (evalCopyRootIntScalars
                      s
                      locals₃
                      srcPtr
                      dstPtr
                      srcEntry
                      dstEntry
                      srcBytes
                      dstBytes
                      totalBytes)
                | _, _ => .none
              | _, _ => .none
            | _, _, _ => .none
          match rootIntStep? with
          | .some stepNode => stepNode
          | .none =>
          let n := countBits
          let srcStart := srcPtr.offsetBytes
          let dstStart := dstPtr.offsetBytes
          let singleSizeMatches : Bool :=
            match totalBytesOpt with
            | .none => true
            | .some totalBytes =>
              let srcPlace : Place := {
                local_ := srcEntry.targetLocal
                projection := srcEntry.targetProjection
              }
              let dstPlace : Place := {
                local_ := dstEntry.targetLocal
                projection := dstEntry.targetProjection
              }
              let srcOk : Bool :=
                match placeTy localDecls layouts srcPlace with
                | .some st =>
                  match rigidTyByteSize layouts st with
                  | .some sBytes => Nat.beq totalBytes sBytes
                  | .none => true
                | .none => true
              let dstOk : Bool :=
                match placeTy localDecls layouts dstPlace with
                | .some dt =>
                  match rigidTyByteSize layouts dt with
                  | .some dBytes => Nat.beq totalBytes dBytes
                  | .none => true
                | .none => true
              Bool.and srcOk dstOk
          let isSingleDirect :=
            Bool.and
              (Bool.and
                (Nat.beq n 1)
                (Bool.and (Nat.beq srcStart 0) (Nat.beq dstStart 0)))
              singleSizeMatches
          match isSingleDirect with
          | true =>
            evalCopySingleDirect
              s
              src
              dst
              localDecls
              layouts
              srcPtr
              dstPtr
              srcEntry
              dstEntry
              locals₃
          | false =>
            let srcRootSlot : Option LocalSlot :=
              match get? locals₃ srcEntry.targetLocal with
              | .some slot => .some slot
              | .none =>
                match get? s.memory.callerLocals srcEntry.targetLocal with
                | .some slot => .some slot
                | .none =>
                  get?
                    s.memory.callerLocals
                    (Nat.sub srcEntry.targetLocal (length locals₃))
            let dstRootSlot : Option LocalSlot :=
              match get? locals₃ dstEntry.targetLocal with
              | .some slot => .some slot
              | .none =>
                match get? s.memory.callerLocals dstEntry.targetLocal with
                | .some slot => .some slot
                | .none =>
                  get?
                    s.memory.callerLocals
                    (Nat.sub dstEntry.targetLocal (length locals₃))
            match srcRootSlot, dstRootSlot with
            | .some (.init srcRootVal), .some (.init dstRootVal) =>
              let dstPlace : Place := {
                local_ := dstEntry.targetLocal
                projection := dstEntry.targetProjection
              }
              let dstLocalPlaceTy : Option Ty :=
                match get? locals₃ dstPlace.local_ with
                | .some _ => placeTy localDecls layouts dstPlace
                | .none => .none
              let dstIsAdt : Bool :=
                match dstLocalPlaceTy with
                | .some { kind := .adt _ _, .. } => true
                | _ => false
              let writeDstVal (newVal : Value) : MirStepNode :=
                match
                  writePlaceValue
                    locals₃
                    s.memory.borrows
                    dstPlace
                    newVal
                with
                | .ok locals₄ =>
                  let borrows' :=
                    invalidateConflictingBorrows
                      s.memory.borrows
                      dstEntry.targetLocal
                      (.some dstPtr.tag)
                  MirStepNode.step
                    (advanceStmt
                      s
                      locals₄
                      { s.memory with borrows := borrows' })
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
                          match
                            set? s.memory.callerLocals callerIdx (.init newVal)
                          with
                          | .some callerLocals' => .ok callerLocals'
                          | .none => .ub
                        | .none => .ub
                      | .deref :: _ => .ub
                      | proj :: rest =>
                        match get? s.memory.callerLocals callerIdx with
                        | .some (.init rootVal) =>
                          match
                            writeProjectedValue
                              locals₃
                              rootVal
                              (proj :: rest)
                              newVal
                          with
                          | .ok rootVal' =>
                            match
                              set?
                                s.memory.callerLocals
                                callerIdx
                                (.init rootVal')
                            with
                            | .some callerLocals' => .ok callerLocals'
                            | .none => .ub
                          | .ub => .ub
                          | .unsupported => .unsupported
                        | _ => .ub
                    match callerWriteRes with
                    | .ub => MirStepNode.fail .ub
                    | .unsupported => MirStepNode.unsupported
                    | .ok callerLocals' =>
                      let borrows' :=
                        invalidateConflictingBorrows
                          s.memory.borrows
                          dstEntry.targetLocal
                          (.some dstPtr.tag)
                      MirStepNode.step
                        (advanceStmt
                          s
                          locals₃
                          { s.memory with
                            borrows := borrows'
                            callerLocals := callerLocals' })
              let copyViaBytes
                  (srcSubVal dstSubVal : Value) :
                  MirStepNode :=
                let overlaps :=
                  match Nat.beq srcPtr.tag dstPtr.tag with
                  | true => true
                  | false =>
                    match
                      Nat.beq srcEntry.targetLocal dstEntry.targetLocal
                    with
                    | false => false
                    | true =>
                      projectionsOverlap
                        srcEntry.targetProjection
                        dstEntry.targetProjection
                match overlaps with
                | true => MirStepNode.fail .ub
                | false =>
                  let srcSliceVal : Option Value :=
                    match srcSubVal with
                    | .aggregate 0 srcElems =>
                      match
                        Nat.ble (Nat.add srcStart n) (length srcElems)
                      with
                      | true =>
                        .some
                          (.aggregate 0
                            (takeValues n (dropValues srcStart srcElems)))
                      | false =>
                        match Nat.beq srcStart 0 with
                        | true => .some srcSubVal
                        | false => .none
                    | _ => .some srcSubVal
                  let dstTargetTyOpt : Option Ty :=
                    match dstLocalPlaceTy with
                    | .some t => .some t
                    | .none => operandPointeeTy localDecls layouts dst
                  match srcSliceVal with
                  | .none => MirStepNode.fail .ub
                  | .some sVal =>
                    match encodeUntypedValueToBytes defaultCodecFuel sVal with
                    | .none => MirStepNode.unsupported
                    | .some bs =>
                      let spliceBytesToDstArray : Option Value :=
                        match Bool.not dstIsAdt, dstSubVal with
                        | true, .aggregate 0 dstElems =>
                          match
                            Nat.ble
                              (Nat.add dstStart (length bs))
                              (length dstElems)
                          with
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
                              .some
                                (.aggregate 0
                                  (spliceValues copiedBytes dstStart dstElems))
                            | .none => .none
                        | _, _ => .none
                      let preferSplicedArray : Bool :=
                        match dstLocalPlaceTy, dstSubVal with
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
                              match
                                decodeValueFromBytes
                                  defaultCodecFuel
                                  layouts
                                  dstPt
                                  bs
                              with
                              | .some decodedVal => writeDstVal decodedVal
                              | .none =>
                                match spliceBytesToDstArray with
                                | .some splicedVal => writeDstVal splicedVal
                                | .none => MirStepNode.fail .ub
                            | false =>
                              match spliceBytesToDstArray with
                              | .some splicedVal => writeDstVal splicedVal
                              | .none => MirStepNode.unsupported
                          | .none =>
                            match spliceBytesToDstArray with
                            | .some splicedVal => writeDstVal splicedVal
                            | .none => MirStepNode.unsupported
                        | .none =>
                          match spliceBytesToDstArray with
                          | .some splicedVal => writeDstVal splicedVal
                          | .none => MirStepNode.fail .ub
              match
                readProjectedValue
                  locals₃
                  srcRootVal
                  srcEntry.targetProjection,
                readProjectedValue
                  locals₃
                  dstRootVal
                  dstEntry.targetProjection
              with
              | .ok (.aggregate 0 srcElems),
                .ok (.aggregate 0 dstElems) =>
                let inBounds :=
                  Bool.and
                    (Bool.not dstIsAdt)
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
                  | false => MirStepNode.fail .ub
                | true =>
                  let sameContainer :=
                    Bool.and
                      (Nat.beq srcEntry.targetLocal dstEntry.targetLocal)
                      (projectionsOverlap
                        srcEntry.targetProjection
                        dstEntry.targetProjection)
                  let disjoint :=
                    match Nat.beq srcPtr.tag dstPtr.tag with
                    | true => false
                    | false =>
                      match sameContainer with
                      | false => true
                      | true =>
                        Bool.or
                          (Nat.ble (Nat.add srcStart n) dstStart)
                          (Nat.ble (Nat.add dstStart n) srcStart)
                  match disjoint with
                  | false => MirStepNode.fail .ub
                  | true =>
                    let copiedSlice :=
                      takeValues n (dropValues srcStart srcElems)
                    let dstElems' :=
                      spliceValues copiedSlice dstStart dstElems
                    writeDstVal (.aggregate 0 dstElems')
              | .ok srcSubVal, .ok dstSubVal =>
                copyViaBytes srcSubVal dstSubVal
              | .ok srcSubVal, .ub =>
                match Nat.beq dstStart 0 with
                | true => copyViaBytes srcSubVal .unit
                | false => MirStepNode.fail .ub
              | .ub, _ =>
                match
                  srcRootVal,
                  dstRootVal,
                  srcEntry.targetProjection,
                  dstEntry.targetProjection
                with
                | .aggregate _ srcFields,
                  .aggregate dstVar dstFields,
                  .field _ srcFieldTy :: .nil,
                  .field _ dstFieldTy :: .nil =>
                  let overlaps :=
                    match Nat.beq srcPtr.tag dstPtr.tag with
                    | true => true
                    | false =>
                      Nat.beq srcEntry.targetLocal dstEntry.targetLocal
                  match overlaps with
                  | true => MirStepNode.fail .ub
                  | false =>
                    let elemBytesOpt : Option Nat :=
                      match operandPointeeTy localDecls layouts src with
                      | .some pt => rigidTyByteSize layouts pt
                      | .none => .some 1
                    match
                      elemBytesOpt,
                      rigidTyByteSize layouts srcFieldTy,
                      rigidTyByteSize layouts dstFieldTy
                    with
                    | .some elemSz, .some srcPlaceBytes, .some dstPlaceBytes =>
                      let copyByteLen := Nat.mul n elemSz
                      let inBounds :=
                        Bool.and
                          (Nat.ble (Nat.add srcStart copyByteLen) srcPlaceBytes)
                          (Nat.ble (Nat.add dstStart copyByteLen) dstPlaceBytes)
                      match inBounds with
                      | false => MirStepNode.fail .ub
                      | true =>
                        match
                          encodeUnionFieldsWith
                            (encodeUntypedValueToBytes defaultCodecFuel)
                            srcPlaceBytes
                            srcFields
                        with
                        | .none => MirStepNode.fail .ub
                        | .some srcUnionBytes =>
                          match
                            sliceAbstractBytes srcUnionBytes srcStart copyByteLen
                          with
                          | .none => MirStepNode.fail .ub
                          | .some copiedBytes =>
                            match
                              Bool.and
                                (Nat.beq dstStart 0)
                                (Nat.beq copyByteLen dstPlaceBytes),
                              decodeValueFromBytes
                                defaultCodecFuel
                                layouts
                                dstFieldTy
                                copiedBytes
                            with
                            | true, .some decodedVal => writeDstVal decodedVal
                            | _, _ =>
                              let dstIsUnion : Bool :=
                                match get? localDecls dstEntry.targetLocal with
                                | .some decl =>
                                  match
                                    LayoutTable.lookup layouts decl.ty.layoutIdx
                                  with
                                  | .some l =>
                                    match l.fields with
                                    | .union _ => true
                                    | _ => false
                                  | .none => false
                                | .none => false
                              match dstIsUnion with
                              | false => MirStepNode.fail .ub
                              | true =>
                                let resetUnion :=
                                  Value.aggregate dstVar (takeValues 1 dstFields)
                                match
                                  set?
                                    locals₃
                                    dstEntry.targetLocal
                                    (.init resetUnion)
                                with
                                | .some locals₄ =>
                                  let borrows' :=
                                    invalidateConflictingBorrows
                                      s.memory.borrows
                                      dstEntry.targetLocal
                                      (.some dstPtr.tag)
                                  MirStepNode.step
                                    (advanceStmt
                                      s
                                      locals₄
                                      { s.memory with borrows := borrows' })
                                | .none => MirStepNode.fail .ub
                    | _, _, _ => MirStepNode.fail .ub
                | _, _, _, _ => MirStepNode.fail .ub
              | _, _ => MirStepNode.fail .ub
            | _, _ => MirStepNode.fail .ub
      | _, _ => MirStepNode.fail .ub
    | _, _ => MirStepNode.fail .ub

/--
Execute a `NonDivergingIntrinsic.copyNonOverlapping src dst count` statement.

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L449-L473>

> "pub enum NonDivergingIntrinsic<'tcx> {
>     Assume(Operand<'tcx>),
>     CopyNonOverlapping(CopyNonOverlapping<'tcx>),
> }"
-/
def evalCopyNonOverlapping
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
      with
      | .ub => MirStepNode.fail .ub
      | .unsupported => MirStepNode.unsupported
      | .ok (.scalar countSc) locals₃ =>
        evalCopyNonOverlappingWithCount
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
Execute a single MIR `Statement` from state `s` using `localDecls` and `layouts`
for type- and layout-aware rvalue and intrinsic evaluation.

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L357-L420>

> "/// Write the discriminant for a variant to the enum Place.
> ///
> /// This is permitted for both coroutines and ADTs. This does not necessarily
> /// write to the entire place; instead, it writes to the minimum set of bytes
> /// as required by the layout for the type.
> SetDiscriminant { place: Box<Place<'tcx>>, variant_index: VariantIdx },
> ...
> /// Retag references in the given place, ensuring they got fresh tags. ...
> Retag(RetagKind, Box<Place<'tcx>>),
>
> /// This statement exists to preserve a trace of a scrutinee matched against a
> /// wildcard binding. ...
> PlaceMention(Box<Place<'tcx>>),"
-/
def evalStmt
    (s : MachineState)
    (stmt : Statement)
    (localDecls : List LocalDecl := .nil)
    (layouts : LayoutTable := emptyLayoutTable) :
    MirStepNode :=
  match stmt.kind with
  | .nop => MirStepNode.step (advanceStmt s s.frame.locals)
  | .coverage => MirStepNode.step (advanceStmt s s.frame.locals)
  | .constEvalCounter => MirStepNode.step (advanceStmt s s.frame.locals)
  | .placeMention place =>
    match get? s.frame.locals place.local_ with
    | .none => MirStepNode.fail .ub
    | .some .dead => MirStepNode.fail .ub
    | .some _ => MirStepNode.step (advanceStmt s s.frame.locals)
  | .retag retagKind place =>
    match
      evalOperand
        s.frame.locals
        (.copy place)
        s.memory.borrows
        s.memory.globals
        layouts
        s.memory.callerLocals
    with
    | .ok (.ptr ptrVal _) locals' =>
      match lookupBorrow s.memory.borrows ptrVal.tag with
      | .some entry =>
        match entry.perm with
        | .disabled => MirStepNode.fail .ub
        | _ =>
          match retagKind with
          | .fnEntry =>
            let protId := s.memory.nextProtector
            let borrows' :=
              attachBorrowProtector s.memory.borrows ptrVal.tag protId
            let mem' : Memory := {
              s.memory with
              borrows := borrows'
              activeProtectors := protId :: s.memory.activeProtectors
              nextProtector := Nat.add protId 1
            }
            MirStepNode.step (advanceStmt s locals' mem')
          | _ => MirStepNode.step (advanceStmt s locals')
      | .none => MirStepNode.fail .ub
    | .ok _ _ => MirStepNode.fail .ub
    | .ub => MirStepNode.fail .ub
    | .unsupported => MirStepNode.unsupported
  | .storageLive loc =>
    match get? s.frame.locals loc with
    | .some _ =>
      match set? s.frame.locals loc .uninit with
      | .some locals' => MirStepNode.step (advanceStmt s locals')
      | .none => MirStepNode.fail .ub
    | .none => MirStepNode.fail .ub
  | .storageDead loc =>
    match get? s.frame.locals loc with
    | .some _ =>
      match set? s.frame.locals loc .dead with
      | .some locals' => MirStepNode.step (advanceStmt s locals')
      | .none => MirStepNode.fail .ub
    | .none => MirStepNode.fail .ub
  | .deinit p =>
    match p.projection with
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
  | .intrinsic (.assume op) =>
    match
      evalOperand
        s.frame.locals
        op
        s.memory.borrows
        s.memory.globals
        layouts
        s.memory.callerLocals
    with
    | .ok (.scalar sc) locals' =>
      match Bool.and (Nat.beq sc.sizeBytes 1) (Nat.beq sc.bits 1) with
      | true => MirStepNode.step (advanceStmt s locals')
      | false => MirStepNode.fail .ub
    | .ok _ _ => MirStepNode.fail .ub
    | .ub => MirStepNode.fail .ub
    | .unsupported => MirStepNode.unsupported
  | .intrinsic (.copyNonOverlapping src dst count) =>
    evalCopyNonOverlapping s src dst count localDecls layouts
  | .setDiscriminant p variantIdx =>
    match p.projection with
    | .nil =>
      match get? s.frame.locals p.local_ with
      | .some (.init (.aggregate _ fields)) =>
        let newSlot := .init (.aggregate variantIdx fields)
        match set? s.frame.locals p.local_ newSlot with
        | .some locals' => MirStepNode.step (advanceStmt s locals')
        | .none => MirStepNode.fail .ub
      | .some (.init _) => MirStepNode.fail .ub
      | .some .uninit => MirStepNode.fail .ub
      | .some .dead => MirStepNode.fail .ub
      | .none => MirStepNode.fail .ub
    | _ :: _ =>
      match
        evalOperand
          s.frame.locals
          (.copy p)
          s.memory.borrows
          s.memory.globals
          layouts
          s.memory.callerLocals
      with
      | .ok (.aggregate _ fields) locals₁ =>
        match
          writePlaceValue
            locals₁
            s.memory.borrows
            p
            (.aggregate variantIdx fields)
        with
        | .ok locals₂ => MirStepNode.step (advanceStmt s locals₂)
        | .ub => MirStepNode.fail .ub
        | .unsupported => MirStepNode.unsupported
      | .ok _ _ => MirStepNode.fail .ub
      | .ub => MirStepNode.fail .ub
      | .unsupported => MirStepNode.unsupported
  | .assign dst rv =>
    match evalRvalue s.frame.locals rv s.memory localDecls layouts with
    | .ok val locals₁ mem₁ =>
      match dst.projection with
      | .nil =>
        match get? locals₁ dst.local_ with
        | .some .dead => MirStepNode.fail .ub
        | .some _ =>
          match set? locals₁ dst.local_ (.init val) with
          | .some locals₂ =>
            match mem₁.activeProtectors with
            | .nil =>
              let borrows' :=
                invalidateConflictingBorrows mem₁.borrows dst.local_ .none
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
              with
              | true => MirStepNode.fail .ub
              | false =>
                let borrows' :=
                  invalidateConflictingBorrows mem₁.borrows dst.local_ .none
                MirStepNode.step
                  (advanceStmt s locals₂ { mem₁ with borrows := borrows' })
          | .none => MirStepNode.fail .ub
        | .none => MirStepNode.fail .ub
      | .deref :: restProj =>
        match
          evalPlaceWrite locals₁ mem₁.borrows dst val mem₁.activeProtectors
        with
        | .ok locals₂ =>
          let borrows' :=
            invalidateDerefWriteBorrows locals₁ mem₁.borrows dst restProj
          MirStepNode.step
            (advanceStmt s locals₂ { mem₁ with borrows := borrows' })
        | .ub =>
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
              let borrows' :=
                invalidateDerefWriteBorrows locals₁ mem₁.borrows dst restProj
              MirStepNode.step
                (advanceStmt
                  s
                  locals₁
                  { mem₁ with
                    borrows := borrows'
                    callerLocals := callerLocals' })
            | .ub => MirStepNode.fail .ub
            | .unsupported => MirStepNode.unsupported
        | .unsupported => MirStepNode.unsupported
      | proj :: rest =>
        match get? locals₁ dst.local_ with
        | .some (.init rootVal) =>
          match writeProjectedValue locals₁ rootVal (proj :: rest) val with
          | .ok rootVal' =>
            match set? locals₁ dst.local_ (.init rootVal') with
            | .some locals₂ =>
              match mem₁.activeProtectors with
              | .nil =>
                let borrows' :=
                  invalidateConflictingBorrowsAtProj
                    mem₁.borrows
                    dst.local_
                    .none
                    (proj :: rest)
                MirStepNode.step
                  (advanceStmt s locals₂ { mem₁ with borrows := borrows' })
              | protHead :: protTail =>
                match
                  hasProtectedWriteConflict
                    mem₁.borrows
                    (protHead :: protTail)
                    dst.local_
                    .none
                    (proj :: rest)
                with
                | true => MirStepNode.fail .ub
                | false =>
                  let borrows' :=
                    invalidateConflictingBorrowsAtProj
                      mem₁.borrows
                      dst.local_
                      .none
                      (proj :: rest)
                  MirStepNode.step
                    (advanceStmt s locals₂ { mem₁ with borrows := borrows' })
            | .none => MirStepNode.fail .ub
          | .ub => MirStepNode.fail .ub
          | .unsupported => MirStepNode.unsupported
        | .some .uninit => MirStepNode.fail .ub
        | .some .dead => MirStepNode.fail .ub
        | .none => MirStepNode.fail .ub
    | .ub => MirStepNode.fail .ub
    | .unsupported => MirStepNode.unsupported
  | _ => MirStepNode.unsupported

end Trusted.Rustc.V2026_06_01.MirSemantics
