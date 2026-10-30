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
Evaluate `copy_nonoverlapping` once `srcVal`, `dstVal`, and scalar `countBits`
have been evaluated into `locals₃`.
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
          let n := countBits
          let srcStart := srcPtr.offsetBytes
          let dstStart := dstPtr.offsetBytes
          let isSingleDirect :=
            Bool.and
              (Nat.beq n 1)
              (Bool.and (Nat.beq srcStart 0) (Nat.beq dstStart 0))
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
