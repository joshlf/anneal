/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import LeanMiriSpec.Correspondence.SimLM2_1
import LeanMiriSpec.Correspondence.ProjLM2_2

/-!
# Union and `Subslice` Hooks (`LM-2.4`)

The hooks in `Translate` reject every union operation and every array
`Subslice` with `StepError.unsupported`: `annealProjectionCx.field` knows only
array elements, `annealProjectionCx.subsliceLayout` rejects every array, the
aggregate hooks cannot downcast, and `annealEvalPlace` and `annealEvalOperand`
require a memory-backed local to be initialized in full before they project
into it. That last check is exactly wrong for unions: a union whose smallest
field was written keeps its remaining bytes uninitialized, and Miri never
requires them to be initialized.

This module adds the `lean-miri` machine leaves that unions and subslices need,
as an overlay `annealStepHooksLM2_4` that changes only `StepHooks.assign`, and
only for assignments that mention a union local or a `Subslice` projection
(`lm24Assign`). Every other statement runs the `Translate` hooks unchanged
(`annealStepHooksLM2_4_assign_of_not_lm24`), so the overlay is a conservative
extension of `annealStepHooksLM2_2`. The leaves follow rustc's interpreter
(`compiler/rustc_const_eval/src/interpret/{place,operand,projection,step}.rs`):

* Union field reads and writes project with the vendored
  `Miri.Interpreter.projectField`, whose `FieldsShape.Union` offset is `0`. A
  read checks initialization only of the field's own bytes, inside
  `Allocation.readScalar`; a write marks only the field's own bytes
  initialized, inside `Allocation.writeScalar`. Writing a field of a union that
  still lives in an immediate first moves it to memory with the vendored
  `Miri.Interpreter.forceAllocation`, as rustc's `as_mplace_or_mutable_local`
  does for a projected local.
* A union aggregate (`AggregateKind.Adt` with an active field) runs the vendored
  `Miri.Interpreter.writeAggregate`: it forces the union into memory (a fresh
  stack allocation starts uninitialized) and writes the one operand into the
  active field, so the bytes past that field stay uninitialized.
* A whole union, and an array view such as a subslice, is copied the way
  rustc's `copy_op` copies a value that is not an immediate: it forces the
  destination into memory and copies the bytes, the initialization mask, and the
  provenance with the vendored `Allocation.copy` (`annealMemCopyOp`). Nothing in
  this path reads the value, so uninitialized union bytes are copied rather than
  rejected.
* `Subslice` projections run the vendored `Miri.Interpreter.projectSubslice`
  with `annealSubsliceLayout`, the layout `[T; count]` of the sub-array.
-/

namespace LeanMiriSpec.Correspondence

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

/-! ## 1. Union Layouts -/

/-- Whether `lay` is the layout of a union (`FieldsShape.Union`). -/
def isUnionLayout (lay : Miri.Interpreter.LocalLayout) : Bool :=
  match lay.layout.fields with
  | .Union _ => true
  | _ => false

/-- Whether local `localId` is declared in `localDecls` with a union layout. -/
def isUnionLocal (localDecls : List LocalDecl) (layouts : LayoutTable) (localId : Nat) : Bool :=
  match lookupLocalDeclLayout localDecls layouts localId with
  | some lay => isUnionLayout lay
  | none => false

/-- Layout of field `idx` of the union layout `parent`.

`encodeTyId` encodes an ADT of layout index `i` as `100 + i`, so the union's
`TypeLayout` is entry `parent.ty - 100` of `layouts`, and its `fieldLayouts`
lists the layout index of each field. A union aggregate supplies no field type,
so this is the only source of the active field's layout there. -/
def unionFieldLayoutOf (layouts : LayoutTable) (parent : Miri.Interpreter.LocalLayout)
    (idx : Nat) : Option Miri.Interpreter.LocalLayout :=
  if 100 ≤ parent.ty ∧ parent.ty < 1000 then
    match layouts.lookup (parent.ty - 100) with
    | some tl =>
        match get? tl.fieldLayouts idx with
        | some fIdx =>
            (layouts.lookup fIdx).map fun fTl =>
              { ty := 100 + fIdx, layout := translateTypeLayout fTl }
        | none => none
    | none => none
  else
    none

/-! ## 2. Projection Contexts -/

/-- `annealProjectionCx` extended to union fields: field `idx` of a union has
the layout of the field type `fieldTy` that the MIR `Field` projection names.
Every other field query is answered by `annealProjectionCx`. -/
def annealUnionProjectionCx
    (frame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    (layouts : LayoutTable) (mach : AnnealMachine) (fieldTy : Miri.MIR.TyId) :
    Miri.Interpreter.ProjectionCx AnnealProv :=
  let base := annealProjectionCx frame layouts mach
  { base with
    field := fun parent idx =>
      match parent.layout.fields with
      | .Union _ => .ok (layoutOfEncodedTyId fieldTy layouts)
      | _ => base.field parent idx }

/-- `annealProjectionCx` extended to union fields whose layout comes from the
union's `TypeLayout.fieldLayouts` (`unionFieldLayoutOf`), for aggregates. -/
def annealUnionAggregateCx
    (frame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    (layouts : LayoutTable) (mach : AnnealMachine) :
    Miri.Interpreter.ProjectionCx AnnealProv :=
  let base := annealProjectionCx frame layouts mach
  { base with
    field := fun parent idx =>
      match parent.layout.fields with
      | .Union _ =>
          match unionFieldLayoutOf layouts parent idx with
          | some lay => .ok lay
          | none => .error (.obligation "union field layout missing from LayoutTable")
      | _ => base.field parent idx }

/-- Layout of the sub-array `[T; count]` of the array layout `baseLay`, which
rustc's `project_subslice` computes with `Ty::new_array(inner, inner_len)` and
`layout_of`: the element stride and alignment of `baseLay`, `count` elements,
and size `stride * count`. Array places are thin, so the metadata is `none`.

The result keeps `baseLay.ty`. Projections into the sub-array read only its
element encoding (`arrayElemLayoutOf` uses `(ty - 1000) % 100`), which the
sub-array shares with `baseLay`; its element count and size come from the
layout data. -/
def annealSubsliceLayout (baseLay : Miri.Interpreter.LocalLayout) (count : UInt64) :
    Except Miri.Interpreter.ProjectionError
      (Miri.Interpreter.LocalLayout × Miri.Interpreter.MemPlaceMeta AnnealProv) :=
  match baseLay.layout.fields with
  | .Array stride _ =>
      match stride.mul count with
      | .ok size =>
          .ok ({ ty := baseLay.ty
                 layout := { baseLay.layout with fields := .Array stride count, size := size } },
               .none)
      | .error err => .error (.size err)
  | _ => .error (.invariant "subslice on non-array")

/-- `annealProjectionCx` with array subslices enabled (`annealSubsliceLayout`).
-/
def annealSubsliceProjectionCx
    (frame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    (layouts : LayoutTable) (mach : AnnealMachine) :
    Miri.Interpreter.ProjectionCx AnnealProv :=
  { annealProjectionCx frame layouts mach with subsliceLayout := annealSubsliceLayout }

/-- Whether `elem` is a `Subslice` projection. -/
def isSubsliceElem : Miri.MIR.ProjectionElem → Bool
  | .Subslice _ _ _ => true
  | _ => false

/-! ## 3. Operands and Places -/

/-- Store `frame` as the top frame of the current state. -/
def annealSetTopFrame
    (frame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit) :
    Miri.Interpreter.RvalueM AnnealStepState Unit := do
  let st ← get
  let idx := st.stack.frames.size - 1
  if h : idx < st.stack.frames.size then
    set { st with stack := { frames := st.stack.frames.set idx frame h } }
  else
    throw (.stack .emptyStack)

/-- Read field `idx` (of MIR field type `fieldTy`) of the union local `localId`.

The local's layout is cached first, as in `annealEvalOperand`. A dead local is
undefined behavior (rustc's `DeadLocal`). A union local that is still an
uninitialized immediate holds no initialized byte, so reading any field of it
is undefined behavior, as in rustc, where the field read of an uninitialized
immediate fails `read_scalar`. A memory-backed union is projected with the
vendored `projectField` at offset `0`, without checking any byte: the caller's
`annealReadImmediateLM2_2` checks initialization of exactly the field's bytes.
Projected reads leave the local initialized even under `Move`. -/
def annealEvalUnionField (localDecls : List LocalDecl) (layouts : LayoutTable)
    (localId idx : Nat) (fieldTy : Miri.MIR.TyId) :
    Miri.Interpreter.RvalueM AnnealStepState (Miri.Interpreter.OpTy AnnealProv) := do
  let st ← get
  if st.stack.currentFrame?.isNone then
    throw (.stack .emptyStack)
  let (frame', layout) ← annealResolveAndCacheLocalLayout localDecls layouts localId none
  let operand ← match frame'.getLocalOperand localId with
    | .ok op => pure op
    | .error (.localExpectedLive _) => throw (.undefinedBehavior "read of dead local")
    | .error e => throw (.stack e)
  match operand with
  | .immediate .uninit =>
      throw (.undefinedBehavior "field read of uninitialized union")
  | .immediate _ =>
      throw (.unsupported "union local held as an initialized immediate")
  | .indirect mp =>
      let st ← get
      match Miri.Interpreter.projectField
          (annealUnionProjectionCx frame' layouts st.machine fieldTy)
          ⟨.indirect mp, layout⟩ idx with
      | .ok projected => return projected
      | .error err => throw (annealLiftProjectionError err)

/-- Evaluate a place with a `Subslice` projection on a memory-backed array
local. This is `annealEvalOperand`'s projected path with
`annealSubsliceProjectionCx` in place of `annealProjectionCx`: it requires the
array to be initialized in full, as Anneal's `MirSemantics` does for every
projected read, and then projects. -/
def annealEvalSubsliceOperand (localDecls : List LocalDecl) (layouts : LayoutTable)
    (place : Miri.MIR.Place) (known : Option Miri.Interpreter.LocalLayout) :
    Miri.Interpreter.RvalueM AnnealStepState (Miri.Interpreter.OpTy AnnealProv) := do
  let st ← get
  if st.stack.currentFrame?.isNone then
    throw (.stack .emptyStack)
  let (frame', layout) ← annealResolveAndCacheLocalLayout localDecls layouts place.localId known
  let operand ← match frame'.getLocalOperand place.localId with
    | .ok op => pure op
    | .error (.localExpectedLive _) => throw (.undefinedBehavior "read of dead local")
    | .error e => throw (.stack e)
  match operand with
  | .immediate .uninit =>
      throw (.undefinedBehavior "projected read of uninitialized local")
  | .indirect mp =>
      let st ← get
      match annealCheckIndirectInitialized st.machine mp layout.layout.size with
      | .error err => throw err
      | .ok () =>
          match annealProjectList (annealSubsliceProjectionCx frame' layouts st.machine)
              ⟨.indirect mp, layout⟩ place.projection.toList with
          | .ok projected => return projected
          | .error projErr => throw (annealLiftProjectionError projErr)
  | _ => throw (.unsupported "projected operand in scalar rvalue")

/-- Union- and subslice-aware operand evaluation: a single `Field` projection
of a union local goes to `annealEvalUnionField`, a projection list containing
a `Subslice` goes to `annealEvalSubsliceOperand`, and every other operand to
`annealEvalOperand`. -/
def annealEvalOperandLM2_4 (localDecls : List LocalDecl) (layouts : LayoutTable)
    (op : Miri.MIR.Operand) (known : Option Miri.Interpreter.LocalLayout) :
    Miri.Interpreter.RvalueM AnnealStepState (Miri.Interpreter.OpTy AnnealProv) :=
  match op with
  | .Copy place | .Move place =>
      match place.projection.toList with
      | [.Field idx fieldTy] =>
          if isUnionLocal localDecls layouts place.localId then
            annealEvalUnionField localDecls layouts place.localId idx fieldTy
          else
            annealEvalOperand localDecls layouts op known
      | projs =>
          if projs.any isSubsliceElem then
            annealEvalSubsliceOperand localDecls layouts place known
          else
            annealEvalOperand localDecls layouts op known
  | _ => annealEvalOperand localDecls layouts op known

/-- The destination place of a write to field `idx` (of MIR field type
`fieldTy`) of the union local `localId`.

A dead local is undefined behavior. A memory-backed union is projected with the
vendored `projectField` at offset `0`; unlike `annealEvalPlace`, this checks no
byte of the union, because writing a field initializes the field and Miri
requires nothing of the other bytes. A union that is still an immediate is
first moved to memory with the vendored `forceAllocation`, as the vendored
`asMplaceOrMutableLocal` and rustc's `as_mplace_or_mutable_local` do for every
write through a projected local; a fresh stack allocation starts uninitialized.

Both Anneal (`uninitFieldWriteShell?` + `writeProjectedValueUnionAware`) and
`lean-miri` (`forceAllocation` + `projectField` + `writeScalar`) support
projected field writes to an uninitialized union local (MIR that borrowck
rejects in surface Rust, yet `core::intrinsics::mir` can express), and
`step_union_field_write_uninit_simulation` certifies their lockstep equivalence. -/
def annealEvalUnionFieldPlace (localDecls : List LocalDecl) (layouts : LayoutTable)
    (localId idx : Nat) (fieldTy : Miri.MIR.TyId) :
    Miri.Interpreter.RvalueM AnnealStepState (Miri.Interpreter.RuntimePlace AnnealProv) := do
  let st ← get
  if st.stack.currentFrame?.isNone then
    throw (.stack .emptyStack)
  let frameIdx := st.stack.frames.size - 1
  let (frame', layout) ← annealResolveAndCacheLocalLayout localDecls layouts localId none
  let mp ← match frame'.getLocalOperand localId with
    | .error (.localExpectedLive _) => throw (.undefinedBehavior "projected write to dead local")
    | .error e => throw (.stack e)
    | .ok (.indirect mp) => pure mp
    | .ok (.immediate _) => do
        let forced ← Miri.Interpreter.forceAllocation (annealPlaceHooks localDecls layouts) ()
          ⟨.local frameIdx localId none frame'.localsIdentity, layout⟩
        pure forced.mplace
  let st ← get
  let some frame := st.stack.currentFrame?
    | throw (.stack .emptyStack)
  match Miri.Interpreter.projectField (annealUnionProjectionCx frame layouts st.machine fieldTy)
      ⟨.indirect mp, layout⟩ idx with
  | .ok ⟨.indirect fieldMp, fieldLayout⟩ => return ⟨.memory fieldMp, fieldLayout⟩
  | .ok ⟨.immediate _, _⟩ => throw (.unsupported "union field place resolved to an immediate")
  | .error err => throw (annealLiftProjectionError err)

/-- Run the vendored `Miri.Interpreter.forceAllocation` on `dest`, translating a
dead local (`StackError.localExpectedLive`) into `StepError.undefinedBehavior`
to match rustc's `err_ub!(DeadLocal)` and Anneal's `MirSemantics.evalStmt` (just
as `annealEvalOperand`, `annealWriteImmediateLM2_2`, and `annealEnsureAllocated` do;
upstream `forceAllocation` lifts `getLocalOperand` via `stackLift` as
`StepError.stack (.localExpectedLive _)`). -/
def annealForceUnionAllocation (localDecls : List LocalDecl) (layouts : LayoutTable)
    (dest : Miri.Interpreter.RuntimePlace AnnealProv) :
    Miri.Interpreter.RvalueM AnnealStepState (Miri.Interpreter.MPlaceTy AnnealProv) :=
  fun st =>
    match Miri.Interpreter.forceAllocation (annealPlaceHooks localDecls layouts) () dest st with
    | .error (.stack (.localExpectedLive _)) st' =>
        .error (.undefinedBehavior "write to dead local") st'
    | res => res

theorem annealForceUnionAllocation_of_ok {localDecls : List LocalDecl} {layouts : LayoutTable}
    {dest : Miri.Interpreter.RuntimePlace AnnealProv} {st st' : AnnealStepState}
    {forced : Miri.Interpreter.MPlaceTy AnnealProv}
    (h : Miri.Interpreter.forceAllocation (annealPlaceHooks localDecls layouts) () dest st =
      .ok forced st') :
    annealForceUnionAllocation localDecls layouts dest st = .ok forced st' := by
  unfold annealForceUnionAllocation
  rw [h]

/-- Resolve a destination `Place` containing a `Subslice` projection on a
memory-backed array local. This mirrors `annealEvalPlace`'s projected path with
`annealSubsliceProjectionCx` in place of `annealProjectionCx`. -/
def annealEvalSubslicePlace (localDecls : List LocalDecl) (layouts : LayoutTable)
    (place : Miri.MIR.Place) :
    Miri.Interpreter.RvalueM AnnealStepState (Miri.Interpreter.RuntimePlace AnnealProv) := do
  let st ← get
  if st.stack.currentFrame?.isNone then
    throw (.stack .emptyStack)
  let (frame', layout) ← annealResolveAndCacheLocalLayout localDecls layouts place.localId none
  match frame'.getLocalOperand place.localId with
  | .error (.localExpectedLive _) =>
      throw (.undefinedBehavior "projected write to dead local")
  | .error e =>
      throw (.stack e)
  | .ok (.immediate .uninit) =>
      throw (.undefinedBehavior "projected write to uninitialized local")
  | .ok (.immediate _) =>
      throw (.unsupported "projected destination place on immediate local")
  | .ok (.indirect mp) =>
      let st ← get
      match annealCheckIndirectInitialized st.machine mp layout.layout.size with
      | .error err => throw err
      | .ok () =>
          match annealProjectList
              (annealSubsliceProjectionCx frame' layouts st.machine)
              ⟨.indirect mp, layout⟩ place.projection.toList with
          | .ok ⟨.indirect elemMp, elemLayout⟩ =>
              return ⟨.memory elemMp, elemLayout⟩
          | .ok ⟨.immediate _, _⟩ =>
              throw (.unsupported "projected place resolved to immediate")
          | .error projErr =>
              throw (annealLiftProjectionError projErr)

/-- Union- and subslice-aware destination places: a single `Field` projection of
a union local goes to `annealEvalUnionFieldPlace`, a projection list containing
a `Subslice` goes to `annealEvalSubslicePlace`, and every other place to
`annealEvalPlace`. -/
def annealEvalPlaceLM2_4 (localDecls : List LocalDecl) (layouts : LayoutTable)
    (place : Miri.MIR.Place) :
    Miri.Interpreter.RvalueM AnnealStepState (Miri.Interpreter.RuntimePlace AnnealProv) :=
  match place.projection.toList with
  | [.Field idx fieldTy] =>
      if isUnionLocal localDecls layouts place.localId then
        annealEvalUnionFieldPlace localDecls layouts place.localId idx fieldTy
      else
        annealEvalPlace localDecls layouts place
  | projs =>
      if projs.any isSubsliceElem then
        annealEvalSubslicePlace localDecls layouts place
      else
        annealEvalPlace localDecls layouts place

/-! ## 4. Whole-Value Memory Copies -/

/-- Whether `copy_op` of `src` takes rustc's memory path: a memory-backed union
or array. rustc's `read_immediate_raw` returns a place, not an immediate, for
these layouts (`BackendRepr::Memory`, and `Scalar::Union`, which is not
`Scalar::Initialized`), and `copy_op_no_validate` then copies memory. -/
def usesMemCopy (src : Miri.Interpreter.OpTy AnnealProv) : Bool :=
  match src.op, src.layout.layout.fields with
  | .indirect _, .Union _ => true
  | .indirect _, .Array _ _ => true
  | _, _ => false

/-- Map an `AllocError` of a whole-value copy to a `StepError`. rustc reports a
copy between overlapping ranges, out of the bounds of an allocation, or into a
read-only allocation as undefined behavior; anything else here means the hooks
built a bad state. -/
def annealMemCopyError : Miri.Memory.AllocError → Miri.Interpreter.StepError
  | .copyRangesOverlap => .undefinedBehavior "whole-value copy between overlapping ranges"
  | .outOfBounds _ _ => .undefinedBehavior "whole-value copy out of bounds"
  | .readOnlyAllocation => .undefinedBehavior "write to read-only allocation"
  | _ => .unsupported "whole-value copy failed"

/-- rustc's `copy_op` slow path for a memory-backed source (`usesMemCopy`):
`dest.force_mplace` followed by `mem_copy(src, dest, dest_size,
nonoverlapping = true)`.

The destination is forced into memory with `annealForceUnionAllocation` (which wraps
the vendored `forceAllocation`, leaving an already memory-backed local in place
and reporting a dead destination local as undefined behavior). When `dest`'s
size is nonzero, the copy runs the vendored `Miri.Memory.Allocation.copy`
(`copyRepeatedly ... 1 ...`) for `dest`'s size in bytes from `src`: copying raw
bytes, copying the initialization mask chunk by chunk (`InitMask.prepareCopy` /
`prepareForOverwrite` / `applyCopy`), and copying provenance. No byte is read
as a value, so uninitialized union padding bytes are copied rather than
reported as undefined behavior.

When `dest`'s size is zero (such as an empty subslice `a[i..i]` of type
`[T; 0]`), `Allocation.copy` cannot be called directly because
`InitMask.prepareCopy` rejects empty copy ranges (in vendored Miri,
`MemoryCopyMachine.access` short-circuits zero-sized copies). This branch
checks `getBytesUnchecked` bounds on source and destination plus destination
mutability, and canonicalizes a zero-byte destination allocation's mask to
`InitMask.new Size.ZERO true` so empty array allocations satisfy
`ArraySliceRel.alloc_mask` and `annealCheckIndirectInitialized` (matching the
lazy-`true` mask convention documented at `Translate.lean`'s
`annealAggregateHooksLM2_2`). -/
def annealMemCopyOp (localDecls : List LocalDecl) (layouts : LayoutTable)
    (src : Miri.Interpreter.OpTy AnnealProv) (dest : Miri.Interpreter.RuntimePlace AnnealProv) :
    Miri.Interpreter.RvalueM AnnealStepState Unit := do
  match src.op with
  | .immediate imm => annealWriteImmediateLM2_2 imm dest
  | .indirect srcMp =>
      let forced ← annealForceUnionAllocation localDecls layouts dest
      let destMp := forced.mplace
      let st ← get
      let some srcId := srcMp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId
        | throw (.unsupported "copy source without an allocation")
      let some srcBase := st.machine.lookupBaseAddr srcId
        | throw (.unsupported "copy source without a base address")
      let some (_, srcLocal) := st.machine.memory.live.find? (fun (k, _) => k == srcId)
        | throw (.unsupported "copy source allocation not live")
      let some destId := destMp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId
        | throw (.unsupported "copy destination without an allocation")
      let some destBase := st.machine.lookupBaseAddr destId
        | throw (.unsupported "copy destination without a base address")
      let srcOff := Miri.ABI.Size.ofBytes (srcMp.ptr.offset.bytes - srcBase)
      let destOff := Miri.ABI.Size.ofBytes (destMp.ptr.offset.bytes - destBase)
      match st.machine.memory.live.findIdx? (fun (k, _) => k == destId) with
      | none => throw (.unsupported "copy destination allocation not live")
      | some destIdx =>
          match st.machine.memory.live[destIdx]? with
          | none => throw (.unsupported "copy destination allocation not live")
          | some (k, ⟨kind, destAlloc⟩) =>
              let size := dest.layout.layout.size
              if size.bytes == 0 then
                match Miri.Memory.Allocation.getBytesUnchecked srcLocal.allocation
                    (Miri.Memory.allocRange srcOff size),
                    Miri.Memory.Allocation.getBytesUnchecked destAlloc
                    (Miri.Memory.allocRange destOff size) with
                | .error err, _ => throw (annealMemCopyError err)
                | .ok _, .error err => throw (annealMemCopyError err)
                | .ok _, .ok _ =>
                    if destAlloc.mutability != .Mut then
                      throw (annealMemCopyError .readOnlyAllocation)
                    else if destAlloc.byteSize.bytes == 0 then
                      match Miri.Memory.Allocation.fromBytes #[] destAlloc.align .Mut with
                      | .ok zeroAlloc =>
                          set { st with machine := { st.machine with
                            memory := { st.machine.memory with
                              live := st.machine.memory.live.set! destIdx
                                (k, ⟨kind, zeroAlloc.withExtra destAlloc.extra⟩) } } }
                      | .error err => throw (annealMemCopyError err)
                    else
                      pure ()
              else
                match Miri.Memory.Allocation.copy srcLocal.allocation
                    (Miri.Memory.allocRange srcOff size) destOff
                    (Miri.ABI.Size.ofBytes 8) (srcId == destId) true destAlloc with
                | EStateM.Result.ok () destAlloc' =>
                    set { st with machine := { st.machine with
                      memory := { st.machine.memory with
                        live := st.machine.memory.live.set! destIdx (k, ⟨kind, destAlloc'⟩) } } }
                | EStateM.Result.error err _ => throw (annealMemCopyError err)

/-! ## 5. Aggregates, Rvalues, and Statements -/

/-- Project the destination of a union aggregate to field `idx`: force the union
local into memory with `annealForceUnionAllocation`, then project with the vendored
`projectField` (offset `0`), taking the field layout from the union's
`TypeLayout` (`annealUnionAggregateCx`). -/
def annealUnionAggregateField (localDecls : List LocalDecl) (layouts : LayoutTable)
    (dest : Miri.Interpreter.RuntimePlace AnnealProv) (idx : Nat) :
    Miri.Interpreter.RvalueM AnnealStepState (Miri.Interpreter.RuntimePlace AnnealProv) := do
  let forced ← annealForceUnionAllocation localDecls layouts dest
  let st ← get
  let some frame := st.stack.currentFrame?
    | throw (.stack .emptyStack)
  match Miri.Interpreter.projectField (annealUnionAggregateCx frame layouts st.machine)
      ⟨.indirect forced.mplace, dest.layout⟩ idx with
  | .ok ⟨.indirect fieldMp, fieldLayout⟩ => return ⟨.memory fieldMp, fieldLayout⟩
  | .ok ⟨.immediate _, _⟩ => throw (.unsupported "union field place resolved to an immediate")
  | .error err => throw (annealLiftProjectionError err)

/-- `annealAggregateHooksLM2_2` extended to union aggregates. A union has the single
variant `0`, so downcasting a union to variant `0` is the identity; projecting
a union to its active field goes to `annealUnionAggregateField`. Operands are
evaluated with `annealEvalOperandLM2_4`. -/
def annealAggregateHooksLM2_4 (localDecls : List LocalDecl) (layouts : LayoutTable) :
    Miri.Interpreter.AggregateHooks
      AnnealProv
      AnnealStepState
      Unit
      (Miri.Interpreter.RuntimePlace AnnealProv) :=
  let base := annealAggregateHooksLM2_2 localDecls layouts
  { base with
    evalOperand := fun _ op known => do
      let opTy ← annealEvalOperandLM2_4 localDecls layouts op known
      let imm ← annealReadImmediateLM2_2 opTy
      return ⟨.immediate imm.imm, imm.layout⟩
    evalOperandAt := fun _ _ op known => do
      let opTy ← annealEvalOperandLM2_4 localDecls layouts op known
      let imm ← annealReadImmediateLM2_2 opTy
      return ⟨.immediate imm.imm, imm.layout⟩
    projectDowncast := fun c dest variant =>
      if isUnionLayout dest.layout then
        if variant == 0 then pure dest
        else throw (.invalidProgram "union downcast to a nonzero variant")
      else
        base.projectDowncast c dest variant
    projectField := fun c dest idx =>
      if isUnionLayout dest.layout then
        annealUnionAggregateField localDecls layouts dest idx
      else
        base.projectField c dest idx
    copyOp := (annealAggregateHooks localDecls layouts).copyOp
    copyOpNoValidate := fun _ src dest _ => do
      let imm ← annealReadImmediateLM2_2 src
      annealWriteImmediateLM2_2 imm.imm dest
    writeDiscriminant := fun _ _ dest => do
      let _ ← annealEnsureAllocated dest
      pure () }

/-- `annealRvalueHooksLM2_2` with union- and subslice-aware places, operands, copies
(`annealMemCopyOp` for `usesMemCopy` sources), aggregates, and array repeats. -/
def annealRvalueHooksLM2_4 (localDecls : List LocalDecl) (layouts : LayoutTable) :
    Miri.Interpreter.RvalueHooks
      AnnealProv
      AnnealStepState
      Unit
      (Miri.Interpreter.RuntimePlace AnnealProv) :=
  let base := annealRvalueHooksLM2_2 localDecls layouts
  { base with
    evalPlace := fun _ p _ => annealEvalPlaceLM2_4 localDecls layouts p
    evalOperand := fun _ op known => annealEvalOperandLM2_4 localDecls layouts op known
    evalOperandAt := fun _ _ op known => annealEvalOperandLM2_4 localDecls layouts op known
    evalPlaceToOp := fun _ p known => annealEvalOperandLM2_4 localDecls layouts (.Copy p) known
    copyOp := fun _ src dest =>
      if usesMemCopy src then annealMemCopyOp localDecls layouts src dest
      else do
        let imm ← annealReadImmediateLM2_2 src
        annealWriteImmediateLM2_2 imm.imm dest
    copyOpAllowTransmute := fun _ src dest =>
      if usesMemCopy src then annealMemCopyOp localDecls layouts src dest
      else do
        let imm ← annealReadImmediateLM2_2 src
        annealWriteImmediateLM2_2 imm.imm dest
    writeAggregate := fun c k os d =>
      Miri.Interpreter.writeAggregate (annealAggregateHooksLM2_4 localDecls layouts) c k os d
    writeRepeat := fun c o d =>
      Miri.Interpreter.writeRepeat (annealAggregateHooksLM2_4 localDecls layouts) c o d }

/-- Whether place `p` mentions a union local or a `Subslice` projection. -/
def lm24Place (localDecls : List LocalDecl) (layouts : LayoutTable) (p : Miri.MIR.Place) : Bool :=
  isUnionLocal localDecls layouts p.localId || p.projection.any isSubsliceElem

/-- Whether operand `op` reads a place that `lm24Place` accepts. -/
def lm24Operand (localDecls : List LocalDecl) (layouts : LayoutTable) :
    Miri.MIR.Operand → Bool
  | .Copy p | .Move p => lm24Place localDecls layouts p
  | _ => false

/-- Whether rvalue `rv` has an operand that `lm24Operand` accepts. -/
def lm24Rvalue (localDecls : List LocalDecl) (layouts : LayoutTable) :
    Miri.MIR.Rvalue → Bool
  | .Use op _ => lm24Operand localDecls layouts op
  | .Repeat op _ => lm24Operand localDecls layouts op
  | .Cast _ op _ => lm24Operand localDecls layouts op
  | .UnaryOp _ op => lm24Operand localDecls layouts op
  | .BinaryOp _ l r => lm24Operand localDecls layouts l || lm24Operand localDecls layouts r
  | .Aggregate _ ops => ops.any (lm24Operand localDecls layouts)
  | .WrapUnsafeBinder op _ => lm24Operand localDecls layouts op
  | _ => false

/-- Whether the assignment `place = rv` runs the `LM-2.4` leaves: its
destination or one of its operands mentions a union local or a `Subslice`. -/
def lm24Assign (localDecls : List LocalDecl) (layouts : LayoutTable)
    (place : Miri.MIR.Place) (rv : Miri.MIR.Rvalue) : Bool :=
  lm24Place localDecls layouts place || lm24Rvalue localDecls layouts rv

/-- `annealStepHooksLM2_2` with the `LM-2.4` union and subslice leaves: an
assignment that `lm24Assign` accepts runs `evalRvalueIntoPlace` with
`annealRvalueHooksLM2_4`, and every other assignment and every other statement
or terminator runs `annealStepHooksLM2_2` unchanged. -/
def annealStepHooksLM2_4 (localDecls : List LocalDecl := .nil)
    (layouts : LayoutTable := emptyLayoutTable) :
    Miri.Interpreter.StepHooks
      AnnealProv
      Miri.Interpreter.LocalLayout
      Unit
      AnnealMachine
      Unit
      (Miri.Interpreter.RuntimePlace AnnealProv) :=
  let base := annealStepHooksLM2_2 localDecls layouts
  { base with
    assign := fun choice place rvalue state =>
      if lm24Assign localDecls layouts place rvalue then
        Miri.Interpreter.runRvalue
          (Miri.Interpreter.evalRvalueIntoPlace (annealRvalueHooksLM2_4 localDecls layouts)
            choice rvalue place)
          state
      else
        base.assign choice place rvalue state }

/-! ## 6. Conservative Extension of `annealStepHooksLM2_2` -/

/-- An assignment that `lm24Assign` rejects runs `annealStepHooksLM2_2`'s
`assign`. -/
theorem annealStepHooksLM2_4_assign_of_not_lm24
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (place : Miri.MIR.Place) (rv : Miri.MIR.Rvalue)
    (h : lm24Assign localDecls layouts place rv = false)
    (state : AnnealStepState) :
    (annealStepHooksLM2_4 localDecls layouts).assign () place rv state =
      (annealStepHooksLM2_2 localDecls layouts).assign () place rv state := by
  simp only [annealStepHooksLM2_4, h, Bool.false_eq_true, ↓reduceIte]

/-- Whether statement `stmt` is an assignment that `lm24Assign` accepts. -/
def lm24Stmt (localDecls : List LocalDecl) (layouts : LayoutTable)
    (stmt : Miri.MIR.Statement) : Bool :=
  match stmt.kind with
  | .Assign place rv => lm24Assign localDecls layouts place rv
  | _ => false

/-- Every statement that `lm24Stmt` rejects evaluates identically under
`annealStepHooksLM2_4` and `annealStepHooksLM2_2`. -/
theorem evalStatement_LM2_4_of_not_lm24
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (stmt : Miri.MIR.Statement) (h : lm24Stmt localDecls layouts stmt = false)
    (state : AnnealStepState) :
    Miri.Interpreter.Step.evalStatement (annealStepHooksLM2_4 localDecls layouts) () stmt state =
      Miri.Interpreter.Step.evalStatement (annealStepHooksLM2_2 localDecls layouts) () stmt state := by
  unfold Miri.Interpreter.Step.evalStatement
  unfold lm24Stmt at h
  split
  · rename_i place rv hk
    rw [hk] at h
    exact annealStepHooksLM2_4_assign_of_not_lm24 localDecls layouts place rv h state
  all_goals rfl

/-- A body none of whose statements `lm24Stmt` accepts. -/
def BodyFreeOfLM2_4 (localDecls : List LocalDecl) (layouts : LayoutTable)
    (body : Miri.MIR.Body) : Prop :=
  ∀ (bb : Miri.MIR.BasicBlock) (stmt : Miri.MIR.Statement),
    bb ∈ body.basicBlocks → stmt ∈ bb.statements → lm24Stmt localDecls layouts stmt = false

/-- On a body free of union and subslice assignments, `annealStepHooksLM2_4`
takes exactly the steps of `annealStepHooksLM2_2`, from every state whose frames all
run that body. Every `lean-miri` theorem about `annealStepHooksLM2_2` therefore holds
verbatim for `annealStepHooksLM2_4` on such bodies. -/
theorem step_LM2_4_eq_of_bodyFree
    (localDecls : List LocalDecl) (layouts : LayoutTable) (mbody : Miri.MIR.Body)
    (hfree : BodyFreeOfLM2_4 localDecls layouts mbody)
    (m : AnnealStepState)
    (hbody : ∀ frame, m.stack.currentFrame? = some frame → frame.body = mbody) :
    Miri.Interpreter.Step.step (annealStepHooksLM2_4 localDecls layouts) () m =
      Miri.Interpreter.Step.step (annealStepHooksLM2_2 localDecls layouts) () m := by
  unfold Miri.Interpreter.Step.step
  cases hcur : m.stack.currentFrame? with
  | none => rfl
  | some frame =>
    have hfb := hbody frame hcur
    dsimp only
    cases hloc : frame.location with
    | unwinding _ => rfl
    | mir loc =>
      dsimp only
      cases hblk : frame.body.basicBlocks[loc.block]? with
      | none => rfl
      | some block =>
        dsimp only
        cases hst : block.statements[loc.statementIndex]? with
        | none => rfl
        | some stmt =>
          dsimp only
          have hblk_mem : block ∈ mbody.basicBlocks := by
            rw [← hfb]; exact Array.mem_of_getElem? hblk
          have hst_mem : stmt ∈ block.statements := Array.mem_of_getElem? hst
          rw [evalStatement_LM2_4_of_not_lm24 localDecls layouts stmt
            (hfree block stmt hblk_mem hst_mem) m]

/-! ## 7. Union Initialization Masks

A union of primitive scalar fields has size `S ∈ {1, 2, 4, 8, 16}`, and each of
its fields occupies the prefix `[0, k)` of its bytes for a `k` of the same
form. Writing one field into a fresh, uninitialized union initializes exactly
that prefix. The lemmas below evaluate the vendored `InitMask` operations on the
resulting mask for every such `S` and `k`. -/

/-- The initialization mask of an `S`-byte allocation whose bytes `[0, k)` are
initialized and whose bytes `[k, S)` are not, in the representation that
`InitMask.setRange` produces from a fresh, uninitialized mask: lazy when every
byte is initialized, and otherwise one materialized 64-bit block whose bits
`[0, k)` are set. -/
def unionPrefixMask (S k : Nat) : Miri.Memory.InitMask :=
  if k = S then Miri.Memory.InitMask.new (translateSizeBytes S) true
  else ⟨.Materialized ⟨#[UInt64.ofNat (2 ^ k - 1)]⟩, translateSizeBytes S⟩

/-- Writing the first `k` bytes of a fresh, uninitialized `S`-byte allocation
initializes exactly `[0, k)`. -/
theorem unionPrefixMask_fresh {S k : Nat} (hS : ValidScalarBytes S)
    (hk : ValidScalarBytes k) (hle : k ≤ S) :
    (Miri.Memory.InitMask.new (translateSizeBytes S) false).setRange
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes k)) true =
      .ok (unionPrefixMask S k) := by
  rcases hS with rfl | rfl | rfl | rfl | rfl <;> rcases hk with rfl | rfl | rfl | rfl | rfl <;>
    first | omega | with_unfolding_all decide

/-- Rewriting the initialized prefix `[0, k)` leaves the mask unchanged. -/
theorem unionPrefixMask_rewrite {S k : Nat} (hS : ValidScalarBytes S)
    (hk : ValidScalarBytes k) (hle : k ≤ S) :
    (unionPrefixMask S k).setRange
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes k)) true =
      .ok (unionPrefixMask S k) := by
  rcases hS with rfl | rfl | rfl | rfl | rfl <;> rcases hk with rfl | rfl | rfl | rfl | rfl <;>
    first | omega | with_unfolding_all decide

/-- Every prefix `[0, j)` with `j ≤ k` is initialized. -/
theorem unionPrefixMask_init {S k j : Nat} (hS : ValidScalarBytes S)
    (hk : ValidScalarBytes k) (hj : ValidScalarBytes j) (hle : k ≤ S) (hjk : j ≤ k) :
    (unionPrefixMask S k).isRangeInitialized
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes j)) = .ok (.ok ()) := by
  rcases hS with rfl | rfl | rfl | rfl | rfl <;> rcases hk with rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl <;>
    first | omega | with_unfolding_all decide

/-- Every prefix `[0, j)` with `k < j ≤ S` contains an uninitialized byte: the
vendored query reports the uninitialized subrange (not an internal error). -/
theorem unionPrefixMask_uninit {S k j : Nat} (hS : ValidScalarBytes S)
    (hk : ValidScalarBytes k) (hj : ValidScalarBytes j) (hkj : k < j) (hjS : j ≤ S) :
    ∃ bad, (unionPrefixMask S k).isRangeInitialized
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes j)) = .ok (.error bad) := by
  rcases hS with rfl | rfl | rfl | rfl | rfl <;> rcases hk with rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl <;>
    first | omega | exact ⟨_, by with_unfolding_all rfl⟩

/-- The whole `S`-byte range is initialized exactly when `k = S`: for `k < S`
the bytes `[k, S)` of the union remain uninitialized. -/
theorem unionPrefixMask_whole_iff {S k : Nat} (hS : ValidScalarBytes S)
    (hk : ValidScalarBytes k) (hle : k ≤ S) :
    (unionPrefixMask S k).isRangeInitialized
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S)) = .ok (.ok ()) ↔
      k = S := by
  constructor
  · intro h
    rcases Nat.lt_or_ge k S with hlt | hge
    · obtain ⟨bad, hbad⟩ := unionPrefixMask_uninit hS hk hS hlt (Nat.le_refl S)
      rw [hbad] at h
      cases h
    · omega
  · rintro rfl
    exact unionPrefixMask_init hS hS hS (Nat.le_refl _) (Nat.le_refl _)

/-- The vendored mask half of `Allocation.copy` (rustc's `mem_copy`) applied to
a union mask: the destination range is first marked initialized
(`prepareForOverwrite`), and `InitMask.prepareCopy` / `InitMask.applyCopy` then
copy the source's initialized and uninitialized chunks. -/
def vendoredUnionMaskCopy (S : Nat) (dest src : Miri.Memory.InitMask) :
    Except Miri.Memory.InitMaskError Miri.Memory.InitMask := do
  let range := Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S)
  let defined ← src.prepareCopy range
  let cleared ← dest.setRange range true
  cleared.applyCopy defined range 1

/-- The initialization mask produced by `vendoredUnionMaskCopy`
(`Allocation.copy`) when copying a union with `[0, k)` initialized into an
`S`-byte allocation. -/
def unionCopiedPrefixMask (S k : Nat) : Miri.Memory.InitMask :=
  if k = S then
    ⟨.Lazy true, translateSizeBytes S⟩
  else
    ⟨.Materialized ⟨#[UInt64.ofNat (18446744073709551615 - ((2 ^ S - 1) - (2 ^ k - 1)))]⟩,
      translateSizeBytes S⟩

/-- Valid `InitMask` representations for an `S`-byte union whose bytes `[0, k)`
are initialized and whose bytes `[k, S)` are uninitialized: either the fresh
write mask `unionPrefixMask S k` or the chunk-copied mask
`unionCopiedPrefixMask S k` produced by `Allocation.copy`. -/
def IsUnionPrefixMask (S k : Nat) (M : Miri.Memory.InitMask) : Prop :=
  M = unionPrefixMask S k ∨ M = unionCopiedPrefixMask S k

theorem IsUnionPrefixMask.of_fresh (S k : Nat) :
    IsUnionPrefixMask S k (unionPrefixMask S k) :=
  Or.inl rfl

theorem IsUnionPrefixMask.of_copied (S k : Nat) :
    IsUnionPrefixMask S k (unionCopiedPrefixMask S k) :=
  Or.inr rfl

theorem IsUnionPrefixMask.init {S k j : Nat} {M : Miri.Memory.InitMask}
    (hM : IsUnionPrefixMask S k M) (hS : ValidScalarBytes S)
    (hk : ValidScalarBytes k) (hj : ValidScalarBytes j) (hle : k ≤ S) (hjk : j ≤ k) :
    M.isRangeInitialized
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes j)) = .ok (.ok ()) := by
  rcases hM with rfl | rfl
  · exact unionPrefixMask_init hS hk hj hle hjk
  · rcases hS with rfl | rfl | rfl | rfl | rfl <;> rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      first | omega | with_unfolding_all decide

theorem IsUnionPrefixMask.uninit {S k j : Nat} {M : Miri.Memory.InitMask}
    (hM : IsUnionPrefixMask S k M) (hS : ValidScalarBytes S)
    (hk : ValidScalarBytes k) (hj : ValidScalarBytes j) (hkj : k < j) (hjS : j ≤ S) :
    ∃ bad, M.isRangeInitialized
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes j)) = .ok (.error bad) := by
  rcases hM with rfl | rfl
  · exact unionPrefixMask_uninit hS hk hj hkj hjS
  · rcases hS with rfl | rfl | rfl | rfl | rfl <;> rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      first | omega | exact ⟨_, by with_unfolding_all rfl⟩

theorem IsUnionPrefixMask.whole_iff {S k : Nat} {M : Miri.Memory.InitMask}
    (hM : IsUnionPrefixMask S k M) (hS : ValidScalarBytes S)
    (hk : ValidScalarBytes k) (hle : k ≤ S) :
    M.isRangeInitialized
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S)) = .ok (.ok ()) ↔
      k = S := by
  constructor
  · intro h
    rcases Nat.lt_or_ge k S with hlt | hge
    · obtain ⟨bad, hbad⟩ := hM.uninit hS hk hS hlt (Nat.le_refl S)
      rw [hbad] at h
      cases h
    · omega
  · rintro rfl
    exact hM.init hS hS hS (Nat.le_refl _) (Nat.le_refl _)

theorem IsUnionPrefixMask.setRange_ge {S k k' : Nat} {M : Miri.Memory.InitMask}
    (hM : IsUnionPrefixMask S k M) (hS : ValidScalarBytes S)
    (hk : ValidScalarBytes k) (hk' : ValidScalarBytes k') (hkk' : k ≤ k') (hk'S : k' ≤ S) :
    ∃ M', M.setRange
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes k')) true = .ok M' ∧
      IsUnionPrefixMask S k' M' := by
  rcases hM with rfl | rfl
  · refine ⟨unionPrefixMask S k', ?_, .of_fresh S k'⟩
    rcases hS with rfl | rfl | rfl | rfl | rfl <;> rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk' with rfl | rfl | rfl | rfl | rfl <;>
      first | omega | with_unfolding_all decide
  · refine ⟨unionCopiedPrefixMask S k', ?_, .of_copied S k'⟩
    rcases hS with rfl | rfl | rfl | rfl | rfl <;> rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk' with rfl | rfl | rfl | rfl | rfl <;>
      first | omega | with_unfolding_all decide

theorem IsUnionPrefixMask.get_byte {S k : Nat} {M : Miri.Memory.InitMask}
    (hM : IsUnionPrefixMask S k M) (hS : ValidScalarBytes S)
    (hk : ValidScalarBytes k) (hle : k ≤ S) :
    ∀ i < S, M.get (Miri.ABI.Size.ofBytes (UInt64.ofNat i)) = .ok (decide (i < k)) := by
  rcases hM with rfl | rfl <;>
    rcases hS with rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl <;>
    first
    | omega
    | with_unfolding_all decide

/-- **Certification of the `I-11` chunk copy.** For every union mask, the
vendored chunk copy into any `S`-byte destination (initialized or not) yields a
mask that initializes exactly the source's prefix `[0, k)`: it neither drops an
initialized chunk nor initializes the uninitialized bytes `[k, S)`. -/
theorem unionPrefixMask_vendoredCopy {S k : Nat} (hS : ValidScalarBytes S)
    (hk : ValidScalarBytes k) (hle : k ≤ S) (destInit : Bool) :
    ∃ M, vendoredUnionMaskCopy S (Miri.Memory.InitMask.new (translateSizeBytes S) destInit)
        (unionPrefixMask S k) = .ok M ∧
      ∀ j, ValidScalarBytes j → j ≤ S →
        (M.isRangeInitialized
            (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes j)) = .ok (.ok ()) ↔
          j ≤ k) := by
  rcases hS with rfl | rfl | rfl | rfl | rfl <;> rcases hk with rfl | rfl | rfl | rfl | rfl <;>
    first
    | omega
    | (cases destInit <;>
        refine ⟨_, by with_unfolding_all rfl, ?_⟩ <;>
        intro j hj hjS <;>
        rcases hj with rfl | rfl | rfl | rfl | rfl <;>
        first | omega | with_unfolding_all decide)

/-! ## 8. Union Allocations

Writes and reads at offset `0` of an allocation with an arbitrary
initialization mask. `AllocLM2_1` proves the same round trip for allocations
whose mask is lazily initialized in full; a union's mask is not. As there,
each private `lean-miri` helper that the vendored definitions call is replicated
below and identified with the original by `rfl`. -/

/-- The raw bytes of an allocation (its private `rawBytes` field). -/
def unionAllocRaw {P E : Type} (a : Miri.Memory.Allocation P E) : Array UInt8 :=
  Miri.Memory.Allocation.casesOn (motive := fun _ => Array UInt8) a
    (fun raw _ _ _ _ _ _ _ => raw)

private def uCheckedSlice {P E : Type} (allocation : Miri.Memory.Allocation P E)
    (range : Miri.Memory.AllocRange) : Except Miri.Memory.AllocError (Array UInt8) := do
  if (unionAllocRaw allocation).size != allocation.byteSize.bytes.toNat then
    throw (.storageLengthMismatch allocation.byteSize (unionAllocRaw allocation).size)
  let finish ← range.endExclusive |>.mapError Miri.Memory.AllocError.memory
  if range.start.bytes > finish.bytes || finish.bytes > allocation.byteSize.bytes then
    throw (.outOfBounds range allocation.byteSize)
  return (unionAllocRaw allocation).extract range.start.bytes.toNat finish.bytes.toNat

private theorem u_getBytesUnchecked_eq {P E : Type}
    (allocation : Miri.Memory.Allocation P E) (range : Miri.Memory.AllocRange) :
    Miri.Memory.Allocation.getBytesUnchecked allocation range =
      uCheckedSlice allocation range := rfl

private def uPointerSize (layout : Miri.ABI.TargetDataLayout) : Miri.ABI.Size :=
  Miri.ABI.Size.fromBits layout.pointerWidth.bits

private def uTargetUIntBytes (layout : Miri.ABI.TargetDataLayout)
    (size : Miri.ABI.Size) (bits : Miri.ABI.U128) :
    Except Miri.Memory.AllocError (Array UInt8) := do
  if size.bytes > 16 then throw (.scalarBytesTooWide size)
  let count := size.bytes.toNat
  let mut result := #[]
  for index in [:count] do
    let valueIndex := if layout.endian == .little then index else count - index - 1
    let byte := (bits.toNat / 2 ^ (8 * valueIndex)) % 256
    result := result.push (UInt8.ofNat byte)
  return result

private def uReadTargetUInt (layout : Miri.ABI.TargetDataLayout)
    (bytes : Array UInt8) : Except Miri.Memory.AllocError Miri.ABI.U128 := do
  if bytes.size > 16 then
    throw (.scalarBytesTooWide (Miri.ABI.Size.ofBytes (UInt64.ofNat bytes.size)))
  let mut value := 0
  for index in [:bytes.size] do
    let some byte := bytes[index]? | throw (.invalidSliceEndpoints index (index + 1) bytes.size)
    let valueIndex := if layout.endian == .little then index else bytes.size - index - 1
    value := value + byte.toNat * 2 ^ (8 * valueIndex)
  return BitVec.ofNat 128 value

private def uReadScalar {P E : Type} [DecidableEq P] [Miri.Memory.PointerProvenance P]
    (allocation : Miri.Memory.Allocation P E) (layout : Miri.ABI.TargetDataLayout)
    (range : Miri.Memory.AllocRange) (readProvenance : Bool) :
    Except Miri.Memory.AllocError (Miri.Memory.Scalar P) := do
  match ← (allocation.initializationMask.isRangeInitialized range).mapError
      Miri.Memory.AllocError.memory with
  | .error bad => throw (.invalidUninitBytes (some ⟨range, bad⟩))
  | .ok () => pure ()
  let bytes ← Miri.Memory.Allocation.getBytesUnchecked allocation range
  let bits ← uReadTargetUInt layout bytes
  if readProvenance then
    let targetSize := uPointerSize layout
    if range.size != targetSize then
      throw (.scalarPointerNotTargetSized range.size targetSize)
    let provenance ← match allocation.provenanceMap.readPtr range.start targetSize with
      | .ok provenance => pure provenance
      | .error (.readPartialPointer offset) => throw (.readPartialPointer offset)
      | .error reason => throw (.provenance reason)
    match provenance with
    | some provenance =>
      if bits.toNat > 18446744073709551615 then
        throw (.pointerBitsDoNotFitOffset bits)
      return Miri.Memory.Scalar.fromPointer layout
        (Miri.Memory.Pointer.new provenance (Miri.ABI.Size.ofBytes (UInt64.ofNat bits.toNat)))
    | none =>
      let scalar ← (Miri.Memory.Scalar.fromUInt bits range.size).mapError
        Miri.Memory.AllocError.scalar
      return scalar
  else
    if Miri.Memory.PointerProvenance.offsetIsAddr (Prov := P) then
      let scalar ← (Miri.Memory.Scalar.fromUInt bits range.size).mapError
        Miri.Memory.AllocError.scalar
      return scalar
    let isEmpty ←
      (allocation.provenanceMap.rangeEmpty range (uPointerSize layout)).mapError
        Miri.Memory.AllocError.provenance
    if isEmpty then
      let scalar ← (Miri.Memory.Scalar.fromUInt bits range.size).mapError
        Miri.Memory.AllocError.scalar
      return scalar
    throw (.readPointerAsInt none)

private theorem u_readScalar_eq {P E : Type} [DecidableEq P]
    [Miri.Memory.PointerProvenance P]
    (allocation : Miri.Memory.Allocation P E) (layout : Miri.ABI.TargetDataLayout)
    (range : Miri.Memory.AllocRange) (readProvenance : Bool) :
    allocation.readScalar layout range readProvenance =
      uReadScalar allocation layout range readProvenance := rfl

private theorem u_encode_loop (x : Nat) (l : List Nat) (acc : Array UInt8) :
    forIn (m := Except Miri.Memory.AllocError) l acc
        (fun index (r : Array UInt8) => pure (ForInStep.yield
          (r.push (UInt8.ofNat (x / 2 ^ (8 * index) % 256))))) =
      .ok (acc ++ (l.map fun i => UInt8.ofNat (x / 2 ^ (8 * i) % 256)).toArray) := by
  induction l generalizing acc with
  | nil => simp [pure, Except.pure]
  | cons i l ih =>
    rw [List.forIn_cons, pure_bind]
    simp only
    rw [ih]
    congr 1
    apply Array.toList_inj.mp
    simp

private theorem uTargetUIntBytes_spec (size : Miri.ABI.Size) (bits : Miri.ABI.U128)
    (hle : size.bytes.toNat ≤ 16) :
    uTargetUIntBytes annealTargetDataLayout size bits =
      .ok (allocLeBytes bits.toNat size.bytes.toNat) := by
  have small : ¬ size.bytes > 16 := by
    simp only [GT.gt, UInt64.lt_iff_toNat_lt]
    simpa using Nat.not_lt.mpr hle
  have hle' : (annealTargetDataLayout.endian == Miri.ABI.Endian.little) = true := rfl
  unfold uTargetUIntBytes
  simp only [small, ↓reduceIte, Std.Legacy.Range.forIn_eq_forIn_range', hle',
    Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, bind_pure]
  rw [u_encode_loop]
  simp [allocLeBytes]

private def uLeSum (x k : Nat) : Nat → Nat
  | 0 => 0
  | m + 1 => x / 2 ^ (8 * k) % 256 * 2 ^ (8 * k) + uLeSum x (k + 1) m

private theorem uLeSum_spec (x : Nat) :
    ∀ m k, x % 2 ^ (8 * k) + uLeSum x k m = x % 2 ^ (8 * (k + m)) := by
  intro m
  induction m with
  | zero => intro k; simp [uLeSum]
  | succ m ih =>
    intro k
    have hstep : x % 2 ^ (8 * k) + x / 2 ^ (8 * k) % 256 * 2 ^ (8 * k) =
        x % 2 ^ (8 * (k + 1)) := by
      rw [show 8 * (k + 1) = 8 * k + 8 by omega, Nat.pow_add, Nat.mod_mul]
      simp only [show (2 : Nat) ^ 8 = 256 by rfl]
      rw [Nat.mul_comm (2 ^ (8 * k))]
    simp only [uLeSum]
    rw [← Nat.add_assoc, hstep, ih (k + 1), show k + 1 + m = k + (m + 1) by omega]

private theorem u_decode_loop (x n : Nat)
    (f : Nat → Nat → Except Miri.Memory.AllocError (ForInStep Nat))
    (hf : ∀ index s, index < n →
      f index s = .ok (.yield (s + x / 2 ^ (8 * index) % 256 * 2 ^ (8 * index)))) :
    ∀ m k acc, k + m ≤ n →
      forIn (List.range' k m) acc f = .ok (acc + uLeSum x k m) := by
  intro m
  induction m with
  | zero => intro k acc _; simp [uLeSum, pure, Except.pure]
  | succ m ih =>
    intro k acc hkm
    rw [List.range'_succ, List.forIn_cons, hf k acc (by omega)]
    simp only [uLeSum]
    rw [show (Except.ok (ForInStep.yield (acc + x / 2 ^ (8 * k) % 256 * 2 ^ (8 * k))) :
        Except Miri.Memory.AllocError (ForInStep Nat)) = pure (ForInStep.yield _) from rfl,
      pure_bind]
    simp only
    rw [ih (k + 1) _ (by omega), Nat.add_assoc]

private theorem uReadTargetUInt_leBytes (x n : Nat) (hn : n ≤ 16) :
    uReadTargetUInt annealTargetDataLayout (allocLeBytes x n) =
      .ok (BitVec.ofNat 128 (x % 2 ^ (8 * n))) := by
  have small : ¬ n > 16 := by omega
  have hle : (annealTargetDataLayout.endian == Miri.ABI.Endian.little) = true := rfl
  unfold uReadTargetUInt
  simp only [allocLeBytes_size, small, ↓reduceIte, Std.Legacy.Range.forIn_eq_forIn_range',
    hle, Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  rw [u_decode_loop x n _ ?hf n 0 0 (by omega)]
  · have := uLeSum_spec x n 0
    simp only [Nat.mul_zero, Nat.pow_zero, Nat.mod_one, Nat.zero_add] at this
    simp [this, pure, Except.pure, bind, Except.bind]
  · intro index s hi
    have hb : (x / 2 ^ (8 * index) % 256) < 256 := Nat.mod_lt _ (by decide)
    simp [allocLeBytes, hi, pure, Except.pure, Nat.mod_eq_of_lt hb]

private theorem u_scalarModulus_eq_two_pow (sz : Nat) :
    scalarModulus sz = 2 ^ (8 * sz) := by
  induction sz with
  | zero => rfl
  | succ k ih =>
    show 256 * scalarModulus k = 2 ^ (8 * (k + 1))
    rw [ih, show 8 * (k + 1) = 8 * k + 8 by omega, Nat.pow_add, Nat.mul_comm]

private theorem u_scalarInt_ext {a b : Miri.Memory.ScalarInt}
    (hd : a.data = b.data) (hs : a.size = b.size) : a = b := by
  cases a
  cases b
  simp only [Miri.Memory.ScalarInt.data, Miri.Memory.ScalarInt.size] at hd hs
  subst hd
  subst hs
  rfl

private theorem u_fromUInt {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    (hrel : ScalarRel sc msc) :
    Miri.Memory.Scalar.fromUInt (Prov := AnnealProv) (BitVec.ofNat 128 sc.bits)
        (translateSizeBytes sc.sizeBytes) = .ok (Miri.Memory.Scalar.fromScalarInt msc) := by
  obtain ⟨msc', htry, hrel'⟩ := scalarInt_tryFromUInt_of_valid hrel.validBytes hrel.canonical
  have heq : msc' = msc :=
    u_scalarInt_ext (hrel'.data_eq.trans hrel.data_eq.symm)
      (hrel'.size_eq.trans hrel.size_eq.symm)
  subst heq
  unfold Miri.Memory.Scalar.fromUInt
  simp [htry, Except.mapError, bind, Except.bind, pure, Except.pure]

private theorem u_toBitsOrPtrInternal {sc : MirAst.ScalarInt}
    {msc : Miri.Memory.ScalarInt} (hrel : ScalarRel sc msc) :
    (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) msc).toBitsOrPtrInternal
        (translateSizeBytes sc.sizeBytes) = .ok (.bits (BitVec.ofNat 128 sc.bits)) := by
  unfold Miri.Memory.Scalar.toBitsOrPtrInternal
  simp only [Miri.Memory.Scalar.fromScalarInt, hrel.toBits_eq, Except.mapError, bind,
    Except.bind, pure, Except.pure]

private theorem u_checkedSlice_prefix {P E : Type}
    {A : Miri.Memory.Allocation P E} {S n : Nat}
    (hlen : A.len = S) (hsz : A.byteSize = translateSizeBytes S) (hS : S ≤ 16) (hn : n ≤ S) :
    uCheckedSlice A (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes n)) =
      .ok ((unionAllocRaw A).extract 0 n) := by
  have hSn : (translateSizeBytes S).bytes.toNat = S := by
    simp only [translateSizeBytes, Miri.ABI.Size.ofBytes, UInt64.toNat_ofNat']
    exact Nat.mod_eq_of_lt (by omega)
  have hnn : (translateSizeBytes n).bytes.toNat = n := by
    simp only [translateSizeBytes, Miri.ABI.Size.ofBytes, UInt64.toNat_ofNat']
    exact Nat.mod_eq_of_lt (by omega)
  have hlt : Miri.ABI.Size.ZERO.bytes.toNat + (translateSizeBytes n).bytes.toNat < 2 ^ 64 := by
    rw [hnn]; simp [Miri.ABI.Size.ZERO]; omega
  have hend := allocRange_endExclusive_of_lt hlt
  have hraw : (unionAllocRaw A).size = A.byteSize.bytes.toNat := by
    rw [hsz, hSn]; exact hlen
  have hfin : (Miri.ABI.Size.ofBytes
      (Miri.ABI.Size.ZERO.bytes + (translateSizeBytes n).bytes)).bytes.toNat = n := by
    simp only [Miri.ABI.Size.ofBytes, Miri.ABI.Size.ZERO, UInt64.zero_add]
    exact hnn
  have hle2 : ¬ (Miri.ABI.Size.ofBytes
      (Miri.ABI.Size.ZERO.bytes + (translateSizeBytes n).bytes)).bytes > A.byteSize.bytes := by
    rw [GT.gt, UInt64.lt_iff_toNat_lt, hfin, hsz, hSn]; omega
  have hle1 : ¬ (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes n)).start.bytes >
      (Miri.ABI.Size.ofBytes (Miri.ABI.Size.ZERO.bytes + (translateSizeBytes n).bytes)).bytes := by
    rw [GT.gt, UInt64.lt_iff_toNat_lt, hfin]
    simp [Miri.Memory.allocRange, Miri.ABI.Size.ZERO]
  unfold uCheckedSlice
  rw [hend]
  simp only [hraw, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, Except.mapError, bind,
    Except.bind, hle1, hle2, Bool.or_self, pure, Except.pure]
  simp only [decide_false, Bool.false_eq_true, ↓reduceIte, hfin]
  rfl

/-- Reading `[0, n)` (without provenance) of an allocation whose bytes `[0, n)`
are initialized and hold the little-endian encoding of a related scalar of
size `n` returns that scalar. -/
theorem union_readScalar_prefix {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    (hrel : ScalarRel sc msc) {E : Type} {B : Miri.Memory.Allocation AnnealProv E} {S : Nat}
    (hlen : B.len = S) (hsz : B.byteSize = translateSizeBytes S) (hS : S ≤ 16)
    (hle : sc.sizeBytes ≤ S)
    (hinit : B.initializationMask.isRangeInitialized
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes sc.sizeBytes)) =
        .ok (.ok ()))
    (hraw : (unionAllocRaw B).extract 0 sc.sizeBytes = allocLeBytes sc.bits sc.sizeBytes) :
    B.readScalar annealTargetDataLayout
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes sc.sizeBytes)) false =
      .ok (Miri.Memory.Scalar.fromScalarInt msc) := by
  have hn := translateSizeBytes_toNat_of_valid hrel.validBytes
  have hn16 := translateSizeBytes_le_16_of_valid hrel.validBytes
  have hn16' : sc.sizeBytes ≤ 16 := by rw [hn] at hn16; exact hn16
  have hoff : Miri.Memory.PointerProvenance.offsetIsAddr AnnealProv = true := rfl
  have hmod : sc.bits % 2 ^ (8 * sc.sizeBytes) = sc.bits := by
    rw [← u_scalarModulus_eq_two_pow]
    exact Nat.mod_eq_of_lt hrel.canonical
  have hslice := u_checkedSlice_prefix (A := B) hlen hsz hS hle
  rw [hraw] at hslice
  rw [u_readScalar_eq]
  unfold uReadScalar
  rw [hinit]
  simp only [Except.mapError, bind, Except.bind]
  rw [u_getBytesUnchecked_eq, hslice]
  simp only []
  rw [uReadTargetUInt_leBytes _ _ hn16', hmod]
  have hrange :
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes sc.sizeBytes)).size =
        translateSizeBytes sc.sizeBytes := rfl
  simp only [Bool.false_eq_true, ↓reduceIte, hoff, hrange, u_fromUInt hrel]

/-- Taking the first `w ≤ k` bytes of `allocLeBytes x k` yields
`allocLeBytes x w`. -/
theorem allocLeBytes_extract_prefix (x w k : Nat) (hle : w ≤ k) :
    (allocLeBytes x k).extract 0 w = allocLeBytes x w := by
  apply Array.ext
  · simp [allocLeBytes_size, Nat.min_eq_left hle]
  · intro i hi₁ hi₂
    rw [Array.getElem_extract]
    simp [allocLeBytes]

/-- Reading an initialized prefix `[0, w)` (`w ≤ k ≤ S`) of an allocation whose
bytes `[0, k)` hold the little-endian encoding of `sc` returns the low `w`
bytes of `sc` (`⟨sc.bits % scalarModulus w, w⟩`). -/
theorem union_readScalar_prefix_le {sc : MirAst.ScalarInt}
    {w : Nat} (hw : ValidScalarBytes w)
    {E : Type} {B : Miri.Memory.Allocation AnnealProv E} {S : Nat}
    (hlen : B.len = S) (hsz : B.byteSize = translateSizeBytes S) (hS : S ≤ 16)
    (hw_le : w ≤ sc.sizeBytes) (hk_le : sc.sizeBytes ≤ S)
    (hinit : B.initializationMask.isRangeInitialized
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes w)) = .ok (.ok ()))
    (hraw : (unionAllocRaw B).extract 0 sc.sizeBytes = allocLeBytes sc.bits sc.sizeBytes) :
    ∃ msc_w : Miri.Memory.ScalarInt,
      ScalarRel ⟨sc.bits % scalarModulus w, w⟩ msc_w ∧
      B.readScalar annealTargetDataLayout
          (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes w)) false =
        .ok (Miri.Memory.Scalar.fromScalarInt msc_w) := by
  have hmod_pos : 0 < scalarModulus w := by
    rw [u_scalarModulus_eq_two_pow]; exact Nat.two_pow_pos _
  have hcan_w : sc.bits % scalarModulus w < scalarModulus w := Nat.mod_lt _ hmod_pos
  obtain ⟨msc_w, _, hrel_w⟩ := scalarInt_tryFromUInt_of_valid (sc := ⟨sc.bits % scalarModulus w, w⟩)
    hw hcan_w
  have hw16 : w ≤ 16 := by rcases hw with rfl | rfl | rfl | rfl | rfl <;> omega
  have hoff : Miri.Memory.PointerProvenance.offsetIsAddr AnnealProv = true := rfl
  have hextr_w : (unionAllocRaw B).extract 0 w = allocLeBytes sc.bits w := by
    have h1 := congrArg (fun a => a.extract 0 w) hraw
    simp only [Array.extract_extract, Nat.zero_add, Nat.min_eq_left hw_le] at h1
    exact h1.trans (allocLeBytes_extract_prefix sc.bits w sc.sizeBytes hw_le)
  have hslice := u_checkedSlice_prefix (A := B) hlen hsz hS (Nat.le_trans hw_le hk_le)
  rw [hextr_w] at hslice
  refine ⟨msc_w, hrel_w, ?_⟩
  rw [u_readScalar_eq]
  unfold uReadScalar
  rw [hinit]
  simp only [Except.mapError, bind, Except.bind]
  rw [u_getBytesUnchecked_eq, hslice]
  simp only []
  rw [uReadTargetUInt_leBytes _ _ hw16, ← u_scalarModulus_eq_two_pow]
  have hrange :
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes w)).size =
        translateSizeBytes w := rfl
  simp only [Bool.false_eq_true, ↓reduceIte, hoff, hrange, u_fromUInt hrel_w]

/-- Reading a range that contains an uninitialized byte is rejected with
`AllocError.invalidUninitBytes`, which `annealReadImmediateLM2_2` reports as
undefined behavior. -/
theorem union_readScalar_uninit {E : Type} {B : Miri.Memory.Allocation AnnealProv E}
    {range : Miri.Memory.AllocRange} {bad : Miri.Memory.AllocRange}
    (hbad : B.initializationMask.isRangeInitialized range = .ok (.error bad)) :
    B.readScalar annealTargetDataLayout range false =
      .error (.invalidUninitBytes (some ⟨range, bad⟩)) := by
  rw [u_readScalar_eq]
  unfold uReadScalar
  rw [hbad]
  rfl

/-- Writing a related scalar at offset `0` of a mutable allocation without
provenance, whose mask `M` becomes `M'` once `[0, k)` is marked initialized,
succeeds; it keeps the allocation's size, length, alignment, mutability, extra,
and native buffer, leaves no provenance, installs `M'`, and stores the
little-endian bytes of the scalar in `[0, k)`. -/
theorem union_writeScalar_prefix {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    (hrel : ScalarRel sc msc) {E : Type} {A : Miri.Memory.Allocation AnnealProv E} {S : Nat}
    (hlen : A.len = S) (hsz : A.byteSize = translateSizeBytes S) (hS : S ≤ 16)
    (hle : sc.sizeBytes ≤ S)
    (hmut : A.mutability = .Mut) (hprov : A.provenanceMap = Miri.Memory.ProvenanceMap.new)
    {M' : Miri.Memory.InitMask}
    (hset : A.initializationMask.setRange
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes sc.sizeBytes)) true =
        .ok M') :
    ∃ A' : Miri.Memory.Allocation AnnealProv E,
      Miri.Memory.Allocation.writeScalar annealTargetDataLayout
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO msc.size)
        (Miri.Memory.Scalar.fromScalarInt msc) A = .ok () A' ∧
      A'.byteSize = A.byteSize ∧
      A'.len = S ∧
      A'.align = A.align ∧
      A'.mutability = .Mut ∧
      A'.provenanceMap = Miri.Memory.ProvenanceMap.new ∧
      A'.initializationMask = M' ∧
      A'.extra = A.extra ∧
      A'.nativeBuffer = A.nativeBuffer ∧
      (unionAllocRaw A').extract 0 sc.sizeBytes = allocLeBytes sc.bits sc.sizeBytes := by
  have hn := translateSizeBytes_toNat_of_valid hrel.validBytes
  have hn16 := translateSizeBytes_le_16_of_valid hrel.validBytes
  have hlt : Miri.ABI.Size.ZERO.bytes.toNat + (translateSizeBytes sc.sizeBytes).bytes.toNat <
      2 ^ 64 := by
    rw [hn]; simp [Miri.ABI.Size.ZERO]; omega
  have hend := allocRange_endExclusive_of_lt hlt
  have hrange :
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes sc.sizeBytes)).size =
        translateSizeBytes sc.sizeBytes := rfl
  have hconv := u_toBitsOrPtrInternal hrel
  have hslice : Miri.Memory.Allocation.getBytesUnchecked A
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes sc.sizeBytes)) =
      .ok ((unionAllocRaw A).extract 0 sc.sizeBytes) := by
    rw [u_getBytesUnchecked_eq, u_checkedSlice_prefix hlen hsz hS hle]
  unfold Miri.Memory.Allocation.getBytesUnchecked at hslice
  unfold Miri.Memory.Allocation.initializationMask at hset
  have hprov2 := hprov
  unfold Miri.Memory.Allocation.provenanceMap at hprov2
  rw [hrel.size_eq]
  unfold Miri.Memory.Allocation.writeScalar
  simp only [hmut, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hrange, hconv, pure_bind]
  rw [hslice]
  simp only [hset]
  rw [hprov2, Miri.Memory.ProvenanceMap.clear_new _ _ _ _ ?pos hend]
  case pos => decide
  simp only []
  split
  · rename_i data hdata
    have hdata' : uTargetUIntBytes annealTargetDataLayout
        (translateSizeBytes sc.sizeBytes) (BitVec.ofNat 128 sc.bits) = .ok data := hdata
    rw [uTargetUIntBytes_spec _ _ hn16] at hdata'
    cases hdata'
    have hstart : (Miri.Memory.allocRange Miri.ABI.Size.ZERO
        (translateSizeBytes sc.sizeBytes)).start.bytes.toNat = 0 := rfl
    have htoNat : (BitVec.ofNat 128 sc.bits).toNat = sc.bits :=
      bitVec_ofNat_128_toNat hrel.validBytes hrel.canonical
    have hSn : (translateSizeBytes S).bytes.toNat = S := by
      simp only [translateSizeBytes, Miri.ABI.Size.ofBytes, UInt64.toNat_ofNat']
      exact Nat.mod_eq_of_lt (by omega)
    have hlen' := hlen
    unfold Miri.Memory.Allocation.len at hlen'
    have hsz' := hsz
    unfold Miri.Memory.Allocation.byteSize at hsz'
    have hbytes_size :
        ((unionAllocRaw A).extract 0 0 ++ allocLeBytes sc.bits sc.sizeBytes ++
          (unionAllocRaw A).extract sc.sizeBytes (unionAllocRaw A).size).size = S := by
      have hr : (unionAllocRaw A).size = S := hlen
      simp only [Array.size_append, Array.size_extract, allocLeBytes_size, hr]
      omega
    have hbytes_size' :
        ((unionAllocRaw A).extract 0
            (Miri.Memory.allocRange Miri.ABI.Size.ZERO
              (translateSizeBytes sc.sizeBytes)).start.bytes.toNat ++
          allocLeBytes (BitVec.ofNat 128 sc.bits).toNat
            (translateSizeBytes sc.sizeBytes).bytes.toNat ++
          (unionAllocRaw A).extract
            ((Miri.Memory.allocRange Miri.ABI.Size.ZERO
              (translateSizeBytes sc.sizeBytes)).start.bytes.toNat +
              (translateSizeBytes sc.sizeBytes).bytes.toNat)
            (unionAllocRaw A).size).size =
          A.byteSize.bytes.toNat := by
      rw [hsz, hSn]
      simpa only [hstart, htoNat, hn, Nat.zero_add] using hbytes_size
    unfold unionAllocRaw at hbytes_size'
    unfold Miri.Memory.Allocation.byteSize at hbytes_size'
    simp only [hbytes_size', bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    refine ⟨_, rfl, rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
    · show (_ : Array UInt8).size = S
      have := hbytes_size'
      rw [hsz', hSn] at this
      exact this
    · show ((Miri.Memory.Allocation.casesOn (motive := fun _ => Array UInt8) A
          (fun raw _ _ _ _ _ _ _ => raw)).extract 0 0 ++ _ ++ _).extract 0 sc.sizeBytes = _
      simp only [hstart, htoNat, hn, Nat.zero_add]
      have hr : (unionAllocRaw A).size = S := hlen
      rw [Array.extract_append, Array.extract_append]
      simp [allocLeBytes_size]
  · rename_i err herr
    have herr' : uTargetUIntBytes annealTargetDataLayout
        (translateSizeBytes sc.sizeBytes) (BitVec.ofNat 128 sc.bits) = .error err := herr
    rw [uTargetUIntBytes_spec _ _ hn16] at herr'
    cases herr'

private def uRangeEntries {α : Type} (values : Array (Miri.ABI.Size × α))
    (start finish : Miri.ABI.Size) : Array (Miri.ABI.Size × α) :=
  values.filter fun entry => start.bytes ≤ entry.1.bytes && entry.1.bytes < finish.bytes

private def uAdjustedStart (range : Miri.Memory.AllocRange) (pointerSize : Miri.ABI.Size) :
    Except Miri.Memory.ProvenanceMapError Miri.ABI.Size :=
  if pointerSize.bytes == 0 then .error .pointerSizeZero
  else .ok (Miri.ABI.Size.ofBytes (UInt64.ofNat (range.start.bytes.toNat - (pointerSize.bytes.toNat - 1))))

private def uRangeEnd (range : Miri.Memory.AllocRange) :
    Except Miri.Memory.ProvenanceMapError Miri.ABI.Size :=
  range.endExclusive.mapError .memory

private def uRangePtrs {Prov : Type} (self : Miri.Memory.ProvenanceMap Prov)
    (range : Miri.Memory.AllocRange) (pointerSize : Miri.ABI.Size) :
    Except Miri.Memory.ProvenanceMapError (Array (Miri.ABI.Size × Prov)) := do
  let start ← uAdjustedStart range pointerSize
  let finish ← uRangeEnd range
  return uRangeEntries self.ptrs start finish

private def uRangeBytes {Prov : Type} (self : Miri.Memory.ProvenanceMap Prov)
    (range : Miri.Memory.AllocRange) :
    Except Miri.Memory.ProvenanceMapError (Array (Miri.ABI.Size × Miri.Memory.PointerFrag Prov)) := do
  let finish ← uRangeEnd range
  return uRangeEntries (self.byteFragments.getD #[]) range.start finish

private def uSubtractSize (left right : Miri.ABI.Size) :
    Except Miri.Memory.ProvenanceMapError Miri.ABI.Size :=
  (Miri.ABI.Size.sub left right).mapError (Miri.Memory.ProvenanceMapError.memory ∘ Miri.Memory.MemoryError.sizeError)

private def uPtrFragments {Prov : Type} (inRange : Miri.ABI.Size → Bool)
    (position : Miri.ABI.Size) (prov : Prov) (data : Array UInt8) (pointerSize : Miri.ABI.Size) :
    Except Miri.Memory.ProvenanceMapError (Array (Miri.ABI.Size × Miri.Memory.PointerFrag Prov)) := do
  if pointerSize.bytes > 8 then throw (.pointerSizeExceedsFragmentStorage pointerSize.bytes)
  let _finish ← (Miri.ABI.Size.add position pointerSize).mapError
    (Miri.Memory.ProvenanceMapError.memory ∘ Miri.Memory.MemoryError.sizeError)
  if h : position.bytes.toNat + pointerSize.bytes.toNat ≤ data.size then
    let bytes : Vector UInt8 8 := Vector.ofFn fun index =>
      if hi : index.val < pointerSize.bytes.toNat then
        data[position.bytes.toNat + index.val]'(by omega)
      else 0
    let mut fragments := #[]
    for index in [:pointerSize.bytes.toNat] do
      let pos := Miri.ABI.Size.ofBytes (position.bytes + UInt64.ofNat index)
      if inRange pos then
        fragments := fragments.push (pos, ⟨UInt8.ofNat index, prov, bytes⟩)
    return fragments
  else throw (.fragmentSliceOutOfBounds position pointerSize data.size)

private def uPrepareCopy {Prov : Type} (self : Miri.Memory.ProvenanceMap Prov)
    (range : Miri.Memory.AllocRange) (data : Array UInt8) (pointerSize : Miri.ABI.Size) :
    Except Miri.Memory.ProvenanceMapError (Miri.Memory.ProvenanceCopy Prov) := do
  if pointerSize.bytes == 0 then throw .pointerSizeZero
  let finish ← uRangeEnd range
  let mut ptrs := #[]
  if range.size.bytes ≥ pointerSize.bytes then
    let adjustedEnd ← uSubtractSize finish (Miri.ABI.Size.ofBytes (pointerSize.bytes - 1))
    for (offset, prov) in uRangeEntries self.ptrs range.start adjustedEnd do
      ptrs := ptrs.push (← uSubtractSize offset range.start, prov)
  let beginOverlap := (← uRangePtrs self (Miri.Memory.allocRange range.start Miri.ABI.Size.ZERO) pointerSize)[0]?
  let endOverlap := (← uRangePtrs self (Miri.Memory.allocRange finish Miri.ABI.Size.ZERO) pointerSize)[0]?
  let mut bytes := #[]
  if beginOverlap.isSome || endOverlap.isSome || self.byteFragments.isSome then
    if let some (position, prov) := beginOverlap then
      let ptrEnd ← (Miri.ABI.Size.add position pointerSize).mapError
        (Miri.Memory.ProvenanceMapError.memory ∘ Miri.Memory.MemoryError.sizeError)
      let fragmentEnd := if ptrEnd.bytes < finish.bytes then ptrEnd else finish
      if range.start.bytes < fragmentEnd.bytes then
        let fragments ← uPtrFragments
          (fun pos => range.start.bytes ≤ pos.bytes && pos.bytes < fragmentEnd.bytes)
          position prov data pointerSize
        for (pos, frag) in fragments do
          bytes := bytes.push (← uSubtractSize pos range.start, frag)
    for (offset, frag) in (← uRangeBytes self range) do
      bytes := bytes.push (← uSubtractSize offset range.start, frag)
    if let some (position, prov) := endOverlap then
      if (beginOverlap.map fun (begin, _) => begin.bytes != position.bytes).getD true then
        if position.bytes < range.start.bytes then throw .unsortedOrDuplicateKeys
        if position.bytes < finish.bytes then
          let fragments ← uPtrFragments
            (fun pos => position.bytes ≤ pos.bytes && pos.bytes < finish.bytes)
            position prov data pointerSize
          for (pos, frag) in fragments do
            let shifted ← uSubtractSize pos range.start
            if !((bytes.back?.map fun last => decide (last.1.bytes < shifted.bytes)).getD true) then
              throw .unsortedOrDuplicateKeys
            bytes := bytes.push (shifted, frag)
  return ⟨ptrs, bytes⟩

private theorem u_prepareCopy_eq {Prov : Type} :
    @Miri.Memory.ProvenanceMap.prepareCopy Prov = uPrepareCopy := rfl

private theorem uRangeEntries_new (start finish : Miri.ABI.Size) :
    uRangeEntries (Miri.Memory.ProvenanceMap.new (Prov := AnnealProv)).ptrs start finish = #[] := rfl

private theorem array_forIn_empty {α β : Type} {m : Type → Type} [Monad m]
    (b : β) (f : α → β → m (ForInStep β)) :
    forIn (#[] : Array α) b f = pure b := rfl

set_option maxHeartbeats 800000 in
private theorem provenanceMap_prepareCopy_new {S : Nat} (hS : ValidScalarBytes S)
    (data : Array UInt8) :
    (Miri.Memory.ProvenanceMap.new (Prov := AnnealProv)).prepareCopy
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S))
      data (Miri.ABI.Size.ofBytes 8) = .ok ⟨#[], #[]⟩ := by
  rw [u_prepareCopy_eq]
  unfold uPrepareCopy uRangePtrs uRangeBytes uAdjustedStart uRangeEnd uSubtractSize
  simp only [uRangeEntries_new, array_forIn_empty]
  rcases hS with rfl | rfl | rfl | rfl | rfl <;>
    simp only [bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure, Except.mapError,
      Miri.Memory.ProvenanceMap.new, Miri.Memory.allocRange, Miri.Memory.AllocRange.endExclusive,
      Miri.Memory.AllocRange.end, Miri.ABI.Size.add, Miri.ABI.Size.sub, Miri.ABI.Size.ZERO,
      Miri.ABI.Size.ofBytes, translateSizeBytes] <;>
    rfl

private def unionInitCopy (S k : Nat) : Miri.Memory.InitCopy :=
  if k = S then
    ⟨true, #[UInt64.ofNat S]⟩
  else
    ⟨true, #[UInt64.ofNat k, UInt64.ofNat (S - k)]⟩

set_option maxHeartbeats 1600000 in
private theorem isUnionPrefixMask_prepareCopy {S k : Nat} {mask : Miri.Memory.InitMask}
    (hS : ValidScalarBytes S) (hk : ValidScalarBytes k) (hle : k ≤ S)
    (h : IsUnionPrefixMask S k mask) :
    mask.prepareCopy (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S)) =
      .ok (unionInitCopy S k) := by
  rcases h with rfl | rfl <;>
    rcases hS with rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl <;>
    first | omega | with_unfolding_all rfl

private theorem unionInitCopy_noBytesInit {S k : Nat}
    (hS : ValidScalarBytes S) (hk : ValidScalarBytes k) (hle : k ≤ S) :
    (unionInitCopy S k).noBytesInit = false := by
  rcases hS with rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl <;>
    first | omega | rfl

private theorem provenanceMap_applyCopy_empty (range : Miri.Memory.AllocRange)
    (p : Miri.Memory.ProvenanceMap AnnealProv) :
    p.applyCopy ⟨#[], #[]⟩ range 1 = .ok () p := rfl

private def allocResultTuple {P E : Type}
    (r : EStateM.Result Miri.Memory.AllocError (Miri.Memory.Allocation P E) Unit) :
    Option (Array UInt8 × Miri.ABI.Size × Miri.Memory.ProvenanceMap P ×
      Miri.Memory.InitMask × Miri.ABI.Align × Miri.Memory.Mutability × E ×
      Option Miri.Memory.NativeBufferOwnership) :=
  match r with
  | .ok () a =>
    Miri.Memory.Allocation.casesOn a (fun raw sz prov mask align mutability extra nat =>
      some (raw, sz, prov, mask, align, mutability, extra, nat))
  | .error _ _ => none

private def allocExceptTuple {P E : Type}
    (r : Except Miri.Memory.AllocError (Miri.Memory.Allocation P E)) :
    Option (Array UInt8 × Miri.ABI.Size × Miri.Memory.ProvenanceMap P ×
      Miri.Memory.InitMask × Miri.ABI.Align × Miri.Memory.Mutability × E ×
      Option Miri.Memory.NativeBufferOwnership) :=
  match r with
  | .ok a =>
    Miri.Memory.Allocation.casesOn a (fun raw sz prov mask align mutability extra nat =>
      some (raw, sz, prov, mask, align, mutability, extra, nat))
  | .error _ => none

private theorem applyCopy_lazy_true {S k : Nat}
    (hS : ValidScalarBytes S) (hk : ValidScalarBytes k) (hle : k ≤ S) :
    (Miri.Memory.InitMask.mk (.Lazy true) (translateSizeBytes S)).applyCopy
      (unionInitCopy S k) (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S)) 1 =
      .ok (unionCopiedPrefixMask S k) := by
  rcases hS with rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl <;>
    first | omega | with_unfolding_all rfl

private theorem of_allocResultTuple_eq_some {E : Type}
    {r : EStateM.Result Miri.Memory.AllocError (Miri.Memory.Allocation AnnealProv E) Unit}
    {S k : Nat} (raw : Array UInt8) {align : Miri.ABI.Align} {extra : E}
    {nat : Option Miri.Memory.NativeBufferOwnership}
    (h : allocResultTuple r =
      some (raw, translateSizeBytes S, Miri.Memory.ProvenanceMap.new,
        unionCopiedPrefixMask S k, align, .Mut, extra, nat))
    (hlen : raw.size = S) :
    ∃ dest' : Miri.Memory.Allocation AnnealProv E,
      r = .ok () dest' ∧
      dest'.byteSize = translateSizeBytes S ∧
      dest'.len = S ∧
      dest'.align = align ∧
      dest'.mutability = .Mut ∧
      dest'.provenanceMap = Miri.Memory.ProvenanceMap.new ∧
      dest'.initializationMask = unionCopiedPrefixMask S k ∧
      IsUnionPrefixMask S k dest'.initializationMask ∧
      dest'.extra = extra ∧
      dest'.nativeBuffer = nat ∧
      unionAllocRaw dest' = raw := by
  cases r with
  | error _ _ => cases h
  | ok u a =>
    cases u
    induction a using Miri.Memory.Allocation.casesOn
    simp only [allocResultTuple, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨hraw, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    subst hraw
    exact ⟨_, rfl, rfl, hlen, rfl, rfl, rfl, rfl, .of_copied _ _, rfl, rfl, rfl⟩

/-- Extracting the raw byte array of an uninitialized allocation created by
`Allocation.tryNew` with `annealZeroedStorage`. -/
theorem tryNew_uninit_raw (size : Miri.ABI.Size) (align : Miri.ABI.Align)
    (allocation : Miri.Memory.Allocation AnnealProv Unit)
    (created : Miri.Memory.Allocation.tryNew size align .Uninit annealZeroedStorage = .ok allocation) :
    unionAllocRaw allocation = Array.replicate size.bytes.toNat 0 := by
  with_unfolding_all
    unfold Miri.Memory.Allocation.tryNew annealZeroedStorage at created
    dsimp only [bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure] at created
    split at created
    · cases created
    · split at created
      · cases created
      · split at created
        · cases created
        · split at created
          · injection created with h
            subst h
            rfl
          · cases created

set_option maxHeartbeats 800000 in
/-- Running the vendored `Miri.Memory.Allocation.copy`
(`copyRepeatedly ... 1 ...`) from an `S`-byte union allocation `src` (with
`IsUnionPrefixMask S k src.initializationMask` and empty provenance) into an
`S`-byte mutable destination `dest` (with
`InitMask.new (translateSizeBytes S) false` and empty provenance) succeeds and
produces an allocation `dest'` with the source's raw bytes, empty provenance,
and `dest'.initializationMask = unionCopiedPrefixMask S k` (which satisfies
`IsUnionPrefixMask S k`). -/
theorem union_copy_freshAlloc_spec {E : Type}
    {src dest : Miri.Memory.Allocation AnnealProv E} {S k : Nat}
    (hS : ValidScalarBytes S) (hk : ValidScalarBytes k) (hle : k ≤ S)
    (hlen_src : src.len = S) (hsz_src : src.byteSize = translateSizeBytes S)
    (hprov_src : src.provenanceMap = Miri.Memory.ProvenanceMap.new)
    (hmask_src : IsUnionPrefixMask S k src.initializationMask)
    (hraw_dst : unionAllocRaw dest = Array.replicate S 0)
    (hsz_dst : dest.byteSize = translateSizeBytes S)
    (hmut_dst : dest.mutability = .Mut)
    (hprov_dst : dest.provenanceMap = Miri.Memory.ProvenanceMap.new)
    (hmask_dst : dest.initializationMask = Miri.Memory.InitMask.new (translateSizeBytes S) false) :
    ∃ dest' : Miri.Memory.Allocation AnnealProv E,
      Miri.Memory.Allocation.copy src
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S))
        Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8) false true dest = .ok () dest' ∧
      dest'.byteSize = translateSizeBytes S ∧
      dest'.len = S ∧
      dest'.align = dest.align ∧
      dest'.mutability = .Mut ∧
      dest'.provenanceMap = Miri.Memory.ProvenanceMap.new ∧
      dest'.initializationMask = unionCopiedPrefixMask S k ∧
      IsUnionPrefixMask S k dest'.initializationMask ∧
      dest'.extra = dest.extra ∧
      dest'.nativeBuffer = dest.nativeBuffer ∧
      unionAllocRaw dest' = unionAllocRaw src := by
  have hS16 : S ≤ 16 := by rcases hS with rfl | rfl | rfl | rfl | rfl <;> omega
  have hSn : (translateSizeBytes S).bytes.toNat = S := by
    simp only [translateSizeBytes, Miri.ABI.Size.ofBytes, UInt64.toNat_ofNat']
    exact Nat.mod_eq_of_lt (by omega)
  have hend : (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S)).endExclusive =
      .ok (translateSizeBytes S) := by
    rcases hS with rfl | rfl | rfl | rfl | rfl <;> rfl
  have hlen_dst : dest.len = S := by
    show (unionAllocRaw dest).size = S
    rw [hraw_dst, Array.size_replicate]
  have hslice_src : Miri.Memory.Allocation.getBytesUnchecked src
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S)) =
      .ok ((unionAllocRaw src).extract 0 S) := by
    rw [u_getBytesUnchecked_eq, u_checkedSlice_prefix hlen_src hsz_src hS16 (Nat.le_refl S)]
  have hslice_dst : Miri.Memory.Allocation.getBytesUnchecked dest
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S)) =
      .ok ((unionAllocRaw dest).extract 0 S) := by
    rw [u_getBytesUnchecked_eq, u_checkedSlice_prefix hlen_dst hsz_dst hS16 (Nat.le_refl S)]
  unfold Miri.Memory.Allocation.getBytesUnchecked at hslice_src hslice_dst
  have hprep_prov := provenanceMap_prepareCopy_new hS (unionAllocRaw src)
  unfold unionAllocRaw at hprep_prov hraw_dst
  have hno_uninit := unionInitCopy_noBytesInit hS hk hle
  have hmul : (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S)).size.mul 1 =
      .ok (translateSizeBytes S) := by
    rcases hS with rfl | rfl | rfl | rfl | rfl <;> rfl
  have hloop (b : Array UInt8) :
      forIn [: (1 : UInt64).toNat] (#[] : Array UInt8) (fun _ r =>
        (pure (ForInStep.yield (r ++ b)) : Id (ForInStep (Array UInt8)))) = b := by
    simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
    rfl
  induction src using Miri.Memory.Allocation.casesOn
  rename_i srcRaw srcSz srcProv srcMask srcAlign srcMut srcExtra srcNat
  induction dest using Miri.Memory.Allocation.casesOn
  rename_i destRaw destSz destProv destMask destAlign destMut destExtra destNat
  change srcRaw.size = S at hlen_src
  change srcSz = translateSizeBytes S at hsz_src
  change srcProv = Miri.Memory.ProvenanceMap.new at hprov_src
  change IsUnionPrefixMask S k srcMask at hmask_src
  have hprep_mask := isUnionPrefixMask_prepareCopy hS hk hle hmask_src
  change destRaw = Array.replicate S 0 at hraw_dst
  change destSz = translateSizeBytes S at hsz_dst
  change destMut = .Mut at hmut_dst
  change destProv = Miri.Memory.ProvenanceMap.new at hprov_dst
  change destMask = Miri.Memory.InitMask.new (translateSizeBytes S) false at hmask_dst
  change _ = Except.ok (srcRaw.extract 0 S) at hslice_src
  change _ = Except.ok (destRaw.extract 0 S) at hslice_dst
  change (Miri.Memory.ProvenanceMap.new (Prov := AnnealProv)).prepareCopy
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S))
      srcRaw (Miri.ABI.Size.ofBytes 8) = .ok ⟨#[], #[]⟩ at hprep_prov
  subst hsz_src hprov_src hraw_dst hsz_dst hmut_dst hprov_dst hmask_dst
  have hsrc_ext : srcRaw.extract 0 S = srcRaw := by
    rw [← hlen_src]
    exact Array.extract_eq_self_of_le (Nat.le_refl _)
  rw [hsrc_ext] at hslice_src
  unfold Miri.Memory.Allocation.copy Miri.Memory.Allocation.copyRepeatedly
  simp only [hloop]
  rw [hslice_src]
  dsimp only [Id.run, bind, Bind.bind, pure, Pure.pure]
  rw [hmul]
  dsimp only [bind, Bind.bind, pure, Pure.pure]
  rw [hslice_dst]
  dsimp only [bind, Bind.bind, pure, Pure.pure]
  rw [hprep_prov]
  dsimp only [bind, Bind.bind, pure, Pure.pure]
  rw [hprep_mask]
  dsimp only [bind, Bind.bind, pure, Pure.pure]
  simp only [hno_uninit, show ((1 : UInt64) == 0) = false from rfl,
    show (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S)).size =
      translateSizeBytes S from rfl,
    provenanceMap_applyCopy_empty, Bool.not_true, Bool.false_and, Bool.and_false,
    Bool.false_eq_true, ↓reduceIte]
  clear hslice_src hslice_dst hlen_dst hsrc_ext hmul hprep_prov hprep_mask hno_uninit hmask_src
    hloop hS16
  split
  · rename_i u updated₁ hprep_ovw
    have hu1 : allocResultTuple (.ok () updated₁) =
        some (Array.replicate S 0, translateSizeBytes S, Miri.Memory.ProvenanceMap.new,
          ⟨.Lazy true, translateSizeBytes S⟩, destAlign, .Mut, destExtra, destNat) := by
      rw [← hprep_ovw]
      clear hprep_ovw hlen_src hk hle hend hSn
      rcases hS with rfl | rfl | rfl | rfl | rfl <;> with_unfolding_all rfl
    clear hprep_ovw
    split
    · rename_i u2 updated₂ hovw
      have hu2 : allocExceptTuple (.ok updated₂) =
          some (srcRaw, translateSizeBytes S, Miri.Memory.ProvenanceMap.new,
            ⟨.Lazy true, translateSizeBytes S⟩, destAlign, .Mut, destExtra, destNat) := by
        have hovw2 : ∃ (k : Miri.ABI.Size → Except Miri.Memory.AllocError (Miri.Memory.Allocation AnnealProv E)),
            (∀ finish, allocExceptTuple (k finish) =
              some ((unionAllocRaw updated₁).extract 0 (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S)).start.bytes.toNat ++ srcRaw ++ (unionAllocRaw updated₁).extract finish.bytes.toNat (unionAllocRaw updated₁).size,
                updated₁.byteSize, updated₁.provenanceMap, updated₁.initializationMask, updated₁.align, updated₁.mutability, updated₁.extra, updated₁.nativeBuffer)) ∧
            Except.ok updated₂ =
              (((Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S)).endExclusive |>.mapError Miri.Memory.AllocError.memory) >>= fun finish =>
                if (((unionAllocRaw updated₁).extract 0 (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S)).start.bytes.toNat ++ srcRaw ++ (unionAllocRaw updated₁).extract finish.bytes.toNat (unionAllocRaw updated₁).size).size != updated₁.byteSize.bytes.toNat) = true then
                  throw (Miri.Memory.AllocError.storageLengthMismatch updated₁.byteSize ((unionAllocRaw updated₁).extract 0 (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S)).start.bytes.toNat ++ srcRaw ++ (unionAllocRaw updated₁).extract finish.bytes.toNat (unionAllocRaw updated₁).size).size)
                else k finish) := by
          refine ⟨_, ?_, by rw [← hovw]; with_unfolding_all rfl⟩
          intro finish
          with_unfolding_all rfl
        rcases hovw2 with ⟨k_fn, hk_fn, hovw2⟩
        rw [hend] at hovw2
        rw [show (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S)).start.bytes.toNat = 0 from rfl] at hovw2 hk_fn
        dsimp only [Except.mapError, bind, Bind.bind, Except.bind] at hovw2
        rw [hSn] at hovw2
        induction updated₁ using Miri.Memory.Allocation.casesOn
        simp only [allocResultTuple, Option.some.injEq, Prod.mk.injEq] at hu1
        rcases hu1 with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        unfold unionAllocRaw Miri.Memory.Allocation.byteSize at hovw2
        unfold unionAllocRaw Miri.Memory.Allocation.byteSize
          Miri.Memory.Allocation.provenanceMap Miri.Memory.Allocation.initializationMask
          Miri.Memory.Allocation.align Miri.Memory.Allocation.mutability
          Miri.Memory.Allocation.extra Miri.Memory.Allocation.nativeBuffer at hk_fn
        dsimp only at hovw2 hk_fn
        have hupd : (Array.replicate S (0 : UInt8)).extract 0 0 ++ srcRaw ++
            (Array.replicate S (0 : UInt8)).extract S (Array.replicate S (0 : UInt8)).size = srcRaw := by
          simp [Array.size_replicate]
        rw [hupd, hSn, hlen_src, bne_self_eq_false] at hovw2
        simp only [Bool.false_eq_true, ↓reduceIte] at hovw2
        rw [hovw2]
        have hk_spec := hk_fn (translateSizeBytes S)
        rw [hSn, hupd] at hk_spec
        exact hk_spec
      clear hovw hu1 hend hSn
      have hmask_u2 : updated₂.initializationMask = ⟨.Lazy true, translateSizeBytes S⟩ := by
        induction updated₂ using Miri.Memory.Allocation.casesOn
        simp only [allocExceptTuple, Option.some.injEq, Prod.mk.injEq] at hu2
        rcases hu2 with ⟨_, _, _, rfl, _, _, _, _⟩
        rfl
      have hap := applyCopy_lazy_true hS hk hle
      rw [← hmask_u2] at hap
      unfold Miri.Memory.Allocation.initializationMask at hap
      rw [hap]
      apply of_allocResultTuple_eq_some srcRaw ?_ hlen_src
      clear hap hmask_u2 hlen_src hk hle hS
      induction updated₂ using Miri.Memory.Allocation.casesOn
      simp only [allocExceptTuple, Option.some.injEq, Prod.mk.injEq] at hu2
      rcases hu2 with ⟨hraw, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rw [hraw]
      rfl
    · rename_i u2 reason hovw
      have hovw2 : ∃ (k : Miri.ABI.Size → Except Miri.Memory.AllocError (Miri.Memory.Allocation AnnealProv E)),
          (∀ finish, allocExceptTuple (k finish) =
            some ((unionAllocRaw updated₁).extract 0 (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S)).start.bytes.toNat ++ srcRaw ++ (unionAllocRaw updated₁).extract finish.bytes.toNat (unionAllocRaw updated₁).size,
              updated₁.byteSize, updated₁.provenanceMap, updated₁.initializationMask, updated₁.align, updated₁.mutability, updated₁.extra, updated₁.nativeBuffer)) ∧
          Except.error reason =
            (((Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S)).endExclusive |>.mapError Miri.Memory.AllocError.memory) >>= fun finish =>
              if (((unionAllocRaw updated₁).extract 0 (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S)).start.bytes.toNat ++ srcRaw ++ (unionAllocRaw updated₁).extract finish.bytes.toNat (unionAllocRaw updated₁).size).size != updated₁.byteSize.bytes.toNat) = true then
                throw (Miri.Memory.AllocError.storageLengthMismatch updated₁.byteSize ((unionAllocRaw updated₁).extract 0 (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S)).start.bytes.toNat ++ srcRaw ++ (unionAllocRaw updated₁).extract finish.bytes.toNat (unionAllocRaw updated₁).size).size)
              else k finish) := by
        refine ⟨_, ?_, by rw [← hovw]; with_unfolding_all rfl⟩
        intro finish
        with_unfolding_all rfl
      rcases hovw2 with ⟨k_fn, hk_fn, hovw2⟩
      rw [hend] at hovw2
      rw [show (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S)).start.bytes.toNat = 0 from rfl] at hovw2 hk_fn
      dsimp only [Except.mapError, bind, Bind.bind, Except.bind] at hovw2
      rw [hSn] at hovw2
      induction updated₁ using Miri.Memory.Allocation.casesOn
      simp only [allocResultTuple, Option.some.injEq, Prod.mk.injEq] at hu1
      rcases hu1 with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      unfold unionAllocRaw Miri.Memory.Allocation.byteSize at hovw2
      unfold unionAllocRaw Miri.Memory.Allocation.byteSize
        Miri.Memory.Allocation.provenanceMap Miri.Memory.Allocation.initializationMask
        Miri.Memory.Allocation.align Miri.Memory.Allocation.mutability
        Miri.Memory.Allocation.extra Miri.Memory.Allocation.nativeBuffer at hk_fn
      dsimp only at hovw2 hk_fn
      have hupd : (Array.replicate S (0 : UInt8)).extract 0 0 ++ srcRaw ++
          (Array.replicate S (0 : UInt8)).extract S (Array.replicate S (0 : UInt8)).size = srcRaw := by
        simp [Array.size_replicate]
      rw [hupd, hSn, hlen_src, bne_self_eq_false] at hovw2
      simp only [Bool.false_eq_true, ↓reduceIte] at hovw2
      have hk_spec := hk_fn (translateSizeBytes S)
      rw [← hovw2] at hk_spec
      cases hk_spec
  · rename_i reason updated₁ hprep_ovw
    clear hlen_src hk hle hend hSn
    rcases hS with rfl | rfl | rfl | rfl | rfl <;> with_unfolding_all cases hprep_ovw

/-- `getBytesUnchecked` on any in-bounds `[off, off + sz)` slice of a
well-sized allocation returns the corresponding slice of `unionAllocRaw`. -/
theorem getBytesUnchecked_at {P E : Type}
    {A : Miri.Memory.Allocation P E} (off sz : Miri.ABI.Size)
    (hlen : A.len = A.byteSize.bytes.toNat)
    (hin : off.bytes.toNat + sz.bytes.toNat ≤ A.byteSize.bytes.toNat) :
    Miri.Memory.Allocation.getBytesUnchecked A (Miri.Memory.allocRange off sz) =
      .ok ((unionAllocRaw A).extract off.bytes.toNat (off.bytes.toNat + sz.bytes.toNat)) := by
  have hbs : A.byteSize.bytes.toNat < 2 ^ 64 := UInt64.toNat_lt _
  have hlt : off.bytes.toNat + sz.bytes.toNat < 2 ^ 64 := Nat.lt_of_le_of_lt hin hbs
  have hend := allocRange_endExclusive_of_lt hlt
  have hraw : (unionAllocRaw A).size = A.byteSize.bytes.toNat := hlen
  have hfin : (Miri.ABI.Size.ofBytes (off.bytes + sz.bytes)).bytes.toNat =
      off.bytes.toNat + sz.bytes.toNat := by
    simp only [Miri.ABI.Size.ofBytes, UInt64.toNat_add]
    exact Nat.mod_eq_of_lt hlt
  have hle1 : ¬ (Miri.Memory.allocRange off sz).start.bytes >
      (Miri.ABI.Size.ofBytes (off.bytes + sz.bytes)).bytes := by
    rw [GT.gt, UInt64.lt_iff_toNat_lt, hfin]
    dsimp [Miri.Memory.allocRange]
    omega
  have hle2 : ¬ (Miri.ABI.Size.ofBytes (off.bytes + sz.bytes)).bytes > A.byteSize.bytes := by
    rw [GT.gt, UInt64.lt_iff_toNat_lt, hfin]
    omega
  rw [u_getBytesUnchecked_eq]
  unfold uCheckedSlice
  rw [hend]
  simp only [hraw, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, Except.mapError, bind,
    Except.bind, hle1, hle2, Bool.or_self, pure, Except.pure, decide_false, hfin]
  rfl

/-- Canonicalizing a zero-byte mutable allocation via `Allocation.fromBytes #[]`
succeeds for any valid alignment (`pow2 ≤ 29`) and yields an empty allocation
satisfying `ArraySliceRel elemKind 0`. -/
theorem zero_array_fromBytes_spec (elemKind : RigidTy) (layouts : LayoutTable)
    {align : Miri.ABI.Align} (hal : align.pow2 ≤ 29)
    (extra : Option Miri.TreeBorrows.BorrowTree) :
    ∃ zeroAlloc : Miri.Memory.Allocation AnnealProv Unit,
      Miri.Memory.Allocation.fromBytes #[] align .Mut = .ok zeroAlloc ∧
      let dest' := zeroAlloc.withExtra extra
      dest'.byteSize = Miri.ABI.Size.ZERO ∧
      dest'.len = 0 ∧
      dest'.align = align ∧
      dest'.mutability = .Mut ∧
      dest'.provenanceMap = Miri.Memory.ProvenanceMap.new ∧
      dest'.initializationMask = Miri.Memory.InitMask.new Miri.ABI.Size.ZERO true ∧
      dest'.extra = extra ∧
      dest'.nativeBuffer = none ∧
      ArraySliceRel elemKind 0 layouts [] Miri.ABI.Size.ZERO dest' := by
  obtain ⟨a, hfb, _, _, _, _, _, _, hextra⟩ :=
    fromBytes_replicate_zero_spec Miri.ABI.Size.ZERO align hal
  obtain ⟨hsz, hlen, hal', hmut, hprov, hmask⟩ := hextra extra
  have hfb' : Miri.Memory.Allocation.fromBytes #[] align .Mut = .ok a := hfb
  have hnat : (a.withExtra extra).nativeBuffer = none := by
    with_unfolding_all
      unfold Miri.Memory.Allocation.fromBytes at hfb'
      dsimp only [bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure] at hfb'
      split at hfb'
      · cases hfb'
      · split at hfb'
        · cases hfb'
        · split at hfb'
          · injection hfb' with h; subst h; rfl
          · cases hfb'
  refine ⟨a, hfb', hsz, hlen, hal', hmut, hprov, hmask, rfl, hnat, ?_⟩
  exact ⟨rfl, by rw [hlen, hsz], hmut, hprov, by rw [hmask, hsz],
    by rw [hsz]; simp [Miri.ABI.Size.ZERO], fun _ _ h => nomatch h⟩

private theorem provenanceMap_prepareCopy_new_at (off sz : Miri.ABI.Size)
    (hlt : off.bytes.toNat + sz.bytes.toNat < 2 ^ 64) (data : Array UInt8) :
    (Miri.Memory.ProvenanceMap.new (Prov := AnnealProv)).prepareCopy
      (Miri.Memory.allocRange off sz) data (Miri.ABI.Size.ofBytes 8) = .ok ⟨#[], #[]⟩ := by
  have hend := allocRange_endExclusive_of_lt hlt
  have hfin : (Miri.ABI.Size.ofBytes (off.bytes + sz.bytes)).bytes.toNat =
      off.bytes.toNat + sz.bytes.toNat := by
    simp only [Miri.ABI.Size.ofBytes, UInt64.toNat_add]
    exact Nat.mod_eq_of_lt hlt
  have hend0_s := allocRange_endExclusive_of_lt (off := off) (sz := Miri.ABI.Size.ZERO)
    (by simp [Miri.ABI.Size.ZERO]; exact UInt64.toNat_lt _)
  have hend0_f := allocRange_endExclusive_of_lt
    (off := Miri.ABI.Size.ofBytes (off.bytes + sz.bytes)) (sz := Miri.ABI.Size.ZERO)
    (by simp [Miri.ABI.Size.ZERO]; exact UInt64.toNat_lt _)
  rw [u_prepareCopy_eq]
  unfold uPrepareCopy uRangePtrs uRangeBytes uAdjustedStart uRangeEnd uSubtractSize
  have hpz : ((Miri.ABI.Size.ofBytes 8).bytes == 0) = false := rfl
  have hstart_eq : (Miri.Memory.allocRange off sz).start = off := rfl
  simp only [hpz, Bool.false_eq_true, ↓reduceIte, hstart_eq, hend, hend0_s, hend0_f,
    Except.mapError, bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure,
    uRangeEntries_new, array_forIn_empty]
  by_cases hge : (Miri.Memory.allocRange off sz).size.bytes ≥ (Miri.ABI.Size.ofBytes 8).bytes
  · have hsub_ok : ¬ (Miri.ABI.Size.ofBytes (off.bytes + sz.bytes)).bytes <
        (Miri.ABI.Size.ofBytes ((Miri.ABI.Size.ofBytes 8).bytes - 1)).bytes := by
      rw [UInt64.lt_iff_toNat_lt, hfin]
      have hge' : 8 ≤ sz.bytes.toNat := by
        simpa [GE.ge, UInt64.le_iff_toNat_le, Miri.Memory.allocRange, Miri.ABI.Size.ofBytes] using hge
      have h7 : (Miri.ABI.Size.ofBytes ((Miri.ABI.Size.ofBytes 8).bytes - 1)).bytes.toNat = 7 := rfl
      omega
    simp only [hge, ↓reduceIte, Miri.ABI.Size.sub, hsub_ok]
    rfl
  · simp only [hge, ↓reduceIte]
    rfl

private theorem initMask_new_true_prepareCopy {srcSz srcOff totalSz : Miri.ABI.Size}
    (hpos : 0 < totalSz.bytes.toNat)
    (hin : srcOff.bytes.toNat + totalSz.bytes.toNat ≤ srcSz.bytes.toNat) :
    (Miri.Memory.InitMask.new srcSz true).prepareCopy (Miri.Memory.allocRange srcOff totalSz) =
      .ok ⟨true, #[totalSz.bytes]⟩ := by
  have hbs : srcSz.bytes.toNat < 2 ^ 64 := UInt64.toNat_lt _
  have hlt : srcOff.bytes.toNat + totalSz.bytes.toNat < 2 ^ 64 := Nat.lt_of_le_of_lt hin hbs
  have hend := allocRange_endExclusive_of_lt hlt
  let finish := Miri.ABI.Size.ofBytes (srcOff.bytes + totalSz.bytes)
  have hfin : finish.bytes.toNat = srcOff.bytes.toNat + totalSz.bytes.toNat := by
    simp only [finish, Miri.ABI.Size.ofBytes, UInt64.toNat_add]
    exact Nat.mod_eq_of_lt hlt
  have hnz : ((Miri.Memory.allocRange srcOff totalSz).size.bytes == 0) = false := by
    cases h : ((Miri.Memory.allocRange srcOff totalSz).size.bytes == 0) with
    | false => rfl
    | true =>
      have := eq_of_beq h
      dsimp [Miri.Memory.allocRange] at this
      rw [this] at hpos
      simp at hpos
  have hnot_gt_len : ¬ finish.bytes > srcSz.bytes := by
    rw [GT.gt, UInt64.lt_iff_toNat_lt, hfin]; omega
  have hlt_fin : srcOff.bytes < finish.bytes := by
    rw [UInt64.lt_iff_toNat_lt, hfin]; omega
  have hnot_gt_sf : ¬ srcOff.bytes > finish.bytes := by
    rw [GT.gt, UInt64.lt_iff_toNat_lt, hfin]; omega
  have hnot_ge_sf : ¬ finish.bytes ≤ srcOff.bytes := by
    rw [UInt64.le_iff_toNat_le, hfin]; omega
  have hfuel : finish.bytes.toNat - srcOff.bytes.toNat + 1 =
      (totalSz.bytes.toNat - 1) + 1 + 1 := by
    omega
  have hfromEnd : Miri.Memory.AllocRange.fromEndpoints srcOff finish =
      .ok (Miri.Memory.allocRange srcOff totalSz) := by
    unfold Miri.Memory.AllocRange.fromEndpoints Miri.ABI.Size.sub
    have hsub : finish.bytes - srcOff.bytes = totalSz.bytes := by
      dsimp [finish, Miri.ABI.Size.ofBytes]
      exact uint64_add_sub_cancel_left srcOff.bytes totalSz.bytes
    have hnot_lt : ¬ finish.bytes < srcOff.bytes := by
      rw [UInt64.lt_iff_toNat_lt, hfin]; omega
    simp [hnot_lt, Except.mapError, bind, Except.bind, pure, Except.pure, hsub,
      Miri.Memory.allocRange]
    cases totalSz; rfl
  let iter0 : Miri.Memory.InitChunkIter := ⟨Miri.Memory.InitMask.new srcSz true, true, srcOff, finish⟩
  let iter1 : Miri.Memory.InitChunkIter := ⟨Miri.Memory.InitMask.new srcSz true, false, finish, finish⟩
  have hrange : (Miri.Memory.InitMask.new srcSz true).rangeAsInitChunks
      (Miri.Memory.allocRange srcOff totalSz) = .ok iter0 := by
    unfold Miri.Memory.InitMask.rangeAsInitChunks
    rw [hend]
    dsimp only [Miri.Memory.InitMask.new, Miri.Memory.allocRange,
      bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure]
    simp only [show ¬ (Miri.ABI.Size.ofBytes (srcOff.bytes + totalSz.bytes)).bytes > srcSz.bytes
        from hnot_gt_len,
      ↓reduceIte,
      show srcOff.bytes < (Miri.ABI.Size.ofBytes (srcOff.bytes + totalSz.bytes)).bytes
        from hlt_fin,
      show (Miri.Memory.InitMask.mk (.Lazy true) srcSz).get srcOff = .ok true from rfl]
    rfl
  have hnext0 : iter0.next? = .ok (some (.Init srcOff finish, iter1)) := by
    have hnot_ge_nat : ¬ srcOff.bytes.toNat ≥ finish.bytes.toNat := by omega
    with_unfolding_all
      unfold Miri.Memory.InitChunkIter.next?
      dsimp only [iter0, iter1, Miri.Memory.InitMask.new,
        bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure]
      change (if decide (srcOff.bytes > finish.bytes) || decide (finish.bytes > srcSz.bytes) then _
        else if srcOff.bytes.toNat ≥ finish.bytes.toNat then _ else _) = _
      simp [hnot_gt_sf, hnot_gt_len, hnot_ge_nat, hnot_ge_sf]
  have hnext1 : iter1.next? = .ok none := by
    have hnot_gt_ff : ¬ finish.bytes > finish.bytes := by
      rw [GT.gt, UInt64.lt_iff_toNat_lt]; omega
    with_unfolding_all
      unfold Miri.Memory.InitChunkIter.next?
      dsimp only [iter1, Miri.Memory.InitMask.new,
        bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure]
      change (if decide (finish.bytes > finish.bytes) || decide (finish.bytes > srcSz.bytes) then _
        else if finish.bytes.toNat ≥ finish.bytes.toNat then _ else _) = _
      simp [hnot_gt_ff, hnot_gt_len]
  have hchunks : Miri.Memory.InitMask.collectChunks iter0 = .ok #[.Init srcOff finish] := by
    have haux : ∃ aux : Miri.Memory.InitChunkIter → Nat →
        Except Miri.Memory.InitMaskError (Array Miri.Memory.InitChunk),
        (∀ it, Miri.Memory.InitMask.collectChunks it =
          aux it (it.finish.bytes.toNat - it.start.bytes.toNat + 1)) ∧
        (∀ it n, aux it (n + 1) = (do
          match ← it.next? with
          | none => return #[]
          | some (chunk, next) => return #[chunk] ++ (← aux next n))) := by
      refine ⟨fun it k => WellFounded.Nat.fix
          (α := (_ : Miri.Memory.InitChunkIter) ×' Nat)
          (motive := fun _ => Except Miri.Memory.InitMaskError (Array Miri.Memory.InitChunk))
          (fun x => PSigma.casesOn x fun _ fuel => fuel) _ ⟨it, k⟩,
        fun _ => by with_unfolding_all rfl,
        fun it n => ?_⟩
      dsimp only
      rw [WellFounded.Nat.fix_eq]
      with_unfolding_all rfl
    rcases haux with ⟨aux, hcol, hstep⟩
    rw [hcol]
    dsimp only [iter0]
    rw [hfuel, hstep]
    rw [hnext0]
    dsimp only [bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure]
    rw [hstep, hnext1]
    rfl
  unfold Miri.Memory.InitMask.prepareCopy
  rw [hnz]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [hrange]
  dsimp only [bind, Bind.bind, Except.bind]
  rw [hchunks]
  simp [Miri.Memory.InitChunk.range, hfromEnd, Miri.Memory.InitChunk.isInit,
    Miri.Memory.allocRange, bind, Except.bind, pure, Except.pure]

private theorem initMask_applyCopy_full (totalSz : Miri.ABI.Size)
    (hpos : 0 < totalSz.bytes.toNat) :
    (Miri.Memory.InitMask.mk (.Lazy true) totalSz).applyCopy
      ⟨true, #[totalSz.bytes]⟩ (Miri.Memory.allocRange Miri.ABI.Size.ZERO totalSz) 1 =
      .ok (Miri.Memory.InitMask.new totalSz true) := by
  have hnz : (totalSz.bytes == 0) = false := by
    cases h : (totalSz.bytes == 0) with
    | false => rfl
    | true =>
      have := eq_of_beq h
      rw [this] at hpos
      simp at hpos
  have hmul : (Miri.Memory.allocRange Miri.ABI.Size.ZERO totalSz).size.mul 1 = .ok totalSz := by
    simp [Miri.ABI.Size.mul, Miri.Memory.allocRange, Miri.ABI.Size.ofBytes]
  have hend : (Miri.Memory.allocRange Miri.ABI.Size.ZERO totalSz).endExclusive = .ok totalSz := by
    have hlt0 : Miri.ABI.Size.ZERO.bytes.toNat + totalSz.bytes.toNat < 2 ^ 64 := by
      simp [Miri.ABI.Size.ZERO]
      exact UInt64.toNat_lt totalSz.bytes
    have h := allocRange_endExclusive_of_lt (off := Miri.ABI.Size.ZERO) (sz := totalSz) hlt0
    simpa [Miri.ABI.Size.ZERO, Miri.ABI.Size.ofBytes] using h
  have hset := Miri.Memory.InitMask.full_overwrite_stays_lazy totalSz totalSz true true
    (Miri.Memory.allocRange Miri.ABI.Size.ZERO totalSz) hend rfl (UInt64.le_refl _)
  unfold Miri.Memory.InitMask.applyCopy
  have hany : (#[totalSz.bytes].isEmpty || #[totalSz.bytes].any (· == 0)) = false := by
    simp [hnz]
  have hsize1 : #[totalSz.bytes].size ≤ 1 := Nat.le_refl 1
  simp only [hany, Bool.false_eq_true, ↓reduceIte, hsize1, hmul, Except.mapError,
    bind, Bind.bind, Except.bind]
  exact hset

set_option maxHeartbeats 800000 in
/-- Running vendored `Miri.Memory.Allocation.copy` (`copyRepeatedly ... 1 ...`)
from a non-empty `ArraySliceRel` subslice at `srcOff` into a fresh
`totalSz`-byte mutable stack allocation (`InitMask.new totalSz false`, empty
provenance) succeeds and produces `dest'` with `InitMask.new totalSz true`,
empty provenance, and
`ArraySliceRel elemKind cnt layouts elems Size.ZERO dest'`. -/
theorem array_copy_freshAlloc_spec
    {elemKind : RigidTy} {cnt : Nat} {layouts : LayoutTable} {elems : List Value}
    {srcOff : Miri.ABI.Size}
    {src dest : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    (hslice : ArraySliceRel elemKind cnt layouts elems srcOff src)
    (hpos : 0 < cnt)
    (helem_pos : 0 < (translateTy { kind := elemKind, layoutIdx := 0 } layouts).layout.size.bytes.toNat)
    (hraw_dst : unionAllocRaw dest =
      Array.replicate
        (cnt * (translateTy { kind := elemKind, layoutIdx := 0 } layouts).layout.size.bytes.toNat) 0)
    (hsz_dst : dest.byteSize =
      Miri.ABI.Size.ofBytes
        (UInt64.ofNat
          (cnt * (translateTy { kind := elemKind, layoutIdx := 0 } layouts).layout.size.bytes.toNat)))
    (hmut_dst : dest.mutability = .Mut)
    (hprov_dst : dest.provenanceMap = Miri.Memory.ProvenanceMap.new)
    (hmask_dst : dest.initializationMask = Miri.Memory.InitMask.new dest.byteSize false) :
    let totalBytes :=
      cnt * (translateTy { kind := elemKind, layoutIdx := 0 } layouts).layout.size.bytes.toNat
    let totalSz := Miri.ABI.Size.ofBytes (UInt64.ofNat totalBytes)
    ∃ dest' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree),
      Miri.Memory.Allocation.copy src (Miri.Memory.allocRange srcOff totalSz)
        Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8) false true dest = .ok () dest' ∧
      dest'.byteSize = totalSz ∧
      dest'.len = totalBytes ∧
      dest'.align = dest.align ∧
      dest'.mutability = .Mut ∧
      dest'.provenanceMap = Miri.Memory.ProvenanceMap.new ∧
      dest'.initializationMask = Miri.Memory.InitMask.new totalSz true ∧
      dest'.extra = dest.extra ∧
      dest'.nativeBuffer = dest.nativeBuffer ∧
      ArraySliceRel elemKind cnt layouts elems Miri.ABI.Size.ZERO dest' := by
  intro totalBytes totalSz
  have htot_pos : 0 < totalBytes := Nat.mul_pos hpos helem_pos
  have hbs_src : src.byteSize.bytes.toNat < 2 ^ 64 := UInt64.toNat_lt _
  have hin_src_nat : srcOff.bytes.toNat + totalBytes ≤ src.byteSize.bytes.toNat :=
    hslice.slice_in_bounds
  have htot_lt64 : totalBytes < 2 ^ 64 := by omega
  have htot_toNat : totalSz.bytes.toNat = totalBytes := by
    simp only [totalSz, Miri.ABI.Size.ofBytes, UInt64.toNat_ofNat']
    exact Nat.mod_eq_of_lt htot_lt64
  have hpos_sz : 0 < totalSz.bytes.toNat := by rw [htot_toNat]; exact htot_pos
  have hin_src : srcOff.bytes.toNat + totalSz.bytes.toNat ≤ src.byteSize.bytes.toNat := by
    rw [htot_toNat]; exact hin_src_nat
  have hlt_src : srcOff.bytes.toNat + totalSz.bytes.toNat < 2 ^ 64 := by omega
  have hsz_dst_eq : dest.byteSize = totalSz := hsz_dst
  have hlen_dst : dest.len = dest.byteSize.bytes.toNat := by
    show (unionAllocRaw dest).size = _
    rw [hraw_dst, hsz_dst_eq, Array.size_replicate, htot_toNat]
  have hin_dst : Miri.ABI.Size.ZERO.bytes.toNat + totalSz.bytes.toNat ≤ dest.byteSize.bytes.toNat := by
    rw [hsz_dst_eq]; simp [Miri.ABI.Size.ZERO]
  have hslice_src := getBytesUnchecked_at (A := src) srcOff totalSz hslice.alloc_len hin_src
  have hslice_dst := getBytesUnchecked_at (A := dest) Miri.ABI.Size.ZERO totalSz hlen_dst hin_dst
  unfold Miri.Memory.Allocation.getBytesUnchecked at hslice_src hslice_dst
  have hprep_prov := provenanceMap_prepareCopy_new_at srcOff totalSz hlt_src (unionAllocRaw src)
  have hprep_mask := initMask_new_true_prepareCopy (srcSz := src.byteSize) hpos_sz hin_src
  have hmul : (Miri.Memory.allocRange srcOff totalSz).size.mul 1 = .ok totalSz := by
    simp [Miri.ABI.Size.mul, Miri.Memory.allocRange, Miri.ABI.Size.ofBytes]
  have hend_dst : (Miri.Memory.allocRange Miri.ABI.Size.ZERO totalSz).endExclusive = .ok totalSz := by
    have hlt0 : Miri.ABI.Size.ZERO.bytes.toNat + totalSz.bytes.toNat < 2 ^ 64 := by
      simp [Miri.ABI.Size.ZERO]
      exact UInt64.toNat_lt totalSz.bytes
    have h := allocRange_endExclusive_of_lt (off := Miri.ABI.Size.ZERO) (sz := totalSz) hlt0
    simpa [Miri.ABI.Size.ZERO, Miri.ABI.Size.ofBytes] using h
  have hloop (b : Array UInt8) :
      forIn [: (1 : UInt64).toNat] (#[] : Array UInt8) (fun _ r =>
        (pure (ForInStep.yield (r ++ b)) : Id (ForInStep (Array UInt8)))) = b := by
    simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
    rfl
  have hnz_sz : ((Miri.Memory.allocRange Miri.ABI.Size.ZERO totalSz).size.bytes == 0) = false := by
    cases h : ((Miri.Memory.allocRange Miri.ABI.Size.ZERO totalSz).size.bytes == 0) with
    | false => rfl
    | true =>
      have := eq_of_beq h
      dsimp [Miri.Memory.allocRange] at this
      rw [this] at hpos_sz
      simp at hpos_sz
  let copiedRaw := (unionAllocRaw src).extract srcOff.bytes.toNat
    (srcOff.bytes.toNat + totalSz.bytes.toNat)
  have hcopied_len : copiedRaw.size = totalBytes := by
    have hraw_src : (unionAllocRaw src).size = src.byteSize.bytes.toNat := hslice.alloc_len
    simp [copiedRaw, Array.size_extract, hraw_src, htot_toNat]
    omega
  -- Run `Allocation.copy` (`copyRepeatedly ... 1 ...`) on `src` and `dest`:
  have hcopy_res : ∃ dest' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree),
      Miri.Memory.Allocation.copy src (Miri.Memory.allocRange srcOff totalSz)
        Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8) false true dest = .ok () dest' ∧
      dest'.byteSize = totalSz ∧
      dest'.len = totalBytes ∧
      dest'.align = dest.align ∧
      dest'.mutability = .Mut ∧
      dest'.provenanceMap = Miri.Memory.ProvenanceMap.new ∧
      dest'.initializationMask = Miri.Memory.InitMask.new totalSz true ∧
      dest'.extra = dest.extra ∧
      dest'.nativeBuffer = dest.nativeBuffer ∧
      unionAllocRaw dest' = copiedRaw := by
    have hprov_src := hslice.alloc_prov
    have hmask_src := hslice.alloc_mask
    have hmask_dst' : dest.initializationMask = Miri.Memory.InitMask.new totalSz false := by
      rw [← hsz_dst_eq]; exact hmask_dst
    induction src using Miri.Memory.Allocation.casesOn
    rename_i srcRaw srcSz srcProv srcMask srcAlign srcMut srcExtra srcNat
    induction dest using Miri.Memory.Allocation.casesOn
    rename_i destRaw destSz destProv destMask destAlign destMut destExtra destNat
    change srcProv = Miri.Memory.ProvenanceMap.new at hprov_src
    change srcMask = Miri.Memory.InitMask.new srcSz true at hmask_src
    change destRaw = Array.replicate totalBytes 0 at hraw_dst
    change destSz = totalSz at hsz_dst
    change destMut = .Mut at hmut_dst
    change destProv = Miri.Memory.ProvenanceMap.new at hprov_dst
    change destMask = Miri.Memory.InitMask.new totalSz false at hmask_dst'
    change _ = Except.ok copiedRaw at hslice_src
    change _ = Except.ok (destRaw.extract 0 (0 + totalSz.bytes.toNat)) at hslice_dst
    change (Miri.Memory.ProvenanceMap.new (Prov := AnnealProv)).prepareCopy
        (Miri.Memory.allocRange srcOff totalSz) srcRaw (Miri.ABI.Size.ofBytes 8) = .ok ⟨#[], #[]⟩ at hprep_prov
    change (Miri.Memory.InitMask.new srcSz true).prepareCopy
        (Miri.Memory.allocRange srcOff totalSz) = .ok ⟨true, #[totalSz.bytes]⟩ at hprep_mask
    subst hprov_src hmask_src hraw_dst hsz_dst hmut_dst hprov_dst hmask_dst'
    unfold Miri.Memory.Allocation.copy Miri.Memory.Allocation.copyRepeatedly
    simp only [hloop]
    rw [hslice_src]
    dsimp only [Id.run, bind, Bind.bind, pure, Pure.pure]
    rw [hmul]
    dsimp only [bind, Bind.bind, pure, Pure.pure]
    rw [hslice_dst]
    dsimp only [bind, Bind.bind, pure, Pure.pure]
    rw [hprep_prov]
    dsimp only [bind, Bind.bind, pure, Pure.pure]
    rw [hprep_mask]
    dsimp only [bind, Bind.bind, pure, Pure.pure]
    have hno_init : (Miri.Memory.InitCopy.mk true #[totalSz.bytes]).noBytesInit = false := rfl
    simp only [hno_init, show ((1 : UInt64) == 0) = false from rfl,
      show (Miri.Memory.allocRange srcOff totalSz).size = totalSz from rfl,
      provenanceMap_applyCopy_empty, Bool.not_true, Bool.false_and, Bool.and_false,
      Bool.false_eq_true, ↓reduceIte]
    have hset_dst : (Miri.Memory.InitMask.new totalSz false).setRange
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO totalSz) true =
        .ok ⟨.Lazy true, totalSz⟩ :=
      Miri.Memory.InitMask.full_overwrite_stays_lazy totalSz totalSz false true
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO totalSz) hend_dst rfl (UInt64.le_refl _)
    have hclr_dst := Miri.Memory.ProvenanceMap.clear_new (P := AnnealProv)
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO totalSz) (Array.replicate totalBytes 0)
      (Miri.ABI.Size.ofBytes 8) totalSz (by decide) hend_dst
    split
    · rename_i _ updated₁ hprep_ovw
      have hu1 : allocResultTuple (.ok () updated₁) =
          some (Array.replicate totalBytes 0, totalSz, Miri.Memory.ProvenanceMap.new,
            ⟨.Lazy true, totalSz⟩, destAlign, .Mut, destExtra, destNat) := by
        have hpo := hprep_ovw
        with_unfolding_all
          conv at hpo => lhs; whnf
          rw [hslice_dst] at hpo
          dsimp only [Id.run, bind, Bind.bind, pure, Pure.pure] at hpo
          simp only [hnz_sz, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false] at hpo
          conv at hpo => lhs; arg 2; whnf
          simp only [hset_dst, Except.mapError] at hpo
          dsimp only [bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure] at hpo
          rw [hclr_dst] at hpo
          cases hpo
          rfl
      split
      · rename_i _ updated₂ hovw
        have hu2 : allocExceptTuple (.ok updated₂) =
            some (copiedRaw, totalSz, Miri.Memory.ProvenanceMap.new,
              ⟨.Lazy true, totalSz⟩, destAlign, .Mut, destExtra, destNat) := by
          have hovw2 : ∃ (k_fn : Miri.ABI.Size → Except Miri.Memory.AllocError
              (Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree))),
              (∀ finish, allocExceptTuple (k_fn finish) =
                some ((unionAllocRaw updated₁).extract 0 0 ++ copiedRaw ++
                  (unionAllocRaw updated₁).extract finish.bytes.toNat (unionAllocRaw updated₁).size,
                  updated₁.byteSize, updated₁.provenanceMap, updated₁.initializationMask,
                  updated₁.align, updated₁.mutability, updated₁.extra, updated₁.nativeBuffer)) ∧
              Except.ok updated₂ =
                (((Miri.Memory.allocRange Miri.ABI.Size.ZERO totalSz).endExclusive |>.mapError
                  Miri.Memory.AllocError.memory) >>= fun finish =>
                  if (((unionAllocRaw updated₁).extract 0 0 ++ copiedRaw ++
                      (unionAllocRaw updated₁).extract finish.bytes.toNat (unionAllocRaw updated₁).size).size !=
                      updated₁.byteSize.bytes.toNat) = true then
                    throw (Miri.Memory.AllocError.storageLengthMismatch updated₁.byteSize
                      ((unionAllocRaw updated₁).extract 0 0 ++ copiedRaw ++
                        (unionAllocRaw updated₁).extract finish.bytes.toNat (unionAllocRaw updated₁).size).size)
                  else k_fn finish) := by
            refine ⟨_, ?_, by rw [← hovw]; with_unfolding_all rfl⟩
            intro finish
            with_unfolding_all rfl
          rcases hovw2 with ⟨k_fn, hk_fn, hovw2⟩
          rw [hend_dst] at hovw2
          dsimp only [Except.mapError, bind, Bind.bind, Except.bind] at hovw2
          induction updated₁ using Miri.Memory.Allocation.casesOn
          simp only [allocResultTuple, Option.some.injEq, Prod.mk.injEq] at hu1
          rcases hu1 with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
          unfold unionAllocRaw Miri.Memory.Allocation.byteSize at hovw2
          unfold unionAllocRaw Miri.Memory.Allocation.byteSize
            Miri.Memory.Allocation.provenanceMap Miri.Memory.Allocation.initializationMask
            Miri.Memory.Allocation.align Miri.Memory.Allocation.mutability
            Miri.Memory.Allocation.extra Miri.Memory.Allocation.nativeBuffer at hk_fn
          dsimp only at hovw2 hk_fn
          have hupd : (Array.replicate totalBytes (0 : UInt8)).extract 0 0 ++ copiedRaw ++
              (Array.replicate totalBytes (0 : UInt8)).extract totalSz.bytes.toNat
                (Array.replicate totalBytes (0 : UInt8)).size = copiedRaw := by
            rw [htot_toNat]
            simp [Array.size_replicate]
          rw [hupd, hcopied_len, htot_toNat, bne_self_eq_false] at hovw2
          simp only [Bool.false_eq_true, ↓reduceIte] at hovw2
          rw [hovw2]
          have hk_spec := hk_fn totalSz
          rw [hupd] at hk_spec
          exact hk_spec
        have hmask_u2 : updated₂.initializationMask = ⟨.Lazy true, totalSz⟩ := by
          induction updated₂ using Miri.Memory.Allocation.casesOn
          simp only [allocExceptTuple, Option.some.injEq, Prod.mk.injEq] at hu2
          rcases hu2 with ⟨_, _, _, rfl, _, _, _, _⟩
          rfl
        have hap := initMask_applyCopy_full totalSz hpos_sz
        rw [← hmask_u2] at hap
        unfold Miri.Memory.Allocation.initializationMask at hap
        rw [hap]
        dsimp only [bind, Bind.bind, pure, Pure.pure]
        induction updated₂ using Miri.Memory.Allocation.casesOn
        simp only [allocExceptTuple, Option.some.injEq, Prod.mk.injEq] at hu2
        rcases hu2 with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        exact ⟨_, rfl, rfl, hcopied_len, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · rename_i _ reason hovw
        have hovw2 : ∃ (k_fn : Miri.ABI.Size → Except Miri.Memory.AllocError
            (Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree))),
            (∀ finish, allocExceptTuple (k_fn finish) =
              some ((unionAllocRaw updated₁).extract 0 0 ++ copiedRaw ++
                (unionAllocRaw updated₁).extract finish.bytes.toNat (unionAllocRaw updated₁).size,
                updated₁.byteSize, updated₁.provenanceMap, updated₁.initializationMask,
                updated₁.align, updated₁.mutability, updated₁.extra, updated₁.nativeBuffer)) ∧
            Except.error reason =
              (((Miri.Memory.allocRange Miri.ABI.Size.ZERO totalSz).endExclusive |>.mapError
                Miri.Memory.AllocError.memory) >>= fun finish =>
                if (((unionAllocRaw updated₁).extract 0 0 ++ copiedRaw ++
                    (unionAllocRaw updated₁).extract finish.bytes.toNat (unionAllocRaw updated₁).size).size !=
                    updated₁.byteSize.bytes.toNat) = true then
                  throw (Miri.Memory.AllocError.storageLengthMismatch updated₁.byteSize
                    ((unionAllocRaw updated₁).extract 0 0 ++ copiedRaw ++
                      (unionAllocRaw updated₁).extract finish.bytes.toNat (unionAllocRaw updated₁).size).size)
                else k_fn finish) := by
          refine ⟨_, ?_, by rw [← hovw]; with_unfolding_all rfl⟩
          intro finish
          with_unfolding_all rfl
        rcases hovw2 with ⟨k_fn, hk_fn, hovw2⟩
        rw [hend_dst] at hovw2
        dsimp only [Except.mapError, bind, Bind.bind, Except.bind] at hovw2
        induction updated₁ using Miri.Memory.Allocation.casesOn
        simp only [allocResultTuple, Option.some.injEq, Prod.mk.injEq] at hu1
        rcases hu1 with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        unfold unionAllocRaw Miri.Memory.Allocation.byteSize at hovw2
        unfold unionAllocRaw Miri.Memory.Allocation.byteSize
          Miri.Memory.Allocation.provenanceMap Miri.Memory.Allocation.initializationMask
          Miri.Memory.Allocation.align Miri.Memory.Allocation.mutability
          Miri.Memory.Allocation.extra Miri.Memory.Allocation.nativeBuffer at hk_fn
        dsimp only at hovw2 hk_fn
        have hupd : (Array.replicate totalBytes (0 : UInt8)).extract 0 0 ++ copiedRaw ++
            (Array.replicate totalBytes (0 : UInt8)).extract totalSz.bytes.toNat
              (Array.replicate totalBytes (0 : UInt8)).size = copiedRaw := by
          rw [htot_toNat]
          simp [Array.size_replicate]
        rw [hupd, hcopied_len, htot_toNat, bne_self_eq_false] at hovw2
        simp only [Bool.false_eq_true, ↓reduceIte] at hovw2
        have hk_spec := hk_fn totalSz
        rw [← hovw2] at hk_spec
        cases hk_spec
    · rename_i _ _ hprep_ovw
      have hpo := hprep_ovw
      with_unfolding_all
        conv at hpo => lhs; whnf
        rw [hslice_dst] at hpo
        dsimp only [Id.run, bind, Bind.bind, pure, Pure.pure] at hpo
        simp only [hnz_sz, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false] at hpo
        conv at hpo => lhs; arg 2; whnf
        simp only [hset_dst, Except.mapError] at hpo
        dsimp only [bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure] at hpo
        rw [hclr_dst] at hpo
        cases hpo
  obtain ⟨dest', hcopy, hsz', hlen', hal', hmut', hprov', hmask', hex', hnat', hraw'⟩ := hcopy_res
  refine ⟨dest', hcopy, hsz', hlen', hal', hmut', hprov', hmask', hex', hnat', ?_⟩
  refine
    { elems_len := hslice.elems_len
      alloc_len := by rw [hlen', hsz', htot_toNat]
      alloc_mut := hmut'
      alloc_prov := hprov'
      alloc_mask := by rw [hmask', hsz']
      slice_in_bounds := by
        rw [hsz', htot_toNat]; simp [Miri.ABI.Size.ZERO]; exact Nat.le_refl totalBytes
      elem_rel := ?_ }
  intro k elemVal hget
  have hk_lt : k < cnt := by
    rw [← hslice.elems_len]
    exact (List.getElem?_eq_some_iff.mp (by rwa [← get?_eq_getElem?])).1
  obtain ⟨sc, msc, hv, hesz, hbool, hchar, hrel, hread_src⟩ := hslice.elem_rel k elemVal hget
  refine ⟨sc, msc, hv, hesz, hbool, hchar, hrel, ?_⟩
  let elemLay := (translateTy { kind := elemKind, layoutIdx := 0 } layouts).layout
  let es := elemLay.size.bytes.toNat
  have hk1_le : (k + 1) * es ≤ totalBytes := Nat.mul_le_mul_right _ (by omega)
  have hmul_add : (k + 1) * es = k * es + es := Nat.add_mul k 1 es |>.trans (by simp)
  have hkes_le : k * es + es ≤ totalBytes := by rw [← hmul_add]; exact hk1_le
  let dstElemOff := Miri.ABI.Size.ofBytes (Miri.ABI.Size.ZERO.bytes + UInt64.ofNat (k * es))
  let srcElemOff := Miri.ABI.Size.ofBytes (srcOff.bytes + UInt64.ofNat (k * es))
  have hdstOff_nat : dstElemOff.bytes.toNat = k * es := by
    simp only [dstElemOff, Miri.ABI.Size.ofBytes, Miri.ABI.Size.ZERO, UInt64.zero_add,
      UInt64.toNat_ofNat']
    exact Nat.mod_eq_of_lt (by omega)
  have hsrcOff_nat : srcElemOff.bytes.toNat = srcOff.bytes.toNat + k * es := by
    have h1 : k * es < 2 ^ 64 := by omega
    have h2 : srcOff.bytes.toNat + k * es < 2 ^ 64 := by omega
    simp only [srcElemOff, Miri.ABI.Size.ofBytes, UInt64.toNat_add, UInt64.toNat_ofNat',
      Nat.mod_eq_of_lt h1]
    exact Nat.mod_eq_of_lt h2
  have hin_elem_dst : dstElemOff.bytes.toNat + es ≤ dest'.byteSize.bytes.toNat := by
    rw [hdstOff_nat, hsz', htot_toNat]; exact hkes_le
  have hin_elem_src : srcElemOff.bytes.toNat + es ≤ src.byteSize.bytes.toNat := by
    rw [hsrcOff_nat]; omega
  have hend_elem_dst := allocRange_endExclusive_of_lt
    (off := dstElemOff) (sz := elemLay.size)
    (by change dstElemOff.bytes.toNat + es < 2 ^ 64; omega)
  have hend_elem_src := allocRange_endExclusive_of_lt
    (off := srcElemOff) (sz := elemLay.size)
    (by change srcElemOff.bytes.toNat + es < 2 ^ 64; omega)
  have hinit_dst : dest'.initializationMask.isRangeInitialized
      (Miri.Memory.allocRange dstElemOff elemLay.size) = .ok (.ok ()) := by
    rw [hmask']
    apply Miri.Memory.InitMask.lazy_initialized_query _ _ _ hend_elem_dst
    rw [UInt64.le_iff_toNat_le]
    have hfin_d : (Miri.ABI.Size.ofBytes (dstElemOff.bytes + elemLay.size.bytes)).bytes.toNat =
        dstElemOff.bytes.toNat + es := by
      simp only [Miri.ABI.Size.ofBytes, UInt64.toNat_add]
      exact Nat.mod_eq_of_lt (by change dstElemOff.bytes.toNat + es < 2 ^ 64; omega)
    rw [hfin_d, htot_toNat, hdstOff_nat]
    exact hkes_le
  have hinit_src : src.initializationMask.isRangeInitialized
      (Miri.Memory.allocRange srcElemOff elemLay.size) = .ok (.ok ()) := by
    rw [hslice.alloc_mask]
    apply Miri.Memory.InitMask.lazy_initialized_query _ _ _ hend_elem_src
    rw [UInt64.le_iff_toNat_le]
    have hfin_s : (Miri.ABI.Size.ofBytes (srcElemOff.bytes + elemLay.size.bytes)).bytes.toNat =
        srcElemOff.bytes.toNat + es := by
      simp only [Miri.ABI.Size.ofBytes, UInt64.toNat_add]
      exact Nat.mod_eq_of_lt (by change srcElemOff.bytes.toNat + es < 2 ^ 64; omega)
    rw [hfin_s]
    exact hin_elem_src
  have hbytes_dst := getBytesUnchecked_at (A := dest') dstElemOff elemLay.size
    (by rw [hlen', hsz', htot_toNat]) hin_elem_dst
  have hbytes_src := getBytesUnchecked_at (A := src) srcElemOff elemLay.size
    hslice.alloc_len hin_elem_src
  have hextr_eq : (unionAllocRaw dest').extract dstElemOff.bytes.toNat
      (dstElemOff.bytes.toNat + es) =
      (unionAllocRaw src).extract srcElemOff.bytes.toNat (srcElemOff.bytes.toNat + es) := by
    rw [hraw']
    dsimp only [copiedRaw]
    rw [Array.extract_extract, hdstOff_nat, hsrcOff_nat, htot_toNat]
    congr 1
    omega
  -- Since both `readScalar` calls see `.ok (.ok ())` mask, identical byte
  -- slices, and `offsetIsAddr AnnealProv = true`, their results are equal!
  change dest'.readScalar annealTargetDataLayout
      (Miri.Memory.allocRange dstElemOff elemLay.size) false = _
  change src.readScalar annealTargetDataLayout
      (Miri.Memory.allocRange srcElemOff elemLay.size) false = _ at hread_src
  rw [u_readScalar_eq] at hread_src ⊢
  unfold uReadScalar at hread_src ⊢
  rw [hinit_dst, hbytes_dst]
  rw [hinit_src, hbytes_src] at hread_src
  dsimp only [es] at hextr_eq
  rw [hextr_eq]
  exact hread_src

/-- Overwriting `[0, finish)` on any `InitMask` with `len.bytes ≤ finish.bytes`
takes `InitMask.setRange`'s `fullOverwrite` fast path in both `.Lazy` and
`.Materialized` representations, returning `⟨.Lazy newState, finish⟩`. -/
theorem initMask_setRange_full_overwrite (mask : Miri.Memory.InitMask)
    (range : Miri.Memory.AllocRange) (finish : Miri.ABI.Size) (newState : Bool)
    (hend : range.endExclusive = .ok finish)
    (hstart : range.start.bytes = 0)
    (hlen : mask.len.bytes ≤ finish.bytes) :
    mask.setRange range newState = .ok ⟨.Lazy newState, finish⟩ := by
  cases mask with
  | mk blocks len =>
    cases blocks <;>
      simp [Miri.Memory.InitMask.setRange, hend, hstart, hlen,
        Pure.pure, Except.pure, Bind.bind, Except.bind]

/-- Every `IsUnionPrefixMask S k` has `len = translateSizeBytes S`. -/
theorem IsUnionPrefixMask.len_eq {S k : Nat} {M : Miri.Memory.InitMask}
    (hM : IsUnionPrefixMask S k M) : M.len = translateSizeBytes S := by
  rcases hM with rfl | rfl
  · unfold unionPrefixMask
    split <;> rfl
  · unfold unionCopiedPrefixMask
    split <;> rfl

/-- Writing `[0, k')` (`k' ≤ k ≤ S`) onto `IsUnionPrefixMask S k M` leaves the
initialized prefix `[0, k)` intact (`IsUnionPrefixMask S k M'`). -/
theorem IsUnionPrefixMask.setRange_le {S k k' : Nat} {M : Miri.Memory.InitMask}
    (hM : IsUnionPrefixMask S k M) (hS : ValidScalarBytes S)
    (hk : ValidScalarBytes k) (hk' : ValidScalarBytes k') (hk'k : k' ≤ k) (hkS : k ≤ S) :
    ∃ M', M.setRange
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes k')) true = .ok M' ∧
      IsUnionPrefixMask S k M' := by
  rcases hM with rfl | rfl
  · refine ⟨unionPrefixMask S k, ?_, .of_fresh S k⟩
    rcases hS with rfl | rfl | rfl | rfl | rfl <;> rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk' with rfl | rfl | rfl | rfl | rfl <;>
      first | omega | with_unfolding_all decide
  · refine ⟨unionCopiedPrefixMask S k, ?_, .of_copied S k⟩
    rcases hS with rfl | rfl | rfl | rfl | rfl <;> rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk' with rfl | rfl | rfl | rfl | rfl <;>
      first | omega | with_unfolding_all decide

/-- Writing `[0, k')` onto `IsUnionPrefixMask S k M` yields a mask initializing
`[0, max k k')` (`IsUnionPrefixMask S (max k k') M'`). -/
theorem IsUnionPrefixMask.setRange_max {S k k' : Nat} {M : Miri.Memory.InitMask}
    (hM : IsUnionPrefixMask S k M) (hS : ValidScalarBytes S)
    (hk : ValidScalarBytes k) (hk' : ValidScalarBytes k') (hkS : k ≤ S) (hk'S : k' ≤ S) :
    ∃ M', M.setRange
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes k')) true = .ok M' ∧
      IsUnionPrefixMask S (max k k') M' := by
  rcases Nat.le_total k k' with hle | hge
  · rw [Nat.max_eq_right hle]
    exact hM.setRange_ge hS hk hk' hle hk'S
  · rw [Nat.max_eq_left hge]
    exact hM.setRange_le hS hk hk' hge hkS

/-- Writing a `k`-byte scalar at offset `0` of an `S`-byte allocation (`k ≤ S`)
stores `allocLeBytes sc.bits k` in `[0, k)` AND preserves the trailing raw bytes
`[k, S)` unchanged. -/
theorem union_writeScalar_prefix_preserve_high
    {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    (hrel : ScalarRel sc msc) {E : Type} {A : Miri.Memory.Allocation AnnealProv E} {S : Nat}
    (hlen : A.len = S) (hsz : A.byteSize = translateSizeBytes S) (hS : S ≤ 16)
    (hle : sc.sizeBytes ≤ S)
    (hmut : A.mutability = .Mut) (hprov : A.provenanceMap = Miri.Memory.ProvenanceMap.new)
    {M' : Miri.Memory.InitMask}
    (hset : A.initializationMask.setRange
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes sc.sizeBytes)) true =
        .ok M') :
    ∃ A' : Miri.Memory.Allocation AnnealProv E,
      Miri.Memory.Allocation.writeScalar annealTargetDataLayout
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO msc.size)
        (Miri.Memory.Scalar.fromScalarInt msc) A = .ok () A' ∧
      A'.byteSize = A.byteSize ∧
      A'.len = S ∧
      A'.align = A.align ∧
      A'.mutability = .Mut ∧
      A'.provenanceMap = Miri.Memory.ProvenanceMap.new ∧
      A'.initializationMask = M' ∧
      A'.extra = A.extra ∧
      A'.nativeBuffer = A.nativeBuffer ∧
      (unionAllocRaw A').extract 0 sc.sizeBytes = allocLeBytes sc.bits sc.sizeBytes ∧
      (unionAllocRaw A').extract sc.sizeBytes S = (unionAllocRaw A).extract sc.sizeBytes S := by
  have hn := translateSizeBytes_toNat_of_valid hrel.validBytes
  have hn16 := translateSizeBytes_le_16_of_valid hrel.validBytes
  have hlt : Miri.ABI.Size.ZERO.bytes.toNat + (translateSizeBytes sc.sizeBytes).bytes.toNat <
      2 ^ 64 := by
    rw [hn]; simp [Miri.ABI.Size.ZERO]; omega
  have hend := allocRange_endExclusive_of_lt hlt
  have hrange :
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes sc.sizeBytes)).size =
        translateSizeBytes sc.sizeBytes := rfl
  have hconv := u_toBitsOrPtrInternal hrel
  have hslice : Miri.Memory.Allocation.getBytesUnchecked A
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes sc.sizeBytes)) =
      .ok ((unionAllocRaw A).extract 0 sc.sizeBytes) := by
    rw [u_getBytesUnchecked_eq, u_checkedSlice_prefix hlen hsz hS hle]
  unfold Miri.Memory.Allocation.getBytesUnchecked at hslice
  unfold Miri.Memory.Allocation.initializationMask at hset
  have hprov2 := hprov
  unfold Miri.Memory.Allocation.provenanceMap at hprov2
  rw [hrel.size_eq]
  unfold Miri.Memory.Allocation.writeScalar
  simp only [hmut, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hrange, hconv, pure_bind]
  rw [hslice]
  simp only [hset]
  rw [hprov2, Miri.Memory.ProvenanceMap.clear_new _ _ _ _ ?pos hend]
  case pos => decide
  simp only []
  split
  · rename_i data hdata
    have hdata' : uTargetUIntBytes annealTargetDataLayout
        (translateSizeBytes sc.sizeBytes) (BitVec.ofNat 128 sc.bits) = .ok data := hdata
    rw [uTargetUIntBytes_spec _ _ hn16] at hdata'
    cases hdata'
    have hstart : (Miri.Memory.allocRange Miri.ABI.Size.ZERO
        (translateSizeBytes sc.sizeBytes)).start.bytes.toNat = 0 := rfl
    have htoNat : (BitVec.ofNat 128 sc.bits).toNat = sc.bits :=
      bitVec_ofNat_128_toNat hrel.validBytes hrel.canonical
    have hSn : (translateSizeBytes S).bytes.toNat = S := by
      simp only [translateSizeBytes, Miri.ABI.Size.ofBytes, UInt64.toNat_ofNat']
      exact Nat.mod_eq_of_lt (by omega)
    have hlen' := hlen
    unfold Miri.Memory.Allocation.len at hlen'
    have hsz' := hsz
    unfold Miri.Memory.Allocation.byteSize at hsz'
    have hbytes_size :
        ((unionAllocRaw A).extract 0 0 ++ allocLeBytes sc.bits sc.sizeBytes ++
          (unionAllocRaw A).extract sc.sizeBytes (unionAllocRaw A).size).size = S := by
      have hr : (unionAllocRaw A).size = S := hlen
      simp only [Array.size_append, Array.size_extract, allocLeBytes_size, hr]
      omega
    have hbytes_size' :
        ((unionAllocRaw A).extract 0
            (Miri.Memory.allocRange Miri.ABI.Size.ZERO
              (translateSizeBytes sc.sizeBytes)).start.bytes.toNat ++
          allocLeBytes (BitVec.ofNat 128 sc.bits).toNat
            (translateSizeBytes sc.sizeBytes).bytes.toNat ++
          (unionAllocRaw A).extract
            ((Miri.Memory.allocRange Miri.ABI.Size.ZERO
              (translateSizeBytes sc.sizeBytes)).start.bytes.toNat +
              (translateSizeBytes sc.sizeBytes).bytes.toNat)
            (unionAllocRaw A).size).size =
          A.byteSize.bytes.toNat := by
      rw [hsz, hSn]
      simpa only [hstart, htoNat, hn, Nat.zero_add] using hbytes_size
    unfold unionAllocRaw at hbytes_size'
    unfold Miri.Memory.Allocation.byteSize at hbytes_size'
    simp only [hbytes_size', bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    refine ⟨_, rfl, rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
    · show (_ : Array UInt8).size = S
      have := hbytes_size'
      rw [hsz', hSn] at this
      exact this
    · show ((Miri.Memory.Allocation.casesOn (motive := fun _ => Array UInt8) A
          (fun raw _ _ _ _ _ _ _ => raw)).extract 0 0 ++ _ ++ _).extract 0 sc.sizeBytes = _
      simp only [hstart, htoNat, hn, Nat.zero_add]
      rw [Array.extract_append, Array.extract_append]
      simp [allocLeBytes_size]
    · show ((unionAllocRaw A).extract 0 _ ++ _ ++
          (unionAllocRaw A).extract _ (unionAllocRaw A).size).extract sc.sizeBytes S = _
      simp only [hstart, htoNat, hn, Nat.zero_add]
      have hr : (unionAllocRaw A).size = S := hlen
      rw [hr, Array.extract_empty_of_stop_le_start (Nat.le_refl 0), Array.empty_append,
        Array.extract_append, Array.extract_eq_empty_of_le (by simp [allocLeBytes_size]; omega),
        Array.empty_append]
      simp only [allocLeBytes_size, Nat.sub_self, Array.extract_extract, Nat.add_zero,
        Nat.min_eq_right (by omega : S ≤ sc.sizeBytes + (S - sc.sizeBytes))]
  · rename_i err herr
    have herr' : uTargetUIntBytes annealTargetDataLayout
        (translateSizeBytes sc.sizeBytes) (BitVec.ofNat 128 sc.bits) = .error err := herr
    rw [uTargetUIntBytes_spec _ _ hn16] at herr'
    cases herr'

set_option maxHeartbeats 800000 in
/-- Running `Miri.Memory.Allocation.copy` (`copyRepeatedly ... 1 ...`) from an
`S`-byte union allocation `src` (`IsUnionPrefixMask S k`) into **any** distinct
mutable `S`-byte destination allocation `dest` (regardless of `dest`'s prior raw
bytes or initialization mask, so long as `dest.initializationMask.len =
translateSizeBytes S`) overwrites `dest` completely with `src`'s raw bytes and
`unionCopiedPrefixMask S k` (`IsUnionPrefixMask S k`). -/
theorem union_copy_alloc_spec {E : Type}
    {src dest : Miri.Memory.Allocation AnnealProv E} {S k : Nat}
    (hS : ValidScalarBytes S) (hk : ValidScalarBytes k) (hle : k ≤ S)
    (hlen_src : src.len = S) (hsz_src : src.byteSize = translateSizeBytes S)
    (hprov_src : src.provenanceMap = Miri.Memory.ProvenanceMap.new)
    (hmask_src : IsUnionPrefixMask S k src.initializationMask)
    (hlen_dst : dest.len = S)
    (hsz_dst : dest.byteSize = translateSizeBytes S)
    (hmut_dst : dest.mutability = .Mut)
    (hprov_dst : dest.provenanceMap = Miri.Memory.ProvenanceMap.new)
    (hmask_dst : dest.initializationMask.len = translateSizeBytes S) :
    ∃ dest' : Miri.Memory.Allocation AnnealProv E,
      Miri.Memory.Allocation.copy src
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S))
        Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8) false true dest = .ok () dest' ∧
      dest'.byteSize = translateSizeBytes S ∧
      dest'.len = S ∧
      dest'.align = dest.align ∧
      dest'.mutability = .Mut ∧
      dest'.provenanceMap = Miri.Memory.ProvenanceMap.new ∧
      dest'.initializationMask = unionCopiedPrefixMask S k ∧
      IsUnionPrefixMask S k dest'.initializationMask ∧
      dest'.extra = dest.extra ∧
      dest'.nativeBuffer = dest.nativeBuffer ∧
      unionAllocRaw dest' = unionAllocRaw src := by
  have hS16 : S ≤ 16 := by rcases hS with rfl | rfl | rfl | rfl | rfl <;> omega
  have hSn : (translateSizeBytes S).bytes.toNat = S := by
    simp only [translateSizeBytes, Miri.ABI.Size.ofBytes, UInt64.toNat_ofNat']
    exact Nat.mod_eq_of_lt (by omega)
  have hend : (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S)).endExclusive =
      .ok (translateSizeBytes S) := by
    rcases hS with rfl | rfl | rfl | rfl | rfl <;> rfl
  have hnz_sz : ((Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S)).size.bytes ==
      0) = false := by
    rcases hS with rfl | rfl | rfl | rfl | rfl <;> rfl
  have hslice_src : Miri.Memory.Allocation.getBytesUnchecked src
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S)) =
      .ok ((unionAllocRaw src).extract 0 S) := by
    rw [u_getBytesUnchecked_eq, u_checkedSlice_prefix hlen_src hsz_src hS16 (Nat.le_refl S)]
  have hslice_dst : Miri.Memory.Allocation.getBytesUnchecked dest
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S)) =
      .ok ((unionAllocRaw dest).extract 0 S) := by
    rw [u_getBytesUnchecked_eq, u_checkedSlice_prefix hlen_dst hsz_dst hS16 (Nat.le_refl S)]
  unfold Miri.Memory.Allocation.getBytesUnchecked at hslice_src hslice_dst
  have hprep_prov := provenanceMap_prepareCopy_new hS (unionAllocRaw src)
  unfold unionAllocRaw at hprep_prov
  have hno_uninit := unionInitCopy_noBytesInit hS hk hle
  have hmul : (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S)).size.mul 1 =
      .ok (translateSizeBytes S) := by
    rcases hS with rfl | rfl | rfl | rfl | rfl <;> rfl
  have hloop (b : Array UInt8) :
      forIn [: (1 : UInt64).toNat] (#[] : Array UInt8) (fun _ r =>
        (pure (ForInStep.yield (r ++ b)) : Id (ForInStep (Array UInt8)))) = b := by
    simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
    rfl
  induction src using Miri.Memory.Allocation.casesOn
  rename_i srcRaw srcSz srcProv srcMask srcAlign srcMut srcExtra srcNat
  induction dest using Miri.Memory.Allocation.casesOn
  rename_i destRaw destSz destProv destMask destAlign destMut destExtra destNat
  change srcRaw.size = S at hlen_src
  change srcSz = translateSizeBytes S at hsz_src
  change srcProv = Miri.Memory.ProvenanceMap.new at hprov_src
  change IsUnionPrefixMask S k srcMask at hmask_src
  have hprep_mask := isUnionPrefixMask_prepareCopy hS hk hle hmask_src
  change destRaw.size = S at hlen_dst
  change destSz = translateSizeBytes S at hsz_dst
  change destMut = .Mut at hmut_dst
  change destProv = Miri.Memory.ProvenanceMap.new at hprov_dst
  change destMask.len = translateSizeBytes S at hmask_dst
  change _ = Except.ok (srcRaw.extract 0 S) at hslice_src
  change _ = Except.ok (destRaw.extract 0 S) at hslice_dst
  change (Miri.Memory.ProvenanceMap.new (Prov := AnnealProv)).prepareCopy
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S))
      srcRaw (Miri.ABI.Size.ofBytes 8) = .ok ⟨#[], #[]⟩ at hprep_prov
  subst hsz_src hprov_src hsz_dst hmut_dst hprov_dst
  have hsrc_ext : srcRaw.extract 0 S = srcRaw := by
    rw [← hlen_src]
    exact Array.extract_eq_self_of_le (Nat.le_refl _)
  rw [hsrc_ext] at hslice_src
  have hset_dst : destMask.setRange
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S)) true =
      .ok ⟨.Lazy true, translateSizeBytes S⟩ :=
    initMask_setRange_full_overwrite destMask
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S))
      (translateSizeBytes S) true hend rfl (by rw [hmask_dst]; exact UInt64.le_refl _)
  have hclr_dst := Miri.Memory.ProvenanceMap.clear_new (P := AnnealProv)
    (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S)) destRaw
    (Miri.ABI.Size.ofBytes 8) (translateSizeBytes S) (by decide) hend
  unfold Miri.Memory.Allocation.copy Miri.Memory.Allocation.copyRepeatedly
  simp only [hloop]
  rw [hslice_src]
  dsimp only [Id.run, bind, Bind.bind, pure, Pure.pure]
  rw [hmul]
  dsimp only [bind, Bind.bind, pure, Pure.pure]
  rw [hslice_dst]
  dsimp only [bind, Bind.bind, pure, Pure.pure]
  rw [hprep_prov]
  dsimp only [bind, Bind.bind, pure, Pure.pure]
  rw [hprep_mask]
  dsimp only [bind, Bind.bind, pure, Pure.pure]
  simp only [hno_uninit, show ((1 : UInt64) == 0) = false from rfl,
    show (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S)).size =
      translateSizeBytes S from rfl,
    provenanceMap_applyCopy_empty, Bool.not_true, Bool.false_and, Bool.and_false,
    Bool.false_eq_true, ↓reduceIte]
  split
  · rename_i _ updated₁ hprep_ovw
    have hu1 : allocResultTuple (.ok () updated₁) =
        some (destRaw, translateSizeBytes S, Miri.Memory.ProvenanceMap.new,
          ⟨.Lazy true, translateSizeBytes S⟩, destAlign, .Mut, destExtra, destNat) := by
      have hpo := hprep_ovw
      with_unfolding_all
        conv at hpo => lhs; whnf
        rw [hslice_dst] at hpo
        dsimp only [Id.run, bind, Bind.bind, pure, Pure.pure] at hpo
        simp only [hnz_sz, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false] at hpo
        conv at hpo => lhs; arg 2; whnf
        simp only [hset_dst, Except.mapError] at hpo
        dsimp only [bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure] at hpo
        rw [hclr_dst] at hpo
        cases hpo
        rfl
    split
    · rename_i _ updated₂ hovw
      have hu2 : allocExceptTuple (.ok updated₂) =
          some (srcRaw, translateSizeBytes S, Miri.Memory.ProvenanceMap.new,
            ⟨.Lazy true, translateSizeBytes S⟩, destAlign, .Mut, destExtra, destNat) := by
        have hovw2 : ∃ (k_fn : Miri.ABI.Size → Except Miri.Memory.AllocError
            (Miri.Memory.Allocation AnnealProv E)),
            (∀ finish, allocExceptTuple (k_fn finish) =
              some ((unionAllocRaw updated₁).extract 0 0 ++ srcRaw ++
                (unionAllocRaw updated₁).extract finish.bytes.toNat (unionAllocRaw updated₁).size,
                updated₁.byteSize, updated₁.provenanceMap, updated₁.initializationMask,
                updated₁.align, updated₁.mutability, updated₁.extra, updated₁.nativeBuffer)) ∧
            Except.ok updated₂ =
              (((Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S)).endExclusive |>.mapError
                Miri.Memory.AllocError.memory) >>= fun finish =>
                if (((unionAllocRaw updated₁).extract 0 0 ++ srcRaw ++
                    (unionAllocRaw updated₁).extract finish.bytes.toNat (unionAllocRaw updated₁).size).size !=
                    updated₁.byteSize.bytes.toNat) = true then
                  throw (Miri.Memory.AllocError.storageLengthMismatch updated₁.byteSize
                    ((unionAllocRaw updated₁).extract 0 0 ++ srcRaw ++
                      (unionAllocRaw updated₁).extract finish.bytes.toNat (unionAllocRaw updated₁).size).size)
                else k_fn finish) := by
          refine ⟨_, ?_, by rw [← hovw]; with_unfolding_all rfl⟩
          intro finish
          with_unfolding_all rfl
        rcases hovw2 with ⟨k_fn, hk_fn, hovw2⟩
        rw [hend] at hovw2
        dsimp only [Except.mapError, bind, Bind.bind, Except.bind] at hovw2
        rw [hSn] at hovw2
        induction updated₁ using Miri.Memory.Allocation.casesOn
        simp only [allocResultTuple, Option.some.injEq, Prod.mk.injEq] at hu1
        rcases hu1 with ⟨hraw₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        unfold unionAllocRaw Miri.Memory.Allocation.byteSize at hovw2
        unfold unionAllocRaw Miri.Memory.Allocation.byteSize
          Miri.Memory.Allocation.provenanceMap Miri.Memory.Allocation.initializationMask
          Miri.Memory.Allocation.align Miri.Memory.Allocation.mutability
          Miri.Memory.Allocation.extra Miri.Memory.Allocation.nativeBuffer at hk_fn
        dsimp only at hovw2 hk_fn
        rw [hraw₁] at hovw2 hk_fn
        have hupd : destRaw.extract 0 0 ++ srcRaw ++ destRaw.extract S destRaw.size = srcRaw := by
          rw [hlen_dst]
          simp [Nat.min_le_left]
        rw [hupd, hSn, hlen_src, bne_self_eq_false] at hovw2
        simp only [Bool.false_eq_true, ↓reduceIte] at hovw2
        rw [hovw2]
        have hk_spec := hk_fn (translateSizeBytes S)
        rw [hSn, hupd] at hk_spec
        exact hk_spec
      have hmask_u2 : updated₂.initializationMask = ⟨.Lazy true, translateSizeBytes S⟩ := by
        induction updated₂ using Miri.Memory.Allocation.casesOn
        simp only [allocExceptTuple, Option.some.injEq, Prod.mk.injEq] at hu2
        rcases hu2 with ⟨_, _, _, rfl, _, _, _, _⟩
        rfl
      have hap := applyCopy_lazy_true hS hk hle
      rw [← hmask_u2] at hap
      unfold Miri.Memory.Allocation.initializationMask at hap
      rw [hap]
      apply of_allocResultTuple_eq_some srcRaw ?_ hlen_src
      induction updated₂ using Miri.Memory.Allocation.casesOn
      simp only [allocExceptTuple, Option.some.injEq, Prod.mk.injEq] at hu2
      rcases hu2 with ⟨hraw, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rw [hraw]
      rfl
    · rename_i _ reason hovw
      have hovw2 : ∃ (k_fn : Miri.ABI.Size → Except Miri.Memory.AllocError
          (Miri.Memory.Allocation AnnealProv E)),
          (∀ finish, allocExceptTuple (k_fn finish) =
            some ((unionAllocRaw updated₁).extract 0 0 ++ srcRaw ++
              (unionAllocRaw updated₁).extract finish.bytes.toNat (unionAllocRaw updated₁).size,
              updated₁.byteSize, updated₁.provenanceMap, updated₁.initializationMask,
              updated₁.align, updated₁.mutability, updated₁.extra, updated₁.nativeBuffer)) ∧
          Except.error reason =
            (((Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S)).endExclusive |>.mapError
              Miri.Memory.AllocError.memory) >>= fun finish =>
              if (((unionAllocRaw updated₁).extract 0 0 ++ srcRaw ++
                  (unionAllocRaw updated₁).extract finish.bytes.toNat (unionAllocRaw updated₁).size).size !=
                  updated₁.byteSize.bytes.toNat) = true then
                throw (Miri.Memory.AllocError.storageLengthMismatch updated₁.byteSize
                  ((unionAllocRaw updated₁).extract 0 0 ++ srcRaw ++
                    (unionAllocRaw updated₁).extract finish.bytes.toNat (unionAllocRaw updated₁).size).size)
              else k_fn finish) := by
        refine ⟨_, ?_, by rw [← hovw]; with_unfolding_all rfl⟩
        intro finish
        with_unfolding_all rfl
      rcases hovw2 with ⟨k_fn, hk_fn, hovw2⟩
      rw [hend] at hovw2
      dsimp only [Except.mapError, bind, Bind.bind, Except.bind] at hovw2
      rw [hSn] at hovw2
      induction updated₁ using Miri.Memory.Allocation.casesOn
      simp only [allocResultTuple, Option.some.injEq, Prod.mk.injEq] at hu1
      rcases hu1 with ⟨hraw₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      unfold unionAllocRaw Miri.Memory.Allocation.byteSize at hovw2
      unfold unionAllocRaw Miri.Memory.Allocation.byteSize
        Miri.Memory.Allocation.provenanceMap Miri.Memory.Allocation.initializationMask
        Miri.Memory.Allocation.align Miri.Memory.Allocation.mutability
        Miri.Memory.Allocation.extra Miri.Memory.Allocation.nativeBuffer at hk_fn
      dsimp only at hovw2 hk_fn
      rw [hraw₁] at hovw2 hk_fn
      have hupd : destRaw.extract 0 0 ++ srcRaw ++ destRaw.extract S destRaw.size = srcRaw := by
        rw [hlen_dst]
        simp [Nat.min_le_left]
      rw [hupd, hSn, hlen_src, bne_self_eq_false] at hovw2
      simp only [Bool.false_eq_true, ↓reduceIte] at hovw2
      have hk_spec := hk_fn (translateSizeBytes S)
      rw [← hovw2] at hk_spec
      cases hk_spec
  · rename_i _ _ hprep_ovw
    have hpo := hprep_ovw
    with_unfolding_all
      conv at hpo => lhs; whnf
      rw [hslice_dst] at hpo
      dsimp only [Id.run, bind, Bind.bind, pure, Pure.pure] at hpo
      simp only [hnz_sz, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false] at hpo
      conv at hpo => lhs; arg 2; whnf
      simp only [hset_dst, Except.mapError] at hpo
      dsimp only [bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure] at hpo
      rw [hclr_dst] at hpo
      cases hpo

set_option maxHeartbeats 800000 in
/-- Running `Miri.Memory.Allocation.copy` with `sameAllocation = true` and
`nonoverlapping = true` on a mutable `S`-byte union allocation `src` with at
least one initialized byte (`IsUnionPrefixMask S k`, `ValidScalarBytes k`) fails
with `AllocError.copyRangesOverlap` (`copy_nonoverlapping` self-copy UB). -/
theorem union_copy_self_overlap_err {E : Type}
    {src : Miri.Memory.Allocation AnnealProv E} {S k : Nat}
    (hS : ValidScalarBytes S) (hk : ValidScalarBytes k) (hle : k ≤ S)
    (hlen : src.len = S) (hsz : src.byteSize = translateSizeBytes S)
    (hmut : src.mutability = .Mut)
    (hprov : src.provenanceMap = Miri.Memory.ProvenanceMap.new)
    (hmask : IsUnionPrefixMask S k src.initializationMask) :
    ∃ st' : Miri.Memory.Allocation AnnealProv E,
      Miri.Memory.Allocation.copy src
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S))
        Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8) true true src =
        .error .copyRangesOverlap st' := by
  have hS16 : S ≤ 16 := by rcases hS with rfl | rfl | rfl | rfl | rfl <;> omega
  have hend : (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S)).endExclusive =
      .ok (translateSizeBytes S) := by
    rcases hS with rfl | rfl | rfl | rfl | rfl <;> rfl
  have hnz_sz : ((Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S)).size.bytes ==
      0) = false := by
    rcases hS with rfl | rfl | rfl | rfl | rfl <;> rfl
  have hpos_sz : (Miri.ABI.Size.ZERO.bytes < (translateSizeBytes S).bytes) := by
    rcases hS with rfl | rfl | rfl | rfl | rfl <;> decide
  have hslice : Miri.Memory.Allocation.getBytesUnchecked src
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S)) =
      .ok ((unionAllocRaw src).extract 0 S) := by
    rw [u_getBytesUnchecked_eq, u_checkedSlice_prefix hlen hsz hS16 (Nat.le_refl S)]
  unfold Miri.Memory.Allocation.getBytesUnchecked at hslice
  have hprep_prov := provenanceMap_prepareCopy_new hS (unionAllocRaw src)
  unfold unionAllocRaw at hprep_prov
  have hno_uninit := unionInitCopy_noBytesInit hS hk hle
  have hmul : (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S)).size.mul 1 =
      .ok (translateSizeBytes S) := by
    rcases hS with rfl | rfl | rfl | rfl | rfl <;> rfl
  have hmask_len := hmask.len_eq
  induction src using Miri.Memory.Allocation.casesOn
  rename_i srcRaw srcSz srcProv srcMask srcAlign srcMut srcExtra srcNat
  change srcRaw.size = S at hlen
  change srcSz = translateSizeBytes S at hsz
  change srcMut = .Mut at hmut
  change srcProv = Miri.Memory.ProvenanceMap.new at hprov
  change IsUnionPrefixMask S k srcMask at hmask
  change srcMask.len = translateSizeBytes S at hmask_len
  have hprep_mask := isUnionPrefixMask_prepareCopy hS hk hle hmask
  change _ = Except.ok (srcRaw.extract 0 S) at hslice
  change (Miri.Memory.ProvenanceMap.new (Prov := AnnealProv)).prepareCopy
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S))
      srcRaw (Miri.ABI.Size.ofBytes 8) = .ok ⟨#[], #[]⟩ at hprep_prov
  subst hsz hmut hprov
  have hset_dst : srcMask.setRange
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S)) true =
      .ok ⟨.Lazy true, translateSizeBytes S⟩ :=
    initMask_setRange_full_overwrite srcMask
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S))
      (translateSizeBytes S) true hend rfl (by rw [hmask_len]; exact UInt64.le_refl _)
  have hclr_dst := Miri.Memory.ProvenanceMap.clear_new (P := AnnealProv)
    (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S)) srcRaw
    (Miri.ABI.Size.ofBytes 8) (translateSizeBytes S) (by decide) hend
  unfold Miri.Memory.Allocation.copy Miri.Memory.Allocation.copyRepeatedly
  rw [hslice]
  dsimp only [Id.run, bind, Bind.bind, pure, Pure.pure]
  rw [hmul]
  dsimp only [bind, Bind.bind, pure, Pure.pure]
  rw [hslice]
  dsimp only [bind, Bind.bind, pure, Pure.pure]
  rw [hprep_prov]
  dsimp only [bind, Bind.bind, pure, Pure.pure]
  rw [hprep_mask]
  dsimp only [bind, Bind.bind, pure, Pure.pure]
  split
  · rename_i _ updated₁ _
    simp only [hno_uninit, Bool.false_eq_true, ↓reduceIte, Bool.and_self,
      show (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S)).size =
        translateSizeBytes S from rfl,
      show (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S)).start =
        Miri.ABI.Size.ZERO from rfl,
      hend, hpos_sz, decide_true]
    exact ⟨updated₁, rfl⟩
  · rename_i _ _ hprep_ovw
    have hpo := hprep_ovw
    with_unfolding_all
      conv at hpo => lhs; whnf
      rw [hslice] at hpo
      dsimp only [Id.run, bind, Bind.bind, pure, Pure.pure] at hpo
      simp only [hnz_sz, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false] at hpo
      conv at hpo => lhs; arg 2; whnf
      simp only [hset_dst, Except.mapError] at hpo
      dsimp only [bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure] at hpo
      rw [hclr_dst] at hpo
      cases hpo

set_option maxHeartbeats 800000 in
/-- Running `Miri.Memory.Allocation.copy` from a completely uninitialized
`S`-byte union allocation (`InitMask.new (translateSizeBytes S) false`, such as
`MaybeUninit::uninit()`) into any mutable `S`-byte destination allocation `dest`
takes `copyRepeatedly`'s `initialized.noBytesInit` fast path
(`Allocation.writeUninit`), succeeding for **any** `sameAlloc : Bool` (including
self-copy!) and resetting `dest.initializationMask` to
`InitMask.new (translateSizeBytes S) false`. -/
theorem union_copy_uninit_alloc_spec {E : Type}
    {src dest : Miri.Memory.Allocation AnnealProv E} {S : Nat}
    (hS : ValidScalarBytes S) (sameAlloc : Bool)
    (hlen_src : src.len = S) (hsz_src : src.byteSize = translateSizeBytes S)
    (hprov_src : src.provenanceMap = Miri.Memory.ProvenanceMap.new)
    (hmask_src : src.initializationMask = Miri.Memory.InitMask.new (translateSizeBytes S) false)
    (hlen_dst : dest.len = S) (hsz_dst : dest.byteSize = translateSizeBytes S)
    (hmut_dst : dest.mutability = .Mut)
    (hprov_dst : dest.provenanceMap = Miri.Memory.ProvenanceMap.new)
    (hmask_dst : dest.initializationMask.len = translateSizeBytes S) :
    ∃ dest' : Miri.Memory.Allocation AnnealProv E,
      Miri.Memory.Allocation.copy src
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S))
        Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8) sameAlloc true dest = .ok () dest' ∧
      dest'.byteSize = translateSizeBytes S ∧
      dest'.len = S ∧
      dest'.align = dest.align ∧
      dest'.mutability = .Mut ∧
      dest'.provenanceMap = Miri.Memory.ProvenanceMap.new ∧
      dest'.initializationMask = Miri.Memory.InitMask.new (translateSizeBytes S) false ∧
      dest'.extra = dest.extra ∧
      dest'.nativeBuffer = dest.nativeBuffer ∧
      unionAllocRaw dest' = unionAllocRaw dest := by
  have hS16 : S ≤ 16 := by rcases hS with rfl | rfl | rfl | rfl | rfl <;> omega
  have hend : (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S)).endExclusive =
      .ok (translateSizeBytes S) := by
    rcases hS with rfl | rfl | rfl | rfl | rfl <;> rfl
  have hnz_sz : ((Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S)).size.bytes ==
      0) = false := by
    rcases hS with rfl | rfl | rfl | rfl | rfl <;> rfl
  have hslice_src : Miri.Memory.Allocation.getBytesUnchecked src
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S)) =
      .ok ((unionAllocRaw src).extract 0 S) := by
    rw [u_getBytesUnchecked_eq, u_checkedSlice_prefix hlen_src hsz_src hS16 (Nat.le_refl S)]
  have hslice_dst : Miri.Memory.Allocation.getBytesUnchecked dest
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S)) =
      .ok ((unionAllocRaw dest).extract 0 S) := by
    rw [u_getBytesUnchecked_eq, u_checkedSlice_prefix hlen_dst hsz_dst hS16 (Nat.le_refl S)]
  unfold Miri.Memory.Allocation.getBytesUnchecked at hslice_src hslice_dst
  have hprep_prov := provenanceMap_prepareCopy_new hS (unionAllocRaw src)
  unfold unionAllocRaw at hprep_prov
  have hprep_mask : (Miri.Memory.InitMask.new (translateSizeBytes S) false).prepareCopy
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S)) =
      .ok ⟨false, #[UInt64.ofNat S]⟩ := by
    rcases hS with rfl | rfl | rfl | rfl | rfl <;> with_unfolding_all rfl
  have hmul : (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S)).size.mul 1 =
      .ok (translateSizeBytes S) := by
    rcases hS with rfl | rfl | rfl | rfl | rfl <;> rfl
  induction src using Miri.Memory.Allocation.casesOn
  rename_i srcRaw srcSz srcProv srcMask srcAlign srcMut srcExtra srcNat
  induction dest using Miri.Memory.Allocation.casesOn
  rename_i destRaw destSz destProv destMask destAlign destMut destExtra destNat
  change srcRaw.size = S at hlen_src
  change srcSz = translateSizeBytes S at hsz_src
  change srcProv = Miri.Memory.ProvenanceMap.new at hprov_src
  change srcMask = Miri.Memory.InitMask.new (translateSizeBytes S) false at hmask_src
  change destRaw.size = S at hlen_dst
  change destSz = translateSizeBytes S at hsz_dst
  change destMut = .Mut at hmut_dst
  change destProv = Miri.Memory.ProvenanceMap.new at hprov_dst
  change destMask.len = translateSizeBytes S at hmask_dst
  change _ = Except.ok (srcRaw.extract 0 S) at hslice_src
  change _ = Except.ok (destRaw.extract 0 S) at hslice_dst
  change (Miri.Memory.ProvenanceMap.new (Prov := AnnealProv)).prepareCopy
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S))
      srcRaw (Miri.ABI.Size.ofBytes 8) = .ok ⟨#[], #[]⟩ at hprep_prov
  subst hsz_src hprov_src hmask_src hsz_dst hmut_dst hprov_dst
  have hset_dst : destMask.setRange
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S)) true =
      .ok ⟨.Lazy true, translateSizeBytes S⟩ :=
    initMask_setRange_full_overwrite destMask
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S))
      (translateSizeBytes S) true hend rfl (by rw [hmask_dst]; exact UInt64.le_refl _)
  have hclr_dst := Miri.Memory.ProvenanceMap.clear_new (P := AnnealProv)
    (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S)) destRaw
    (Miri.ABI.Size.ofBytes 8) (translateSizeBytes S) (by decide) hend
  unfold Miri.Memory.Allocation.copy Miri.Memory.Allocation.copyRepeatedly
  rw [hslice_src]
  dsimp only [Id.run, bind, Bind.bind, pure, Pure.pure]
  rw [hmul]
  dsimp only [bind, Bind.bind, pure, Pure.pure]
  rw [hslice_dst]
  dsimp only [bind, Bind.bind, pure, Pure.pure]
  rw [hprep_prov]
  dsimp only [bind, Bind.bind, pure, Pure.pure]
  rw [hprep_mask]
  dsimp only [bind, Bind.bind, pure, Pure.pure]
  split
  · rename_i _ updated₁ hprep_ovw
    have hu1 : allocResultTuple (.ok () updated₁) =
        some (destRaw, translateSizeBytes S, Miri.Memory.ProvenanceMap.new,
          ⟨.Lazy true, translateSizeBytes S⟩, destAlign, .Mut, destExtra, destNat) := by
      have hpo := hprep_ovw
      with_unfolding_all
        conv at hpo => lhs; whnf
        rw [hslice_dst] at hpo
        dsimp only [Id.run, bind, Bind.bind, pure, Pure.pure] at hpo
        simp only [hnz_sz, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false] at hpo
        conv at hpo => lhs; arg 2; whnf
        simp only [hset_dst, Except.mapError] at hpo
        dsimp only [bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure] at hpo
        rw [hclr_dst] at hpo
        cases hpo
        rfl
    have hno_init : (Miri.Memory.InitCopy.mk false #[UInt64.ofNat S]).noBytesInit = true := rfl
    simp only [hno_init, ↓reduceIte]
    have hlen_u1 : updated₁.len = S := by
      induction updated₁ using Miri.Memory.Allocation.casesOn
      simp only [allocResultTuple, Option.some.injEq, Prod.mk.injEq] at hu1
      rcases hu1 with ⟨hraw₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      exact hraw₁ ▸ hlen_dst
    have hsz_u1 : updated₁.byteSize = translateSizeBytes S := by
      induction updated₁ using Miri.Memory.Allocation.casesOn
      simp only [allocResultTuple, Option.some.injEq, Prod.mk.injEq] at hu1
      rcases hu1 with ⟨_, rfl, _⟩; rfl
    have hslice_u1 : Miri.Memory.Allocation.getBytesUnchecked updated₁
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S)) =
        .ok ((unionAllocRaw updated₁).extract 0 S) := by
      rw [u_getBytesUnchecked_eq, u_checkedSlice_prefix hlen_u1 hsz_u1 hS16 (Nat.le_refl S)]
    unfold Miri.Memory.Allocation.getBytesUnchecked at hslice_u1
    have hset_uninit : (Miri.Memory.InitMask.mk (.Lazy true) (translateSizeBytes S)).setRange
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S)) false =
        .ok (Miri.Memory.InitMask.new (translateSizeBytes S) false) :=
      initMask_setRange_full_overwrite _ _ _ false hend rfl (UInt64.le_refl _)
    split
    · rename_i _ _ hwu
      have hwu' := hwu
      induction updated₁ using Miri.Memory.Allocation.casesOn
      simp only [allocResultTuple, Option.some.injEq, Prod.mk.injEq] at hu1
      rcases hu1 with ⟨hraw₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      cases hraw₁
      with_unfolding_all
        conv at hwu' => lhs; whnf
        rw [hslice_u1] at hwu'
        dsimp only [Id.run, bind, Bind.bind, pure, Pure.pure] at hwu'
        simp only [hnz_sz, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false] at hwu'
        conv at hwu' => lhs; arg 2; whnf
        simp only [hset_uninit, Except.mapError] at hwu'
        dsimp only [bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure] at hwu'
        rw [hclr_dst] at hwu'
        cases hwu'
    · rename_i updated₂ hwu
      have hu2 : allocResultTuple (.ok () updated₂) =
          some (destRaw, translateSizeBytes S, Miri.Memory.ProvenanceMap.new,
            Miri.Memory.InitMask.new (translateSizeBytes S) false,
            destAlign, .Mut, destExtra, destNat) := by
        have hwu' := hwu
        induction updated₁ using Miri.Memory.Allocation.casesOn
        simp only [allocResultTuple, Option.some.injEq, Prod.mk.injEq] at hu1
        rcases hu1 with ⟨hraw₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        cases hraw₁
        with_unfolding_all
          conv at hwu' => lhs; whnf
          rw [hslice_u1] at hwu'
          dsimp only [Id.run, bind, Bind.bind, pure, Pure.pure] at hwu'
          simp only [hnz_sz, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false] at hwu'
          conv at hwu' => lhs; arg 2; whnf
          simp only [hset_uninit, Except.mapError] at hwu'
          dsimp only [bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure] at hwu'
          rw [hclr_dst] at hwu'
          cases hwu'
          rfl
      induction updated₂ using Miri.Memory.Allocation.casesOn
      simp only [allocResultTuple, Option.some.injEq, Prod.mk.injEq] at hu2
      rcases hu2 with ⟨hraw₂, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      cases hraw₂
      exact ⟨_, rfl, rfl, hlen_dst, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · rename_i _ _ hprep_ovw
    have hpo := hprep_ovw
    with_unfolding_all
      conv at hpo => lhs; whnf
      rw [hslice_dst] at hpo
      dsimp only [Id.run, bind, Bind.bind, pure, Pure.pure] at hpo
      simp only [hnz_sz, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false] at hpo
      conv at hpo => lhs; arg 2; whnf
      simp only [hset_dst, Except.mapError] at hpo
      dsimp only [bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure] at hpo
      rw [hclr_dst] at hpo
      cases hpo

set_option maxHeartbeats 800000 in
/-- Running `Miri.Memory.Allocation.copy` (`copyRepeatedly ... 1 ...`) from a
non-empty `ArraySliceRel` subslice at `srcOff` into **any** distinct mutable
`totalSz`-byte destination allocation `dest` (regardless of `dest`'s prior raw
bytes or initialization mask, so long as `dest.len = totalBytes` and
`dest.initializationMask.len = totalSz`) overwrites `dest` completely with
`InitMask.new totalSz true`, empty provenance, and
`ArraySliceRel elemKind cnt layouts elems Size.ZERO dest'`. -/
theorem array_copy_alloc_spec
    {elemKind : RigidTy} {cnt : Nat} {layouts : LayoutTable} {elems : List Value}
    {srcOff : Miri.ABI.Size}
    {src dest : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    (hslice : ArraySliceRel elemKind cnt layouts elems srcOff src)
    (hpos : 0 < cnt)
    (helem_pos : 0 < (translateTy { kind := elemKind, layoutIdx := 0 } layouts).layout.size.bytes.toNat)
    (hlen_dst_in : dest.len =
      cnt * (translateTy { kind := elemKind, layoutIdx := 0 } layouts).layout.size.bytes.toNat)
    (hsz_dst : dest.byteSize =
      Miri.ABI.Size.ofBytes
        (UInt64.ofNat
          (cnt * (translateTy { kind := elemKind, layoutIdx := 0 } layouts).layout.size.bytes.toNat)))
    (hmut_dst : dest.mutability = .Mut)
    (hprov_dst : dest.provenanceMap = Miri.Memory.ProvenanceMap.new)
    (hmask_dst : dest.initializationMask.len = dest.byteSize) :
    let totalBytes :=
      cnt * (translateTy { kind := elemKind, layoutIdx := 0 } layouts).layout.size.bytes.toNat
    let totalSz := Miri.ABI.Size.ofBytes (UInt64.ofNat totalBytes)
    ∃ dest' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree),
      Miri.Memory.Allocation.copy src (Miri.Memory.allocRange srcOff totalSz)
        Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8) false true dest = .ok () dest' ∧
      dest'.byteSize = totalSz ∧
      dest'.len = totalBytes ∧
      dest'.align = dest.align ∧
      dest'.mutability = .Mut ∧
      dest'.provenanceMap = Miri.Memory.ProvenanceMap.new ∧
      dest'.initializationMask = Miri.Memory.InitMask.new totalSz true ∧
      dest'.extra = dest.extra ∧
      dest'.nativeBuffer = dest.nativeBuffer ∧
      ArraySliceRel elemKind cnt layouts elems Miri.ABI.Size.ZERO dest' := by
  intro totalBytes totalSz
  have htot_pos : 0 < totalBytes := Nat.mul_pos hpos helem_pos
  have hbs_src : src.byteSize.bytes.toNat < 2 ^ 64 := UInt64.toNat_lt _
  have hin_src_nat : srcOff.bytes.toNat + totalBytes ≤ src.byteSize.bytes.toNat :=
    hslice.slice_in_bounds
  have htot_lt64 : totalBytes < 2 ^ 64 := by omega
  have htot_toNat : totalSz.bytes.toNat = totalBytes := by
    simp only [totalSz, Miri.ABI.Size.ofBytes, UInt64.toNat_ofNat']
    exact Nat.mod_eq_of_lt htot_lt64
  have hpos_sz : 0 < totalSz.bytes.toNat := by rw [htot_toNat]; exact htot_pos
  have hin_src : srcOff.bytes.toNat + totalSz.bytes.toNat ≤ src.byteSize.bytes.toNat := by
    rw [htot_toNat]; exact hin_src_nat
  have hlt_src : srcOff.bytes.toNat + totalSz.bytes.toNat < 2 ^ 64 := by omega
  have hsz_dst_eq : dest.byteSize = totalSz := hsz_dst
  have hlen_dst : dest.len = dest.byteSize.bytes.toNat := by
    rw [hlen_dst_in, hsz_dst_eq, htot_toNat]
  have hin_dst : Miri.ABI.Size.ZERO.bytes.toNat + totalSz.bytes.toNat ≤ dest.byteSize.bytes.toNat := by
    rw [hsz_dst_eq]; simp [Miri.ABI.Size.ZERO]
  have hslice_src := getBytesUnchecked_at (A := src) srcOff totalSz hslice.alloc_len hin_src
  have hslice_dst := getBytesUnchecked_at (A := dest) Miri.ABI.Size.ZERO totalSz hlen_dst hin_dst
  unfold Miri.Memory.Allocation.getBytesUnchecked at hslice_src hslice_dst
  have hprep_prov := provenanceMap_prepareCopy_new_at srcOff totalSz hlt_src (unionAllocRaw src)
  have hprep_mask := initMask_new_true_prepareCopy (srcSz := src.byteSize) hpos_sz hin_src
  have hmul : (Miri.Memory.allocRange srcOff totalSz).size.mul 1 = .ok totalSz := by
    simp [Miri.ABI.Size.mul, Miri.Memory.allocRange, Miri.ABI.Size.ofBytes]
  have hend_dst : (Miri.Memory.allocRange Miri.ABI.Size.ZERO totalSz).endExclusive = .ok totalSz := by
    have hlt0 : Miri.ABI.Size.ZERO.bytes.toNat + totalSz.bytes.toNat < 2 ^ 64 := by
      simp [Miri.ABI.Size.ZERO]
      exact UInt64.toNat_lt totalSz.bytes
    have h := allocRange_endExclusive_of_lt (off := Miri.ABI.Size.ZERO) (sz := totalSz) hlt0
    simpa [Miri.ABI.Size.ZERO, Miri.ABI.Size.ofBytes] using h
  have hloop (b : Array UInt8) :
      forIn [: (1 : UInt64).toNat] (#[] : Array UInt8) (fun _ r =>
        (pure (ForInStep.yield (r ++ b)) : Id (ForInStep (Array UInt8)))) = b := by
    simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
    rfl
  have hnz_sz : ((Miri.Memory.allocRange Miri.ABI.Size.ZERO totalSz).size.bytes == 0) = false := by
    cases h : ((Miri.Memory.allocRange Miri.ABI.Size.ZERO totalSz).size.bytes == 0) with
    | false => rfl
    | true =>
      have := eq_of_beq h
      dsimp [Miri.Memory.allocRange] at this
      rw [this] at hpos_sz
      simp at hpos_sz
  let copiedRaw := (unionAllocRaw src).extract srcOff.bytes.toNat
    (srcOff.bytes.toNat + totalSz.bytes.toNat)
  have hcopied_len : copiedRaw.size = totalBytes := by
    have hraw_src : (unionAllocRaw src).size = src.byteSize.bytes.toNat := hslice.alloc_len
    simp [copiedRaw, Array.size_extract, hraw_src, htot_toNat]
    omega
  have hcopy_res : ∃ dest' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree),
      Miri.Memory.Allocation.copy src (Miri.Memory.allocRange srcOff totalSz)
        Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8) false true dest = .ok () dest' ∧
      dest'.byteSize = totalSz ∧
      dest'.len = totalBytes ∧
      dest'.align = dest.align ∧
      dest'.mutability = .Mut ∧
      dest'.provenanceMap = Miri.Memory.ProvenanceMap.new ∧
      dest'.initializationMask = Miri.Memory.InitMask.new totalSz true ∧
      dest'.extra = dest.extra ∧
      dest'.nativeBuffer = dest.nativeBuffer ∧
      unionAllocRaw dest' = copiedRaw := by
    have hprov_src := hslice.alloc_prov
    have hmask_src := hslice.alloc_mask
    have hmask_dst' : dest.initializationMask.len = totalSz := by
      rw [← hsz_dst_eq]; exact hmask_dst
    induction src using Miri.Memory.Allocation.casesOn
    rename_i srcRaw srcSz srcProv srcMask srcAlign srcMut srcExtra srcNat
    induction dest using Miri.Memory.Allocation.casesOn
    rename_i destRaw destSz destProv destMask destAlign destMut destExtra destNat
    change srcProv = Miri.Memory.ProvenanceMap.new at hprov_src
    change srcMask = Miri.Memory.InitMask.new srcSz true at hmask_src
    change destRaw.size = totalBytes at hlen_dst_in
    change destSz = totalSz at hsz_dst
    change destMut = .Mut at hmut_dst
    change destProv = Miri.Memory.ProvenanceMap.new at hprov_dst
    change destMask.len = totalSz at hmask_dst'
    change _ = Except.ok copiedRaw at hslice_src
    change _ = Except.ok (destRaw.extract 0 (0 + totalSz.bytes.toNat)) at hslice_dst
    change (Miri.Memory.ProvenanceMap.new (Prov := AnnealProv)).prepareCopy
        (Miri.Memory.allocRange srcOff totalSz) srcRaw (Miri.ABI.Size.ofBytes 8) = .ok ⟨#[], #[]⟩ at hprep_prov
    change (Miri.Memory.InitMask.new srcSz true).prepareCopy
        (Miri.Memory.allocRange srcOff totalSz) = .ok ⟨true, #[totalSz.bytes]⟩ at hprep_mask
    subst hprov_src hmask_src hsz_dst hmut_dst hprov_dst
    unfold Miri.Memory.Allocation.copy Miri.Memory.Allocation.copyRepeatedly
    simp only [hloop]
    rw [hslice_src]
    dsimp only [Id.run, bind, Bind.bind, pure, Pure.pure]
    rw [hmul]
    dsimp only [bind, Bind.bind, pure, Pure.pure]
    rw [hslice_dst]
    dsimp only [bind, Bind.bind, pure, Pure.pure]
    rw [hprep_prov]
    dsimp only [bind, Bind.bind, pure, Pure.pure]
    rw [hprep_mask]
    dsimp only [bind, Bind.bind, pure, Pure.pure]
    have hno_init : (Miri.Memory.InitCopy.mk true #[totalSz.bytes]).noBytesInit = false := rfl
    simp only [hno_init, show ((1 : UInt64) == 0) = false from rfl,
      show (Miri.Memory.allocRange srcOff totalSz).size = totalSz from rfl,
      provenanceMap_applyCopy_empty, Bool.not_true, Bool.false_and, Bool.and_false,
      Bool.false_eq_true, ↓reduceIte]
    have hset_dst : destMask.setRange
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO totalSz) true =
        .ok ⟨.Lazy true, totalSz⟩ :=
      initMask_setRange_full_overwrite destMask
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO totalSz) totalSz true hend_dst rfl
        (by rw [hmask_dst']; exact UInt64.le_refl _)
    have hclr_dst := Miri.Memory.ProvenanceMap.clear_new (P := AnnealProv)
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO totalSz) destRaw
      (Miri.ABI.Size.ofBytes 8) totalSz (by decide) hend_dst
    split
    · rename_i _ updated₁ hprep_ovw
      have hu1 : allocResultTuple (.ok () updated₁) =
          some (destRaw, totalSz, Miri.Memory.ProvenanceMap.new,
            ⟨.Lazy true, totalSz⟩, destAlign, .Mut, destExtra, destNat) := by
        have hpo := hprep_ovw
        with_unfolding_all
          conv at hpo => lhs; whnf
          rw [hslice_dst] at hpo
          dsimp only [Id.run, bind, Bind.bind, pure, Pure.pure] at hpo
          simp only [hnz_sz, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false] at hpo
          conv at hpo => lhs; arg 2; whnf
          simp only [hset_dst, Except.mapError] at hpo
          dsimp only [bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure] at hpo
          rw [hclr_dst] at hpo
          cases hpo
          rfl
      split
      · rename_i _ updated₂ hovw
        have hu2 : allocExceptTuple (.ok updated₂) =
            some (copiedRaw, totalSz, Miri.Memory.ProvenanceMap.new,
              ⟨.Lazy true, totalSz⟩, destAlign, .Mut, destExtra, destNat) := by
          have hovw2 : ∃ (k_fn : Miri.ABI.Size → Except Miri.Memory.AllocError
              (Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree))),
              (∀ finish, allocExceptTuple (k_fn finish) =
                some ((unionAllocRaw updated₁).extract 0 0 ++ copiedRaw ++
                  (unionAllocRaw updated₁).extract finish.bytes.toNat (unionAllocRaw updated₁).size,
                  updated₁.byteSize, updated₁.provenanceMap, updated₁.initializationMask,
                  updated₁.align, updated₁.mutability, updated₁.extra, updated₁.nativeBuffer)) ∧
              Except.ok updated₂ =
                (((Miri.Memory.allocRange Miri.ABI.Size.ZERO totalSz).endExclusive |>.mapError
                  Miri.Memory.AllocError.memory) >>= fun finish =>
                  if (((unionAllocRaw updated₁).extract 0 0 ++ copiedRaw ++
                      (unionAllocRaw updated₁).extract finish.bytes.toNat (unionAllocRaw updated₁).size).size !=
                      updated₁.byteSize.bytes.toNat) = true then
                    throw (Miri.Memory.AllocError.storageLengthMismatch updated₁.byteSize
                      ((unionAllocRaw updated₁).extract 0 0 ++ copiedRaw ++
                        (unionAllocRaw updated₁).extract finish.bytes.toNat (unionAllocRaw updated₁).size).size)
                  else k_fn finish) := by
            refine ⟨_, ?_, by rw [← hovw]; with_unfolding_all rfl⟩
            intro finish
            with_unfolding_all rfl
          rcases hovw2 with ⟨k_fn, hk_fn, hovw2⟩
          rw [hend_dst] at hovw2
          dsimp only [Except.mapError, bind, Bind.bind, Except.bind] at hovw2
          induction updated₁ using Miri.Memory.Allocation.casesOn
          simp only [allocResultTuple, Option.some.injEq, Prod.mk.injEq] at hu1
          rcases hu1 with ⟨hraw₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
          unfold unionAllocRaw Miri.Memory.Allocation.byteSize at hovw2
          unfold unionAllocRaw Miri.Memory.Allocation.byteSize
            Miri.Memory.Allocation.provenanceMap Miri.Memory.Allocation.initializationMask
            Miri.Memory.Allocation.align Miri.Memory.Allocation.mutability
            Miri.Memory.Allocation.extra Miri.Memory.Allocation.nativeBuffer at hk_fn
          dsimp only at hovw2 hk_fn
          rw [hraw₁] at hovw2 hk_fn
          have hupd : destRaw.extract 0 0 ++ copiedRaw ++
              destRaw.extract totalSz.bytes.toNat destRaw.size = copiedRaw := by
            rw [htot_toNat, hlen_dst_in]
            simp [Nat.min_le_left]
          rw [hupd, hcopied_len, htot_toNat, bne_self_eq_false] at hovw2
          simp only [Bool.false_eq_true, ↓reduceIte] at hovw2
          rw [hovw2]
          have hk_spec := hk_fn totalSz
          rw [hupd] at hk_spec
          exact hk_spec
        have hmask_u2 : updated₂.initializationMask = ⟨.Lazy true, totalSz⟩ := by
          induction updated₂ using Miri.Memory.Allocation.casesOn
          simp only [allocExceptTuple, Option.some.injEq, Prod.mk.injEq] at hu2
          rcases hu2 with ⟨_, _, _, rfl, _, _, _, _⟩
          rfl
        have hap := initMask_applyCopy_full totalSz hpos_sz
        rw [← hmask_u2] at hap
        unfold Miri.Memory.Allocation.initializationMask at hap
        rw [hap]
        dsimp only [bind, Bind.bind, pure, Pure.pure]
        induction updated₂ using Miri.Memory.Allocation.casesOn
        simp only [allocExceptTuple, Option.some.injEq, Prod.mk.injEq] at hu2
        rcases hu2 with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        exact ⟨_, rfl, rfl, hcopied_len, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · rename_i _ reason hovw
        have hovw2 : ∃ (k_fn : Miri.ABI.Size → Except Miri.Memory.AllocError
            (Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree))),
            (∀ finish, allocExceptTuple (k_fn finish) =
              some ((unionAllocRaw updated₁).extract 0 0 ++ copiedRaw ++
                (unionAllocRaw updated₁).extract finish.bytes.toNat (unionAllocRaw updated₁).size,
                updated₁.byteSize, updated₁.provenanceMap, updated₁.initializationMask,
                updated₁.align, updated₁.mutability, updated₁.extra, updated₁.nativeBuffer)) ∧
            Except.error reason =
              (((Miri.Memory.allocRange Miri.ABI.Size.ZERO totalSz).endExclusive |>.mapError
                Miri.Memory.AllocError.memory) >>= fun finish =>
                if (((unionAllocRaw updated₁).extract 0 0 ++ copiedRaw ++
                    (unionAllocRaw updated₁).extract finish.bytes.toNat (unionAllocRaw updated₁).size).size !=
                    updated₁.byteSize.bytes.toNat) = true then
                  throw (Miri.Memory.AllocError.storageLengthMismatch updated₁.byteSize
                    ((unionAllocRaw updated₁).extract 0 0 ++ copiedRaw ++
                      (unionAllocRaw updated₁).extract finish.bytes.toNat (unionAllocRaw updated₁).size).size)
                else k_fn finish) := by
          refine ⟨_, ?_, by rw [← hovw]; with_unfolding_all rfl⟩
          intro finish
          with_unfolding_all rfl
        rcases hovw2 with ⟨k_fn, hk_fn, hovw2⟩
        rw [hend_dst] at hovw2
        dsimp only [Except.mapError, bind, Bind.bind, Except.bind] at hovw2
        induction updated₁ using Miri.Memory.Allocation.casesOn
        simp only [allocResultTuple, Option.some.injEq, Prod.mk.injEq] at hu1
        rcases hu1 with ⟨hraw₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        unfold unionAllocRaw Miri.Memory.Allocation.byteSize at hovw2
        unfold unionAllocRaw Miri.Memory.Allocation.byteSize
          Miri.Memory.Allocation.provenanceMap Miri.Memory.Allocation.initializationMask
          Miri.Memory.Allocation.align Miri.Memory.Allocation.mutability
          Miri.Memory.Allocation.extra Miri.Memory.Allocation.nativeBuffer at hk_fn
        dsimp only at hovw2 hk_fn
        rw [hraw₁] at hovw2 hk_fn
        have hupd : destRaw.extract 0 0 ++ copiedRaw ++
            destRaw.extract totalSz.bytes.toNat destRaw.size = copiedRaw := by
          rw [htot_toNat, hlen_dst_in]
          simp [Nat.min_le_left]
        rw [hupd, hcopied_len, htot_toNat, bne_self_eq_false] at hovw2
        simp only [Bool.false_eq_true, ↓reduceIte] at hovw2
        have hk_spec := hk_fn totalSz
        rw [← hovw2] at hk_spec
        cases hk_spec
    · rename_i _ _ hprep_ovw
      have hpo := hprep_ovw
      with_unfolding_all
        conv at hpo => lhs; whnf
        rw [hslice_dst] at hpo
        dsimp only [Id.run, bind, Bind.bind, pure, Pure.pure] at hpo
        simp only [hnz_sz, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false] at hpo
        conv at hpo => lhs; arg 2; whnf
        simp only [hset_dst, Except.mapError] at hpo
        dsimp only [bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure] at hpo
        rw [hclr_dst] at hpo
        cases hpo
  obtain ⟨dest', hcopy, hsz', hlen', hal', hmut', hprov', hmask', hex', hnat', hraw'⟩ := hcopy_res
  refine ⟨dest', hcopy, hsz', hlen', hal', hmut', hprov', hmask', hex', hnat', ?_⟩
  refine
    { elems_len := hslice.elems_len
      alloc_len := by rw [hlen', hsz', htot_toNat]
      alloc_mut := hmut'
      alloc_prov := hprov'
      alloc_mask := by rw [hmask', hsz']
      slice_in_bounds := by
        rw [hsz', htot_toNat]; simp [Miri.ABI.Size.ZERO]; exact Nat.le_refl totalBytes
      elem_rel := ?_ }
  intro k elemVal hget
  have hk_lt : k < cnt := by
    rw [← hslice.elems_len]
    exact (List.getElem?_eq_some_iff.mp (by rwa [← get?_eq_getElem?])).1
  obtain ⟨sc, msc, hv, hesz, hbool, hchar, hrel, hread_src⟩ := hslice.elem_rel k elemVal hget
  refine ⟨sc, msc, hv, hesz, hbool, hchar, hrel, ?_⟩
  let elemLay := (translateTy { kind := elemKind, layoutIdx := 0 } layouts).layout
  let es := elemLay.size.bytes.toNat
  have hk1_le : (k + 1) * es ≤ totalBytes := Nat.mul_le_mul_right _ (by omega)
  have hmul_add : (k + 1) * es = k * es + es := Nat.add_mul k 1 es |>.trans (by simp)
  have hkes_le : k * es + es ≤ totalBytes := by rw [← hmul_add]; exact hk1_le
  let dstElemOff := Miri.ABI.Size.ofBytes (Miri.ABI.Size.ZERO.bytes + UInt64.ofNat (k * es))
  let srcElemOff := Miri.ABI.Size.ofBytes (srcOff.bytes + UInt64.ofNat (k * es))
  have hdstOff_nat : dstElemOff.bytes.toNat = k * es := by
    simp only [dstElemOff, Miri.ABI.Size.ofBytes, Miri.ABI.Size.ZERO, UInt64.zero_add,
      UInt64.toNat_ofNat']
    exact Nat.mod_eq_of_lt (by omega)
  have hsrcOff_nat : srcElemOff.bytes.toNat = srcOff.bytes.toNat + k * es := by
    have h1 : k * es < 2 ^ 64 := by omega
    have h2 : srcOff.bytes.toNat + k * es < 2 ^ 64 := by omega
    simp only [srcElemOff, Miri.ABI.Size.ofBytes, UInt64.toNat_add, UInt64.toNat_ofNat',
      Nat.mod_eq_of_lt h1]
    exact Nat.mod_eq_of_lt h2
  have hin_elem_dst : dstElemOff.bytes.toNat + es ≤ dest'.byteSize.bytes.toNat := by
    rw [hdstOff_nat, hsz', htot_toNat]; exact hkes_le
  have hin_elem_src : srcElemOff.bytes.toNat + es ≤ src.byteSize.bytes.toNat := by
    rw [hsrcOff_nat]; omega
  have hend_elem_dst := allocRange_endExclusive_of_lt
    (off := dstElemOff) (sz := elemLay.size)
    (by change dstElemOff.bytes.toNat + es < 2 ^ 64; omega)
  have hend_elem_src := allocRange_endExclusive_of_lt
    (off := srcElemOff) (sz := elemLay.size)
    (by change srcElemOff.bytes.toNat + es < 2 ^ 64; omega)
  have hinit_dst : dest'.initializationMask.isRangeInitialized
      (Miri.Memory.allocRange dstElemOff elemLay.size) = .ok (.ok ()) := by
    rw [hmask']
    apply Miri.Memory.InitMask.lazy_initialized_query _ _ _ hend_elem_dst
    rw [UInt64.le_iff_toNat_le]
    have hfin_d : (Miri.ABI.Size.ofBytes (dstElemOff.bytes + elemLay.size.bytes)).bytes.toNat =
        dstElemOff.bytes.toNat + es := by
      simp only [Miri.ABI.Size.ofBytes, UInt64.toNat_add]
      exact Nat.mod_eq_of_lt (by change dstElemOff.bytes.toNat + es < 2 ^ 64; omega)
    rw [hfin_d, htot_toNat, hdstOff_nat]
    exact hkes_le
  have hinit_src : src.initializationMask.isRangeInitialized
      (Miri.Memory.allocRange srcElemOff elemLay.size) = .ok (.ok ()) := by
    rw [hslice.alloc_mask]
    apply Miri.Memory.InitMask.lazy_initialized_query _ _ _ hend_elem_src
    rw [UInt64.le_iff_toNat_le]
    have hfin_s : (Miri.ABI.Size.ofBytes (srcElemOff.bytes + elemLay.size.bytes)).bytes.toNat =
        srcElemOff.bytes.toNat + es := by
      simp only [Miri.ABI.Size.ofBytes, UInt64.toNat_add]
      exact Nat.mod_eq_of_lt (by change srcElemOff.bytes.toNat + es < 2 ^ 64; omega)
    rw [hfin_s]
    exact hin_elem_src
  have hbytes_dst := getBytesUnchecked_at (A := dest') dstElemOff elemLay.size
    (by rw [hlen', hsz', htot_toNat]) hin_elem_dst
  have hbytes_src := getBytesUnchecked_at (A := src) srcElemOff elemLay.size
    hslice.alloc_len hin_elem_src
  have hextr_eq : (unionAllocRaw dest').extract dstElemOff.bytes.toNat
      (dstElemOff.bytes.toNat + es) =
      (unionAllocRaw src).extract srcElemOff.bytes.toNat (srcElemOff.bytes.toNat + es) := by
    rw [hraw']
    dsimp only [copiedRaw]
    rw [Array.extract_extract, hdstOff_nat, hsrcOff_nat, htot_toNat]
    congr 1
    omega
  change dest'.readScalar annealTargetDataLayout
      (Miri.Memory.allocRange dstElemOff elemLay.size) false = _
  change src.readScalar annealTargetDataLayout
      (Miri.Memory.allocRange srcElemOff elemLay.size) false = _ at hread_src
  rw [u_readScalar_eq] at hread_src ⊢
  unfold uReadScalar at hread_src ⊢
  rw [hinit_dst, hbytes_dst]
  rw [hinit_src, hbytes_src] at hread_src
  dsimp only [es] at hextr_eq
  rw [hextr_eq]
  exact hread_src

/-! ## 9. Union State Relation

`StateRel`'s `MemPlaceRel` requires every byte of an initialized memory-backed
local to be initialized (`val_consistent`), so it cannot relate a union whose
smaller field was written. `StateRelLM2_4` extends `StateRel` with two ways to
relate an initialized `n`-field Anneal union to a memory-backed `UnionMemRel`
allocation whose bytes `[0, k)` (`k = sc.sizeBytes`) hold `sc` and are
initialized while its trailing bytes `[k, S)` are not:
* `UnionLocalRel.union`: a plain single-active-field union
  `Value.aggregate 0 (unionSlotFields n f (.scalar sc))` (`f < n`, matching
  `evalAggregateAdtUnionValue?` and same-or-wider `rebuildUnionFieldsAfterWriteOpt`);
* `UnionLocalRel.unionOverlay`: a union carrying a `D13a` raw-byte overlay
  `Value.aggregate 0 (unionSlotFields n j (.scalar sc_low) ++ [.aggregate 0 (encodeRawAbstractByteVals mergedBytes)])`
  after a narrower projected scalar field write (`sc_low.sizeBytes < sc.sizeBytes`,
  `UnionOverlaySlotSpec`).
Every `StateRel` is a `StateRelLM2_4` (`StateRel.toLM2_4`). -/

/-- The `n`-slot Anneal field list of a union whose active field `f < n` holds `v`
and whose remaining `n - 1` sibling slots hold `.unit`, matching both
`evalAggregateAdtUnionValue?` and `rebuildUnionFieldsAfterWriteOpt`. -/
def unionSlotFields (n f : Nat) (v : Value) : List Value :=
  appendValueList (replicateValue f .unit) (v :: replicateValue (Nat.sub n (.succ f)) .unit)

/-- A union of `S ∈ {1, 2, 4, 8, 16}` bytes: its `lean-miri` layout has
`FieldsShape.Union` with at least one field, size `S`, an alignment that
`Align.fromBytes` accepts, `uTy.layoutIdx ∈ (0, 900)` (so `100 + uTy.layoutIdx < 1000`
stays inside `LeanMiriSpec.Translate`'s ADT `TyId` range in `unionFieldLayoutOf`),
and a well-formed `FieldsShape.union` entry in `layouts` whose scalar
`fieldLayouts` match `encodeByLayoutIdxAux`. -/
structure WellTypedUnionTy (layouts : LayoutTable) (uTy : Ty) (S : Nat) : Prop where
  size_valid : ValidScalarBytes S
  fields_union : ∃ n, (translateTy uTy layouts).layout.fields = .Union n ∧ 0 < n
  size_eq : (translateTy uTy layouts).layout.size = translateSizeBytes S
  sized : (translateTy uTy layouts).layout.isSized = true
  align_le : (translateTy uTy layouts).layout.align.abi.pow2 ≤ 29
  adt_spec : ∃ defPath args tl n,
    uTy.kind = .adt defPath args ∧
    0 < uTy.layoutIdx ∧
    uTy.layoutIdx < 900 ∧
    layouts.lookup uTy.layoutIdx = some tl ∧
    tl.fields = .union n ∧
    tl.variants = .single 0 ∧
    tl.isUninhabited = false ∧
    tl.size.bytes = S ∧
    tl.fieldLayouts.length = n ∧
    layouts.pointerBits = 64 ∧
    layouts.isLittleEndian = true ∧
    ∀ idx flIdx, get? tl.fieldLayouts idx = some flIdx →
      ∃ fTl, layouts.lookup flIdx = some fTl ∧
        fTl.isUninhabited = false ∧
        ValidScalarBytes fTl.size.bytes ∧
        fTl.size.bytes ≤ S ∧
        ∀ (fTy : Ty) (sc : MirAst.ScalarInt) (msc : Miri.Memory.ScalarInt),
          IsPrimScalarTy fTy →
          ImmediateRel fTy layouts (.scalar sc) (.scalar (.fromScalarInt msc)) →
          sc.sizeBytes = fTl.size.bytes →
          ∀ fuel', encodeByLayoutIdxAux (fuel' + 1) layouts flIdx (.scalar sc) =
            encodeScalarBytes sc .none

/-- Construct a `WellTypedUnionTy` from purely structural layout facts whenever
every union field layout `fTl` has a full-range scalar (or non-range-restricted)
`backendRepr` (`vr.start = 0 ∧ vr.end_ + 1 = scalarModulus fTl.size.bytes`),
discharging the `encodeByLayoutIdxAux` codec clause once and for all. -/
theorem WellTypedUnionTy.of_fullRangeScalarFields
    {layouts : LayoutTable} {uTy : Ty} {S : Nat}
    (hsz : ValidScalarBytes S)
    (hfu : ∃ n, (translateTy uTy layouts).layout.fields = .Union n ∧ 0 < n)
    (hsize : (translateTy uTy layouts).layout.size = translateSizeBytes S)
    (hsized : (translateTy uTy layouts).layout.isSized = true)
    (halign : (translateTy uTy layouts).layout.align.abi.pow2 ≤ 29)
    {defPath : DefPath} {args : List RigidTy} {tl : TypeLayout} {n : Nat}
    (hkind : uTy.kind = .adt defPath args)
    (hidx_pos : 0 < uTy.layoutIdx)
    (hidx_lt : uTy.layoutIdx < 900)
    (hlook : layouts.lookup uTy.layoutIdx = some tl)
    (htl_fields : tl.fields = .union n)
    (htl_var : tl.variants = .single 0)
    (htl_uninh : tl.isUninhabited = false)
    (htl_sz : tl.size.bytes = S)
    (htl_len : tl.fieldLayouts.length = n)
    (hptr : layouts.pointerBits = 64)
    (hle : layouts.isLittleEndian = true)
    (hfields : ∀ idx flIdx, get? tl.fieldLayouts idx = some flIdx →
      ∃ fTl, layouts.lookup flIdx = some fTl ∧
        fTl.isUninhabited = false ∧
        ValidScalarBytes fTl.size.bytes ∧
        fTl.size.bytes ≤ S ∧
        (∀ prim vr, fTl.backendRepr = .scalar (.initialized prim vr) →
          vr.start = 0 ∧ vr.end_ + 1 = scalarModulus fTl.size.bytes)) :
    WellTypedUnionTy layouts uTy S where
  size_valid := hsz
  fields_union := hfu
  size_eq := hsize
  sized := hsized
  align_le := halign
  adt_spec := by
    refine ⟨defPath, args, tl, n, hkind, hidx_pos, hidx_lt, hlook, htl_fields, htl_var,
      htl_uninh, htl_sz, htl_len, hptr, hle, ?_⟩
    intro idx flIdx hget
    obtain ⟨fTl, hfTl, huninh, hfSz, hfLe, hfull⟩ := hfields idx flIdx hget
    refine ⟨fTl, hfTl, huninh, hfSz, hfLe, ?_⟩
    intro fTy sc msc _ himm hsc_sz fuel'
    cases himm with
    | scalar _ _ hrel _ _ _ =>
      have hcan := hrel.canonical
      rcases sc with ⟨bits, sz⟩
      dsimp only at hsc_sz hcan
      have hlookup : LayoutTable.lookup layouts flIdx = some fTl := hfTl
      unfold encodeByLayoutIdxAux
      rw [hlookup]
      rcases fTl with ⟨fSize, fAlign, fRepr, fFields, fVariants, fUninh, fLays⟩
      dsimp only at huninh hfSz hfull hsc_sz ⊢
      subst huninh hsc_sz
      dsimp only []
      have hble1 : Nat.ble 1 fSize.bytes = true := by
        rcases hfSz with h1 | h1 | h1 | h1 | h1 <;> rw [h1] <;> rfl
      have hbeqSz : Nat.beq fSize.bytes fSize.bytes = true := Nat.beq_refl fSize.bytes
      rw [hble1]
      dsimp only []
      rw [hbeqSz]
      dsimp only []
      cases fRepr with
      | memory => rfl
      | scalarPair _ _ => rfl
      | scalar sl =>
        cases sl with
        | union _ => rfl
        | initialized prim vr =>
          obtain ⟨hvs, hve⟩ := hfull prim vr rfl
          have hbits_le : bits ≤ vr.end_ := by omega
          have hse : Nat.ble vr.start vr.end_ = true := Nat.ble_eq.mpr (by omega)
          have hsv : Nat.ble vr.start bits = true := Nat.ble_eq.mpr (by omega)
          have hve_b : Nat.ble bits vr.end_ = true := Nat.ble_eq.mpr hbits_le
          have hw : wrappingRangeContains vr bits = true := by
            unfold wrappingRangeContains
            simp [hse, hsv, hve_b]
          have hnot_char : Nat.beq vr.end_ 0x10FFFF = false := by
            rcases hfSz with h1 | h1 | h1 | h1 | h1
            · rw [h1] at hve; have : vr.end_ = 255 := by simpa [scalarModulus] using hve
              rw [this]; rfl
            · rw [h1] at hve; have : vr.end_ = 65535 := by simpa [scalarModulus] using hve
              rw [this]; rfl
            · rw [h1] at hve; have : vr.end_ = 4294967295 := by simpa [scalarModulus] using hve
              rw [this]; rfl
            · rw [h1] at hve
              have : vr.end_ = 18446744073709551615 := by simpa [scalarModulus] using hve
              rw [this]; rfl
            · rw [h1] at hve
              have : vr.end_ = 340282366920938463463374607431768211455 := by
                simpa [scalarModulus] using hve
              rw [this]; rfl
          dsimp only []
          rw [hw]
          simp [hvs, hnot_char]

/-- A memory-backed union local `mp` whose active scalar field (of type `f0Ty`)
holds `sc`: `mp` points at offset `0` of its own live allocation, which has `S`
bytes, is mutable, has no provenance, Tree Borrows extra, or native buffer, has
the union's alignment, initializes `[0, k)` and leaves `[k, S)` uninitialized
for `k = sc.sizeBytes ≤ S` (`IsUnionPrefixMask`), and stores the little-endian
encoding of `sc` in `[0, k)`. -/
inductive UnionMemRel (mach : AnnealMachine) (uTy : Ty) (layouts : LayoutTable) (S : Nat)
    (f0Ty : Ty) (sc : MirAst.ScalarInt) (mp : Miri.Interpreter.MemPlace AnnealProv) : Prop where
  | mk
      (allocId : Miri.Memory.AllocId)
      (tag : Miri.Memory.BorTag)
      (baseAddr : UInt64)
      (localAlloc :
        Miri.Memory.LocalAllocation
          AnnealProv
          (Option Miri.TreeBorrows.BorrowTree)
          Miri.Memory.MiriMemoryKind)
      (msc : Miri.Memory.ScalarInt)
      (ptr_prov : mp.ptr.provenance = some (.concrete allocId tag))
      (no_misalign : mp.misaligned = none)
      (thin_meta : mp.metadata = .none)
      (live_lookup : (allocId, localAlloc) ∈ mach.memory.live.toList)
      (base_lookup : mach.lookupBaseAddr allocId = some baseAddr)
      (ptr_addr_eq : mp.ptr.offset = Miri.ABI.Size.ofBytes baseAddr)
      (addr_no_overflow : baseAddr.toNat + S < 2 ^ 64)
      (alloc_size : localAlloc.allocation.byteSize = translateSizeBytes S)
      (alloc_len : localAlloc.allocation.len = S)
      (alloc_mut : localAlloc.allocation.mutability = .Mut)
      (alloc_prov : localAlloc.allocation.provenanceMap = Miri.Memory.ProvenanceMap.new)
      (alloc_align : localAlloc.allocation.align = (translateTy uTy layouts).layout.align.abi)
      (alloc_extra : localAlloc.allocation.extra = none)
      (alloc_native : localAlloc.allocation.nativeBuffer = none)
      (k_le : sc.sizeBytes ≤ S)
      (mask : IsUnionPrefixMask S sc.sizeBytes localAlloc.allocation.initializationMask)
      (sc_rel : ScalarRel sc msc)
      (f0_prim : IsPrimScalarTy f0Ty)
      (f0_imm : ImmediateRel f0Ty layouts (.scalar sc) (.scalar (.fromScalarInt msc)))
      (raw : (unionAllocRaw localAlloc.allocation).extract 0 sc.sizeBytes =
        allocLeBytes sc.bits sc.sizeBytes) :
      UnionMemRel mach uTy layouts S f0Ty sc mp

/-- Witness that typed slot `(j_low, sc_low)` and raw-byte overlay `mergedBytes`
form a well-typed `D13a` overlay union representation for byte image
`encodeLittleEndianBytes sc.bits sc.sizeBytes none ++ replicateUninitBytes (S - sc.sizeBytes)`. -/
structure UnionOverlaySlotSpec
    (layouts : LayoutTable) (uTy : Ty) (S n j_low : Nat)
    (sc sc_low : MirAst.ScalarInt) (mergedBytes : List AbstractByte) : Prop where
  j_lt : j_low < n
  low_lt : sc_low.sizeBytes < sc.sizeBytes
  field_typed :
    ∃ (fLowTy : Ty) (msc_low : Miri.Memory.ScalarInt) (fl : Miri.Interpreter.LocalLayout),
      IsPrimScalarTy fLowTy ∧
      ImmediateRel fLowTy layouts (.scalar sc_low) (.scalar (.fromScalarInt msc_low)) ∧
      unionFieldLayoutOf layouts (translateTy uTy layouts) j_low = some fl ∧
      fl.layout.size = (translateTy fLowTy layouts).layout.size
  low_prefix :
    ∃ highBytes,
      encodeLittleEndianBytes sc.bits sc.sizeBytes none =
        encodeLittleEndianBytes sc_low.bits sc_low.sizeBytes none ++ highBytes
  bytes_eq :
    mergedBytes =
      encodeLittleEndianBytes sc.bits sc.sizeBytes none ++
        replicateUninitBytes (S - sc.sizeBytes)

/-- `LocalRel` extended with initialized unions (`UnionMemRel`), covering both
plain single-active-field union values (`union`) and `D13a` raw-byte-overlay
union values produced by narrower projected field writes (`unionOverlay`). -/
inductive UnionLocalRel
    (mach : AnnealMachine)
    (decl : LocalDecl)
    (layouts : LayoutTable) :
    LocalSlot →
    Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout →
    Prop where
  /-- Any `LocalRel`-related pair. -/
  | base (slot : LocalSlot)
      (mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout) :
      LocalRel mach decl layouts slot mls →
      UnionLocalRel mach decl layouts slot mls
  /-- An initialized `n`-field union holding active field `f`'s (`f < n`) value `sc`. -/
  | union (S n f : Nat) (f0Ty : Ty) (sc : MirAst.ScalarInt)
      (mp : Miri.Interpreter.MemPlace AnnealProv)
      (cachedLayout : Option Miri.Interpreter.LocalLayout) :
      (∀ l ∈ cachedLayout, l = translateTy decl.ty layouts) →
      WellTypedUnionTy layouts decl.ty S →
      (translateTy decl.ty layouts).layout.fields = .Union n →
      f < n →
      UnionMemRel mach decl.ty layouts S f0Ty sc mp →
      UnionLocalRel mach decl layouts
        (.init (.aggregate 0 (unionSlotFields n f (.scalar sc))))
        ⟨.live (.indirect mp), cachedLayout⟩
  /-- An initialized `n`-field union carrying a `D13a` raw-byte overlay after a
  narrower projected scalar field write `_u.j = sc_low` (`sc_low.sizeBytes < sc.sizeBytes ≤ S`),
  whose initialized `[0, sc.sizeBytes)` prefix represents `sc` (`UnionMemRel`). -/
  | unionOverlay (S n j : Nat) (f0Ty : Ty) (sc sc_low : MirAst.ScalarInt)
      (mergedBytes : List AbstractByte)
      (mp : Miri.Interpreter.MemPlace AnnealProv)
      (cachedLayout : Option Miri.Interpreter.LocalLayout) :
      (∀ l ∈ cachedLayout, l = translateTy decl.ty layouts) →
      WellTypedUnionTy layouts decl.ty S →
      (translateTy decl.ty layouts).layout.fields = .Union n →
      UnionOverlaySlotSpec layouts decl.ty S n j sc sc_low mergedBytes →
      UnionMemRel mach decl.ty layouts S f0Ty sc mp →
      UnionLocalRel mach decl layouts
        (.init (.aggregate 0
          (unionSlotFields n j (.scalar sc_low) ++
            [.aggregate 0 (encodeRawAbstractByteVals mergedBytes)])))
        ⟨.live (.indirect mp), cachedLayout⟩

/-- `FrameRel` with `UnionLocalRel` in place of `LocalRel`. -/
structure FrameRelLM2_4
    (body : CapturedMir)
    (mach : AnnealMachine)
    (af : StackFrame)
    (mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit) : Prop where
  body_eq : mf.body = translateBody body
  location_eq : mf.location = .mir ⟨af.blockIdx, af.stmtIdx⟩
  af_locals_len : af.locals.length = body.localDecls.length
  mf_locals_size : mf.locals.size = body.localDecls.length
  locals_rel :
    ∀ (i : Nat) (decl : LocalDecl) (slot : LocalSlot)
      (mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout),
      get? body.localDecls i = some decl →
      get? af.locals i = some slot →
      mf.locals[i]? = some mls →
      UnionLocalRel mach decl body.layouts slot mls

/-- `StateRel` with `FrameRelLM2_4` in place of `FrameRel`. -/
inductive StateRelLM2_4
    (body : CapturedMir)
    (s : MachineState)
    (m : AnnealStepState) : Prop where
  | mk
      (topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
      (frames_eq : m.stack.frames = #[topFrame])
      (returnContinuation_eq : topFrame.returnContinuation = .stop false)
      (returnPlace_eq :
        ∃ retLay,
          topFrame.returnPlace =
            .frameLocal 0 0 none retLay topFrame.localsIdentity)
      (frame_rel : FrameRelLM2_4 body m.machine s.frame topFrame)
      (activeCallee_none : s.memory.activeCallee = none)
      (callStack_nil : s.memory.callStack = .nil)
      (borrows_nil : s.memory.borrows = .nil)
      (activeProtectors_nil : s.memory.activeProtectors = .nil)
      (callerLocals_nil : s.memory.callerLocals = .nil)
      (memoryAllocDisjoint : MemoryAllocDisjoint topFrame) :
      StateRelLM2_4 body s m

/-- Every `StateRel` is a `StateRelLM2_4`. -/
theorem StateRel.toLM2_4 {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (h : StateRel body s m) : StateRelLM2_4 body s m := by
  rcases h with ⟨tf, hf, hrc, hrp, hfr, hcal, hst, hbor, hprot, hcaller, hdisj⟩
  exact ⟨tf, hf, hrc, hrp,
    ⟨hfr.body_eq, hfr.location_eq, hfr.af_locals_len, hfr.mf_locals_size,
      fun i d sl ml hd hs hm => .base sl ml (hfr.locals_rel i d sl ml hd hs hm)⟩,
    hcal, hst, hbor, hprot, hcaller, hdisj⟩

/-- A `StateRelLM2_4` in which every local is `LocalRel`-related is a
`StateRel`. -/
theorem StateRelLM2_4.toStateRel {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (h : StateRelLM2_4 body s m)
    (hbase : ∀ topFrame, m.stack.frames = #[topFrame] →
      ∀ (i : Nat) (decl : LocalDecl) (slot : LocalSlot)
        (mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout),
        get? body.localDecls i = some decl →
        get? s.frame.locals i = some slot →
        topFrame.locals[i]? = some mls →
        LocalRel m.machine decl body.layouts slot mls) :
    StateRel body s m := by
  rcases h with ⟨tf, hf, hrc, hrp, hfr, hcal, hst, hbor, hprot, hcaller, hdisj⟩
  exact ⟨tf, hf, hrc, hrp,
    ⟨hfr.body_eq, hfr.location_eq, hfr.af_locals_len, hfr.mf_locals_size,
      fun i d sl ml hd hs hm => hbase tf hf i d sl ml hd hs hm⟩,
    hcal, hst, hbor, hprot, hcaller, hdisj⟩

/-- `StepRel` with `StateRelLM2_4` in place of `StateRel`: both machines take a
normal step to related states, or both report undefined behavior. -/
inductive StepRelLM2_4 (body : CapturedMir) (m : AnnealStepState) :
    MirStepNode →
    Miri.Interpreter.StepResult AnnealStepState Bool →
    Prop where
  | step (s' : MachineState) (m' : AnnealStepState) :
      StateRelLM2_4 body s' m' →
      StepRelLM2_4 body m (MirStepNode.step s') (m', .ok true)
  | ub (m' : AnnealStepState) (msg : String) :
      StepRelLM2_4 body m (MirStepNode.fail .ub) (m', .error (.undefinedBehavior msg))

/-! ## 10. Padded Union with `[(); N]` ZST Array Arm (`kani#5176` / `kani#5159`)

When a `#[repr(C)] union` has a zero-sized `[(); N]` array arm (`N > 0`) alongside
a larger payload arm of size `S ∈ {1, 2, 4, 8, 16}`:
* Constructing or writing the `[(); N]` ZST arm (`_u = PU { z: [(); N] }` or
  `_u.z = [(); N]`) into an uninitialized union activates a 0-byte arm whose
  Anneal representation is `.init (.aggregate 0 (List.replicate n .unit))`
  (`unionActiveSlotIsZstPlaceholder = true`) with byte image `replicateUninitBytes S`
  (all `S` bytes `.uninit`), while `lean-miri` allocates an `S`-byte stack
  allocation with `InitMask.new (translateSizeBytes S) false`
  (`PaddedZstUnionUninitMemRel`).
* Overwriting an already-initialized union (holding scalar `sc` of width
  `k = sc.sizeBytes ≤ S`) with `_u.z = [(); N]` (`0` bytes) sets the typed
  slots to `List.replicate n .unit` and attaches the `D13a` raw-byte overlay
  retaining `[0, k)` initialized and `[k, S)` uninitialized in Anneal, while a
  0-byte `annealMemCopyOp` in `lean-miri` preserves `UnionMemRel` in place.
* Whole-union copies and moves (`_w = copy _u`, `_w = move _u`) of a ZST-initialized
  union preserve `InitMask.new (translateSizeBytes S) false` in `lean-miri`
  (`union_copy_uninit_alloc_spec`) and `.init (.aggregate 0 (List.replicate n .unit))`
  in Anneal.
* Reading the inhabited `[(); N]` ZST arm (`_r = copy _u.z`) or an in-bounds
  element (`_r = copy _u.z[i]`, `i < N`) succeeds on both all-uninit
  ZST-initialized unions and payload-initialized unions without reading any
  uninitialized padding bytes, whereas reading an out-of-bounds element (`i ≥ N`),
  an uninitialized scalar payload field (`w > 0`), or an uninhabited 0-byte field
  (`tyIsUninhabited = true`, `kani#5159`) is undefined behavior in both machines. -/

/-- The canonical Anneal value of `()` (`Value.unit`). -/
def zstUnitVal : Value := .unit

/-- The canonical Anneal value of `[(); N]`: `N` copies of `zstUnitVal`. -/
def zstArrayVal (N : Nat) : Value := .aggregate 0 (List.replicate N zstUnitVal)

/-- The `n`-slot all-`.unit` Anneal union field list produced when a union is
initialized via a zero-sized `[(); N]` placeholder arm (`unionActiveSlotIsZstPlaceholder`). -/
def unionAllUnitFields (n : Nat) : List Value := List.replicate n .unit

/-- A `#[repr(C)] union` of size `S ∈ {1, 2, 4, 8, 16}` with an inhabited
`[(); N]` ZST array arm at field `f_z < n` (layout index `zstFlIdx`). -/
structure WellTypedPaddedZstUnionTy
    (layouts : LayoutTable) (uTy : Ty) (S N f_z zstFlIdx : Nat) : Prop where
  size_valid : ValidScalarBytes S
  count_pos : 0 < N
  fields_union : ∃ n, (translateTy uTy layouts).layout.fields = .Union n ∧ f_z < n
  size_eq : (translateTy uTy layouts).layout.size = translateSizeBytes S
  sized : (translateTy uTy layouts).layout.isSized = true
  align_le : (translateTy uTy layouts).layout.align.abi.pow2 ≤ 29
  adt_spec : ∃ defPath args tl n zstTl,
    uTy.kind = .adt defPath args ∧
    0 < uTy.layoutIdx ∧
    uTy.layoutIdx < 900 ∧
    layouts.lookup uTy.layoutIdx = some tl ∧
    tl.fields = .union n ∧
    tl.variants = .single 0 ∧
    tl.isUninhabited = false ∧
    tl.size.bytes = S ∧
    tl.fieldLayouts.length = n ∧
    layouts.pointerBits = 64 ∧
    layouts.isLittleEndian = true ∧
    get? tl.fieldLayouts f_z = some zstFlIdx ∧
    0 < zstFlIdx ∧
    layouts.lookup zstFlIdx = some zstTl ∧
    zstTl.isUninhabited = false ∧
    zstTl.size.bytes = 0 ∧
    zstTl.fields = .array ⟨0⟩ N ∧
    zstTl.variants = .single 0 ∧
    zstTl.fieldLayouts = []

/-- A memory-backed `S`-byte union local `mp` initialized via a 0-byte ZST arm
(such as `[(); N]`): `mp` points at offset `0` of its own live mutable `S`-byte
stack allocation whose `initializationMask` is `InitMask.new (translateSizeBytes S) false`
(all `S` bytes uninitialized). -/
inductive PaddedZstUnionUninitMemRel
    (mach : AnnealMachine) (uTy : Ty) (layouts : LayoutTable) (S : Nat)
    (mp : Miri.Interpreter.MemPlace AnnealProv) : Prop where
  | mk
      (allocId : Miri.Memory.AllocId)
      (tag : Miri.Memory.BorTag)
      (baseAddr : UInt64)
      (localAlloc :
        Miri.Memory.LocalAllocation
          AnnealProv
          (Option Miri.TreeBorrows.BorrowTree)
          Miri.Memory.MiriMemoryKind)
      (ptr_prov : mp.ptr.provenance = some (.concrete allocId tag))
      (no_misalign : mp.misaligned = none)
      (thin_meta : mp.metadata = .none)
      (live_lookup : (allocId, localAlloc) ∈ mach.memory.live.toList)
      (base_lookup : mach.lookupBaseAddr allocId = some baseAddr)
      (ptr_addr_eq : mp.ptr.offset = Miri.ABI.Size.ofBytes baseAddr)
      (addr_no_overflow : baseAddr.toNat + S < 2 ^ 64)
      (alloc_size : localAlloc.allocation.byteSize = translateSizeBytes S)
      (alloc_len : localAlloc.allocation.len = S)
      (alloc_mut : localAlloc.allocation.mutability = .Mut)
      (alloc_prov : localAlloc.allocation.provenanceMap = Miri.Memory.ProvenanceMap.new)
      (alloc_align : localAlloc.allocation.align = (translateTy uTy layouts).layout.align.abi)
      (alloc_extra : localAlloc.allocation.extra = none)
      (alloc_native : localAlloc.allocation.nativeBuffer = none)
      (mask_uninit :
        localAlloc.allocation.initializationMask =
          Miri.Memory.InitMask.new (translateSizeBytes S) false) :
      PaddedZstUnionUninitMemRel mach uTy layouts S mp

theorem PaddedZstUnionUninitMemRel.of_live_base
    {mach mach' : AnnealMachine} {uTy : Ty} {layouts : LayoutTable} {S : Nat}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    (h : PaddedZstUnionUninitMemRel mach uTy layouts S mp)
    (hlive : ∀ a la, (a, la) ∈ mach.memory.live.toList → (a, la) ∈ mach'.memory.live.toList)
    (hbase : ∀ a b, mach.lookupBaseAddr a = some b → mach'.lookupBaseAddr a = some b) :
    PaddedZstUnionUninitMemRel mach' uTy layouts S mp := by
  cases h with
  | mk allocId tag baseAddr la hprov hmis hmeta hl hb hptr hovf hsz hlen hmut hp hal hex hnat hmask =>
    exact .mk allocId tag baseAddr la hprov hmis hmeta (hlive _ _ hl) (hbase _ _ hb)
      hptr hovf hsz hlen hmut hp hal hex hnat hmask

/-- Any scalar read of width `w ∈ {1, 2, 4, 8, 16}` (`w ≤ S`) from an all-uninit
ZST-initialized union allocation (`PaddedZstUnionUninitMemRel`) encounters an
uninitialized byte at offset `0` and fails with `AllocError.invalidUninitBytes`. -/
theorem PaddedZstUnionUninitMemRel.readScalar_uninit_error
    {mach : AnnealMachine} {uTy : Ty} {layouts : LayoutTable} {S w : Nat}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hS : ValidScalarBytes S) (hw : ValidScalarBytes w) (hwS : w ≤ S)
    (hmem : PaddedZstUnionUninitMemRel mach uTy layouts S mp) :
    ∃ allocId tag localAlloc badRange,
      mp.ptr.provenance = some (.concrete allocId tag) ∧
      (allocId, localAlloc) ∈ mach.memory.live.toList ∧
      localAlloc.allocation.readScalar annealTargetDataLayout
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes w)) false =
          .error (.invalidUninitBytes badRange) := by
  cases hmem with
  | mk allocId tag baseAddr la hprov _ _ hlive _ _ _ hsz hlen _ _ _ _ _ hmask =>
    have hbad : la.allocation.initializationMask.isRangeInitialized
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes w)) =
        .ok (.error (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes w))) := by
      rw [hmask]
      rcases hS with rfl | rfl | rfl | rfl | rfl <;>
        rcases hw with rfl | rfl | rfl | rfl | rfl <;>
        (try omega) <;>
        rfl
    exact ⟨allocId, tag, la, _, hprov, hlive, union_readScalar_uninit hbad⟩

/-- A 0-byte memory-backed ZST place `mp` (such as a `[(); N]` local): `mp`
points at offset `0` of a live mutable 0-byte allocation (`byteSize = Size.ZERO`,
`len = 0`). -/
inductive ZstZeroMemRel
    (mach : AnnealMachine)
    (mp : Miri.Interpreter.MemPlace AnnealProv) : Prop where
  | mk
      (allocId : Miri.Memory.AllocId)
      (tag : Miri.Memory.BorTag)
      (baseAddr : UInt64)
      (localAlloc :
        Miri.Memory.LocalAllocation
          AnnealProv
          (Option Miri.TreeBorrows.BorrowTree)
          Miri.Memory.MiriMemoryKind)
      (ptr_prov : mp.ptr.provenance = some (.concrete allocId tag))
      (no_misalign : mp.misaligned = none)
      (thin_meta : mp.metadata = .none)
      (live_lookup : (allocId, localAlloc) ∈ mach.memory.live.toList)
      (base_lookup : mach.lookupBaseAddr allocId = some baseAddr)
      (ptr_addr_eq : mp.ptr.offset = Miri.ABI.Size.ofBytes baseAddr)
      (alloc_size : localAlloc.allocation.byteSize = Miri.ABI.Size.ZERO)
      (alloc_len : localAlloc.allocation.len = 0)
      (alloc_mut : localAlloc.allocation.mutability = .Mut) :
      ZstZeroMemRel mach mp

/-- Extended local relation covering `UnionLocalRel` plus padded unions whose
active arm is a 0-byte `[(); N]` ZST array (`zstUninit` on all-uninit storage,
`zstOverlay` when `[(); N]` overwrote a scalar-initialized union), pre-allocated
uninitialized unions (`uninitIndirect`), and initialized 0-byte `[(); N]` ZST
array locals (`zstArrayIndirect`).

Model boundary notes (`R-b`, `R-c`):
* **`zstArrayIndirect` (`R-c`)**: relates only an initialized Anneal slot
  `.init (zstArrayVal N)` to a live 0-byte `ZstZeroMemRel` allocation
  `⟨.live (.indirect mp), cachedLayout⟩`, so reading that `[(); N]` local
  succeeds in both Anneal and `lean-miri` (whereas an `.uninit` `[(); N]` local
  is represented via `ofUnionLocalRel (.base (.immediate .uninit .uninit ..))`
  and faults in both).
* **Never-written (`.uninit`) union 0-byte field reads (`R-b`)**: in rustc's
  interpreter / Miri (and MiniRust's `evalValue_load_union_zstArray_field`),
  `StorageLive` allocates `S` uninitialized bytes in memory and reading an
  inhabited 0-byte ZST arm succeeds even before any write to the union. By
  contrast, Anneal's `MirSemantics.evalOperand` requires `LocalSlot.init` before
  `readProjectedValueUnionAware`, and `lean-miri`'s `annealEvalUnionField` /
  `annealEvalOperandLM2_4PaddedZst` likewise faults on `.immediate .uninit`
  (as produced by `StorageLive`). Under `uninitIndirect` (a pre-allocated
  write/copy destination where Anneal holds `.uninit` and `lean-miri` already
  holds `.indirect mp`), `lean-miri` matches real Miri by accepting a 0-byte
  inhabited field read while Anneal faults on `LocalSlot.uninit`; once a ZST arm
  initializes the union (`zstUninit`), all `S` backing bytes remain `.uninit`
  and both Anneal and `lean-miri` accept inhabited 0-byte reads. -/
inductive PaddedZstUnionLocalRel
    (mach : AnnealMachine)
    (decl : LocalDecl)
    (layouts : LayoutTable) :
    LocalSlot →
    Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout →
    Prop where
  | ofUnionLocalRel (slot : LocalSlot)
      (mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout) :
      UnionLocalRel mach decl layouts slot mls →
      PaddedZstUnionLocalRel mach decl layouts slot mls
  | uninitIndirect (S n N f_z zstFlIdx : Nat)
      (mp : Miri.Interpreter.MemPlace AnnealProv)
      (cachedLayout : Option Miri.Interpreter.LocalLayout) :
      (∀ l ∈ cachedLayout, l = translateTy decl.ty layouts) →
      WellTypedPaddedZstUnionTy layouts decl.ty S N f_z zstFlIdx →
      (translateTy decl.ty layouts).layout.fields = .Union n →
      PaddedZstUnionUninitMemRel mach decl.ty layouts S mp →
      PaddedZstUnionLocalRel mach decl layouts
        .uninit
        ⟨.live (.indirect mp), cachedLayout⟩
  | zstArrayIndirect (N : Nat)
      (mp : Miri.Interpreter.MemPlace AnnealProv)
      (cachedLayout : Option Miri.Interpreter.LocalLayout) :
      (∀ l ∈ cachedLayout, l = translateTy decl.ty layouts) →
      decl.ty.kind = .array (.tuple []) N →
      (translateTy decl.ty layouts).layout.size = Miri.ABI.Size.ZERO →
      ZstZeroMemRel mach mp →
      PaddedZstUnionLocalRel mach decl layouts
        (.init (zstArrayVal N))
        ⟨.live (.indirect mp), cachedLayout⟩
  | zstUninit (S n N f_z zstFlIdx : Nat)
      (mp : Miri.Interpreter.MemPlace AnnealProv)
      (cachedLayout : Option Miri.Interpreter.LocalLayout) :
      (∀ l ∈ cachedLayout, l = translateTy decl.ty layouts) →
      WellTypedPaddedZstUnionTy layouts decl.ty S N f_z zstFlIdx →
      (translateTy decl.ty layouts).layout.fields = .Union n →
      PaddedZstUnionUninitMemRel mach decl.ty layouts S mp →
      PaddedZstUnionLocalRel mach decl layouts
        (.init (.aggregate 0 (List.replicate n .unit)))
        ⟨.live (.indirect mp), cachedLayout⟩
  | zstOverlay (S n N f_z zstFlIdx : Nat) (f0Ty : Ty) (sc : MirAst.ScalarInt)
      (mp : Miri.Interpreter.MemPlace AnnealProv)
      (cachedLayout : Option Miri.Interpreter.LocalLayout) :
      (∀ l ∈ cachedLayout, l = translateTy decl.ty layouts) →
      WellTypedPaddedZstUnionTy layouts decl.ty S N f_z zstFlIdx →
      (translateTy decl.ty layouts).layout.fields = .Union n →
      UnionMemRel mach decl.ty layouts S f0Ty sc mp →
      PaddedZstUnionLocalRel mach decl layouts
        (.init (.aggregate 0
          (List.replicate n .unit ++
            [.aggregate 0
              (encodeRawAbstractByteVals
                (encodeLittleEndianBytes sc.bits sc.sizeBytes none ++
                  replicateUninitBytes (S - sc.sizeBytes)))])))
        ⟨.live (.indirect mp), cachedLayout⟩

/-- `FrameRelLM2_4` extended with `PaddedZstUnionLocalRel`. -/
structure FrameRelLM2_4PaddedZst
    (body : CapturedMir)
    (mach : AnnealMachine)
    (af : StackFrame)
    (mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit) : Prop where
  body_eq : mf.body = translateBody body
  location_eq : mf.location = .mir ⟨af.blockIdx, af.stmtIdx⟩
  af_locals_len : af.locals.length = body.localDecls.length
  mf_locals_size : mf.locals.size = body.localDecls.length
  locals_rel :
    ∀ (i : Nat) (decl : LocalDecl) (slot : LocalSlot)
      (mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout),
      get? body.localDecls i = some decl →
      get? af.locals i = some slot →
      mf.locals[i]? = some mls →
      PaddedZstUnionLocalRel mach decl body.layouts slot mls

/-- `StateRelLM2_4` extended with `FrameRelLM2_4PaddedZst`. -/
inductive StateRelLM2_4PaddedZst
    (body : CapturedMir)
    (s : MachineState)
    (m : AnnealStepState) : Prop where
  | mk
      (topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
      (frames_eq : m.stack.frames = #[topFrame])
      (returnContinuation_eq : topFrame.returnContinuation = .stop false)
      (returnPlace_eq :
        ∃ retLay,
          topFrame.returnPlace =
            .frameLocal 0 0 none retLay topFrame.localsIdentity)
      (frame_rel : FrameRelLM2_4PaddedZst body m.machine s.frame topFrame)
      (activeCallee_none : s.memory.activeCallee = none)
      (callStack_nil : s.memory.callStack = .nil)
      (borrows_nil : s.memory.borrows = .nil)
      (activeProtectors_nil : s.memory.activeProtectors = .nil)
      (callerLocals_nil : s.memory.callerLocals = .nil)
      (memoryAllocDisjoint : MemoryAllocDisjoint topFrame) :
      StateRelLM2_4PaddedZst body s m

/-- Every `StateRelLM2_4` embeds into `StateRelLM2_4PaddedZst`. -/
theorem StateRelLM2_4.toPaddedZst {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (h : StateRelLM2_4 body s m) : StateRelLM2_4PaddedZst body s m := by
  rcases h with ⟨tf, hf, hrc, hrp, hfr, hcal, hst, hbor, hprot, hcaller, hdisj⟩
  exact ⟨tf, hf, hrc, hrp,
    ⟨hfr.body_eq, hfr.location_eq, hfr.af_locals_len, hfr.mf_locals_size,
      fun i d sl ml hd hs hm => .ofUnionLocalRel sl ml (hfr.locals_rel i d sl ml hd hs hm)⟩,
    hcal, hst, hbor, hprot, hcaller, hdisj⟩

/-- Every `StateRel` embeds into `StateRelLM2_4PaddedZst`. -/
theorem StateRel.toPaddedZst {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (h : StateRel body s m) : StateRelLM2_4PaddedZst body s m :=
  h.toLM2_4.toPaddedZst

/-- `StepRelLM2_4` extended with `StateRelLM2_4PaddedZst`. -/
inductive StepRelLM2_4PaddedZst (body : CapturedMir) (m : AnnealStepState) :
    MirStepNode →
    Miri.Interpreter.StepResult AnnealStepState Bool →
    Prop where
  | step (s' : MachineState) (m' : AnnealStepState) :
      StateRelLM2_4PaddedZst body s' m' →
      StepRelLM2_4PaddedZst body m (MirStepNode.step s') (m', .ok true)
  | ub (m' : AnnealStepState) (msg : String) :
      StepRelLM2_4PaddedZst body m (MirStepNode.fail .ub) (m', .error (.undefinedBehavior msg))

theorem StepRelLM2_4.toPaddedZst {body : CapturedMir} {m : AnnealStepState}
    {node : MirStepNode} {res : Miri.Interpreter.StepResult AnnealStepState Bool}
    (h : StepRelLM2_4 body m node res) : StepRelLM2_4PaddedZst body m node res := by
  cases h with
  | step s' m' hst => exact .step s' m' hst.toPaddedZst
  | ub m' msg => exact .ub m' msg

/-- For any `N > 0`, `zstArrayVal N` (`[(); N]`) lacks a layout-free byte image
(`unionSlotLacksLayoutFreeImage = true`), so when its field/operand type is
statically zero-sized (`tyByteSize = some 0`), `unionActiveSlotIsZstPlaceholder`
returns `true` (`kani#5176`). -/
theorem unionActiveSlotIsZstPlaceholder_zstArrayVal
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    {N : Nat} (hN : 0 < N) {zstArrTy : Ty}
    (hsz : tyByteSize localDecls layouts (resolveTyWithLocalDecls localDecls layouts zstArrTy) = some 0)
    (fls : List Nat := []) :
    unionActiveSlotIsZstPlaceholder localDecls layouts (some zstArrTy) (zstArrayVal N) fls = true := by
  cases N with
  | zero => exact absurd hN (Nat.lt_irrefl 0)
  | succ k =>
    have hlacks : unionSlotLacksLayoutFreeImage layouts (zstArrayVal (k + 1)) = true := rfl
    unfold unionActiveSlotIsZstPlaceholder
    rw [hlacks]
    dsimp only
    rw [hsz]
    rfl

/-- Merging `k` `.unit` slots in `mergeUnionTypedSlotsAux` leaves `(buf, bufMask)`
unchanged. -/
theorem mergeUnionTypedSlotsAux_allUnits
    (layouts : LayoutTable)
    (encodeSlot : Nat → Value → Option (List AbstractByte))
    (fallbackLayoutIdx : Nat) (hasOverlay : Bool) (unionSize : Nat) :
    ∀ (k : Nat) (flIdxs : List Nat) (buf : List AbstractByte) (bufMask : List Bool),
      mergeUnionTypedSlotsAux layouts encodeSlot fallbackLayoutIdx hasOverlay unionSize
        flIdxs (List.replicate k .unit) buf bufMask = some buf
  | 0, _, buf, _ => rfl
  | k + 1, [], buf, bufMask => by
    simp only [List.replicate_succ, mergeUnionTypedSlotsAux]
    exact mergeUnionTypedSlotsAux_allUnits layouts encodeSlot fallbackLayoutIdx hasOverlay
      unionSize k [] buf bufMask
  | k + 1, _ :: flRest, buf, bufMask => by
    simp only [List.replicate_succ, mergeUnionTypedSlotsAux]
    exact mergeUnionTypedSlotsAux_allUnits layouts encodeSlot fallbackLayoutIdx hasOverlay
      unionSize k flRest buf bufMask

/-- Encoding an `n`-slot all-`.unit` union value `.aggregate 0 (List.replicate n .unit)`
at a well-typed padded ZST union layout (`WellTypedPaddedZstUnionTy`) produces
`some (replicateUninitBytes S)` (all `S` bytes `.uninit`). -/
theorem encodeByLayoutIdxAux_union_allUnits
    {layouts : LayoutTable} {uTy : Ty} {S N f_z zstFlIdx : Nat}
    (hwt : WellTypedPaddedZstUnionTy layouts uTy S N f_z zstFlIdx)
    {n : Nat} (hfields_u : (translateTy uTy layouts).layout.fields = .Union n)
    (fuel : Nat) :
    encodeByLayoutIdxAux (fuel + 1) layouts uTy.layoutIdx
      (.aggregate 0 (List.replicate n .unit)) = some (replicateUninitBytes S) := by
  obtain ⟨_, _, tl, n', _, hk, _, _, hlookup, hfu, _, huninh, htl_sz, hfl_len, _, _,
    hgf, _, _, _, _, _, _, _⟩ := hwt.adt_spec
  have hn_eq : n' = n := by
    unfold translateTy at hfields_u
    dsimp only at hfields_u
    rw [hk, hlookup] at hfields_u
    dsimp only [translateTypeLayout, translateFieldsShape] at hfields_u
    rw [hfu] at hfields_u
    cases hfields_u
    rfl
  subst hn_eq
  have hfls_ne : ∃ a as, tl.fieldLayouts = a :: as := by
    cases h : tl.fieldLayouts with
    | nil => rw [h] at hgf; cases hgf
    | cons a as => exact ⟨a, as, rfl⟩
  obtain ⟨a, as, hfls_eq⟩ := hfls_ne
  have hsplit : ∀ k : Nat,
      splitUnionTypedAndOverlay k (List.replicate k .unit) =
        some (List.replicate k .unit, none) := by
    intro k
    induction k with
    | zero => rfl
    | succ k' ih =>
      simp only [List.replicate_succ, splitUnionTypedAndOverlay, ih]
  unfold encodeByLayoutIdxAux encodeUnionSlotsIntoBufAux
  dsimp only
  rw [hlookup]
  dsimp only
  rw [huninh, hfu]
  dsimp only
  rw [hsplit n']
  dsimp only
  rw [hfls_eq]
  dsimp only
  rw [← hfls_eq, htl_sz]
  exact mergeUnionTypedSlotsAux_allUnits layouts _ _ false S n' tl.fieldLayouts
    (replicateUninitBytes S) (replicateBool S false)

/-- Reading a zero-sized `zstLayoutData` field from any live memory-backed union
operand `⟨.indirect mp, { ty := tyId, layout := zstLayoutData }⟩` via
`annealReadImmediateLM2_2` succeeds immediately with `Immediate.uninit` without
inspecting `mp`'s allocation bytes or initialization mask. -/
theorem annealReadImmediate_zstLayoutData
    {m : AnnealStepState} (hnodup : LiveAllocsNodup m.machine)
    {mp : Miri.Interpreter.MemPlace AnnealProv} {tyId : Miri.MIR.TyId}
    {allocId : Miri.Memory.AllocId} {tag : Miri.Memory.BorTag} {baseAddr : UInt64}
    {la : Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
      Miri.Memory.MiriMemoryKind}
    (hprov : mp.ptr.provenance = some (.concrete allocId tag))
    (hlive : (allocId, la) ∈ m.machine.memory.live.toList)
    (hbase : m.machine.lookupBaseAddr allocId = some baseAddr) :
    annealReadImmediateLM2_2 ⟨.indirect mp, { ty := tyId, layout := zstLayoutData }⟩ m =
      .ok ⟨.uninit, { ty := tyId, layout := zstLayoutData }⟩ m := by
  have hfind := array_find?_of_nodup_fst hnodup hlive
  rcases la with ⟨kind, alloc⟩
  unfold annealReadImmediateLM2_2 annealReadIndirectImmediate
  dsimp only [zstLayoutData]
  rw [hprov]
  dsimp only [Option.bind, Miri.Memory.Provenance.getAllocId, get, getThe, MonadStateOf.get,
    EStateM.get, bind, EStateM.bind]
  rw [hbase, hfind]
  rfl

/-- Writing a zero-sized source operand `⟨.indirect zMp, zLay⟩`
(`zLay.layout.size = Miri.ABI.Size.ZERO`) into a memory-backed union field place
`⟨.memory mp, fLay⟩` (`fLay.layout.size = Miri.ABI.Size.ZERO`) via
`annealMemCopyOp` when `mp` points to a live mutable `S`-byte allocation (`ValidScalarBytes S`,
either `PaddedZstUnionUninitMemRel` or `UnionMemRel`) succeeds as a no-op
(`.ok () m`), leaving `m`'s stack and memory state unchanged. -/
theorem annealMemCopyOp_zero_into_union_field
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    {m : AnnealStepState} (hnodup : LiveAllocsNodup m.machine)
    {S : Nat} (hS : ValidScalarBytes S)
    {mp zMp : Miri.Interpreter.MemPlace AnnealProv}
    {allocId srcAllocId : Miri.Memory.AllocId} {tag srcTag : Miri.Memory.BorTag}
    {baseAddr srcBaseAddr : UInt64}
    {la srcLa : Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
      Miri.Memory.MiriMemoryKind}
    (hprov : mp.ptr.provenance = some (.concrete allocId tag))
    (hlive : (allocId, la) ∈ m.machine.memory.live.toList)
    (hbase : m.machine.lookupBaseAddr allocId = some baseAddr)
    (hptr : mp.ptr.offset = Miri.ABI.Size.ofBytes baseAddr)
    (hsz : la.allocation.byteSize = translateSizeBytes S)
    (hlen : la.allocation.len = S)
    (hmut : la.allocation.mutability = .Mut)
    (hprov_src : zMp.ptr.provenance = some (.concrete srcAllocId srcTag))
    (hlive_src : (srcAllocId, srcLa) ∈ m.machine.memory.live.toList)
    (hbase_src : m.machine.lookupBaseAddr srcAllocId = some srcBaseAddr)
    (hptr_src : zMp.ptr.offset = Miri.ABI.Size.ofBytes srcBaseAddr)
    (hlen_src : srcLa.allocation.len = srcLa.allocation.byteSize.bytes.toNat)
    {zLay fLay : Miri.Interpreter.LocalLayout}
    (hf0 : fLay.layout.size = Miri.ABI.Size.ZERO) :
    annealMemCopyOp localDecls layouts ⟨.indirect zMp, zLay⟩ ⟨.memory mp, fLay⟩ m =
      .ok () m := by
  have hfind_src := array_find?_of_nodup_fst hnodup hlive_src
  obtain ⟨destIdx, _, hidx_dst, hget_dst, _⟩ := array_findIdx?_of_nodup_fst hnodup hlive
  have hrel_src : Miri.ABI.Size.ofBytes (zMp.ptr.offset.bytes - srcBaseAddr) = Miri.ABI.Size.ZERO := by
    have hb : zMp.ptr.offset.bytes = srcBaseAddr := by rw [hptr_src]; rfl
    rw [hb, UInt64.sub_self]; rfl
  have hrel_dst : Miri.ABI.Size.ofBytes (mp.ptr.offset.bytes - baseAddr) = Miri.ABI.Size.ZERO := by
    have hb : mp.ptr.offset.bytes = baseAddr := by rw [hptr]; rfl
    rw [hb, UInt64.sub_self]; rfl
  have hlen_dst_nat : la.allocation.len = la.allocation.byteSize.bytes.toNat := by
    rw [hlen, hsz, translateSizeBytes_toNat_of_valid hS]
  have hslice_src := getBytesUnchecked_at (A := srcLa.allocation) Miri.ABI.Size.ZERO Miri.ABI.Size.ZERO
    hlen_src (Nat.zero_le _)
  have hslice_dst := getBytesUnchecked_at (A := la.allocation) Miri.ABI.Size.ZERO Miri.ABI.Size.ZERO
    hlen_dst_nat (Nat.zero_le _)
  have hnz : (la.allocation.byteSize.bytes == 0) = false := by
    rw [hsz]
    rcases hS with rfl | rfl | rfl | rfl | rfl <;> rfl
  have h0 : (Miri.ABI.Size.ZERO.bytes == 0) = true := rfl
  have hforce : annealForceUnionAllocation localDecls layouts ⟨.memory mp, fLay⟩ m =
      .ok ⟨mp, fLay⟩ m := rfl
  rcases la with ⟨kind_d, alloc_d⟩
  dsimp only at hsz hlen hmut hslice_dst hnz ⊢
  unfold annealMemCopyOp
  simp only [bind, EStateM.bind, hforce, get, getThe, MonadStateOf.get, EStateM.get,
    hprov_src, hprov, Option.bind, Miri.Memory.Provenance.getAllocId,
    hbase_src, hbase, hfind_src, hidx_dst, hget_dst, hrel_src, hrel_dst, hf0,
    h0, ↓reduceIte, hslice_src, hslice_dst, hmut, bne_self_eq_false,
    Bool.false_eq_true, hnz, pure, EStateM.pure]

/-- Operand evaluation that extends `annealEvalOperandLM2_4` on two shapes of
union-local operands and agrees with it elsewhere
(`annealEvalOperandLM2_4PaddedZst_eq_of_not_unionLocal`):
1. A field read `[.Field j fty]` whose field type is uninhabited
   (`isUninhabitedEncodedTyId fty layouts = true`) is
   `.error (.undefinedBehavior "read of uninhabited union field")` (`kani#5159`).
   This changes a defined outcome of the pinned `annealEvalOperandLM2_4`, which
   copies the 0-byte field without validation and succeeds
   (`lm24_padded_zst_uninhabited_arm_base_adapter_accepts` in `WitLM2_4.lean`).
   rustc and Miri validate a typed copy, and the vendored validity visitor
   rejects a value of a type without variants ("zero-variant enum value",
   `Miri/Interpreter/ValidityVisitor.lean`); this hook performs that rejection
   for union field reads only, keyed on the encoded field type.
2. An element read `[.Field j fty, .ConstantIndex offset minLen false]` of a
   `[(); N]` arm, which `annealEvalOperandLM2_4` does not support, returns the
   union's place at the zero-sized `()` layout when `minLen ≤ N ∧ offset < N`,
   and `.error (.undefinedBehavior "out-of-bounds union ZST array index")`
   otherwise. rustc's interpreter also reports UB when `minLen > N`, but it
   asserts `offset < min_length` instead of reporting UB, and rustc only emits
   `ConstantIndex` with `offset < minLen`; a projection with `offset ≥ minLen`
   is ill-formed MIR. -/
def annealEvalOperandLM2_4PaddedZst
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (op : Miri.MIR.Operand)
    (expectedLayout : Option Miri.Interpreter.LocalLayout) :
    Miri.Interpreter.RvalueM AnnealStepState (Miri.Interpreter.OpTy AnnealProv) := do
  let place :=
    match op with
    | .Copy p | .Move p => some p
    | _ => none
  match place with
  | some p =>
    if isUnionLocal localDecls layouts p.localId then
      match p.projection.toList with
      | [.Field _ fty] =>
        if isUninhabitedEncodedTyId fty layouts then
          let st ← get
          if st.stack.currentFrame?.isNone then
            throw (.stack .emptyStack)
          let (frame', _) ← annealResolveAndCacheLocalLayout localDecls layouts p.localId none
          match frame'.getLocalOperand p.localId with
          | .error (.localExpectedLive _) => throw (.undefinedBehavior "read of dead local")
          | .error e => throw (.stack e)
          | .ok (.immediate .uninit) =>
            throw (.undefinedBehavior "field read of uninitialized union")
          | .ok (.immediate _) =>
            throw (.unsupported "union local held as an initialized immediate")
          | .ok (.indirect _) =>
            throw (.undefinedBehavior "read of uninhabited union field")
        else
          annealEvalOperandLM2_4 localDecls layouts op expectedLayout
      | [.Field j fty, .ConstantIndex offset minLen false] =>
        let st ← get
        if st.stack.currentFrame?.isNone then
          throw (.stack .emptyStack)
        let (frame', uLay) ← annealResolveAndCacheLocalLayout localDecls layouts p.localId none
        match frame'.getLocalOperand p.localId with
        | .error (.localExpectedLive _) => throw (.undefinedBehavior "read of dead local")
        | .error e => throw (.stack e)
        | .ok (.immediate .uninit) =>
          throw (.undefinedBehavior "field read of uninitialized union")
        | .ok (.immediate _) =>
          throw (.unsupported "union local held as an initialized immediate")
        | .ok (.indirect mp) =>
          match uLay.layout.fields with
          | .Union n =>
            if j < n then
              match unionZstArrayElemCount? layouts fty with
              | some arrLen =>
                if minLen ≤ arrLen && offset < arrLen then
                  pure ⟨.indirect mp,
                    { ty := encodeTyId { kind := .tuple [], layoutIdx := 0 },
                      layout := zstLayoutData }⟩
                else
                  throw (.undefinedBehavior "out-of-bounds union ZST array index")
              | none =>
                throw (.unsupported "non-ZST-array union ConstantIndex projection")
            else
              throw (.undefinedBehavior "out-of-bounds union field")
          | _ => throw (.unsupported "non-union local in union ConstantIndex branch")
      | _ => annealEvalOperandLM2_4 localDecls layouts op expectedLayout
    else
      annealEvalOperandLM2_4 localDecls layouts op expectedLayout
  | none =>
    annealEvalOperandLM2_4 localDecls layouts op expectedLayout
where
  /-- Whether an encoded field `TyId` (`encodeTyId`) is uninhabited: the never
  type (`50`), or a type encoded through its layout index (`100 + layoutIdx`)
  whose layout entry is uninhabited. Scalar types and arrays of scalars, the
  other encodings, are inhabited. -/
  isUninhabitedEncodedTyId (tyId : Miri.MIR.TyId) (layouts : LayoutTable) : Bool :=
    if tyId == 50 then true
    else if 100 ≤ tyId && tyId < 1000 then
      match layouts.lookup (tyId - 100) with
      | some tl => tl.isUninhabited
      | none => false
    else false
  /-- Extract `N` when `tyId` encodes `{ kind := .array (.tuple []) N, layoutIdx := zstFlIdx }`
  whose layout entry in `layouts` is a 0-byte inhabited `.array ⟨0⟩ N`. -/
  unionZstArrayElemCount? (layouts : LayoutTable) (tyId : Miri.MIR.TyId) : Option Nat :=
    if tyId ≥ 1000 && tyId % 100 == 51 then
      let flIdx := (tyId - 1000) / 100
      match layouts.lookup flIdx with
      | some tl =>
        if !tl.isUninhabited && tl.size.bytes == 0 then
          match tl.fields with
          | .array stride cnt => if stride.bytes == 0 then some cnt else none
          | _ => none
        else none
      | none => none
    else none

/-- `annealEvalOperandLM2_4PaddedZst` is `annealEvalOperandLM2_4` on every
operand that does not read a union local. -/
theorem annealEvalOperandLM2_4PaddedZst_eq_of_not_unionLocal
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (op : Miri.MIR.Operand) (expectedLayout : Option Miri.Interpreter.LocalLayout)
    (h : ∀ p, (op = .Copy p ∨ op = .Move p) → isUnionLocal localDecls layouts p.localId = false) :
    annealEvalOperandLM2_4PaddedZst localDecls layouts op expectedLayout =
      annealEvalOperandLM2_4 localDecls layouts op expectedLayout := by
  unfold annealEvalOperandLM2_4PaddedZst
  cases op with
  | Copy p => simp [h p (.inl rfl)]
  | Move p => simp [h p (.inr rfl)]
  | _ => rfl

/-- `annealEvalOperandLM2_4PaddedZst` is `annealEvalOperandLM2_4` on a
union-local operand whose projection is neither `[Field j fty]` nor
`[Field j fty, ConstantIndex ..]`. -/
theorem annealEvalOperandLM2_4PaddedZst_eq_of_projection
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (p : Miri.MIR.Place) (expectedLayout : Option Miri.Interpreter.LocalLayout)
    (hproj : ∀ j fty, p.projection.toList ≠ [.Field j fty])
    (hidx : ∀ j fty offset minLen,
      p.projection.toList ≠ [.Field j fty, .ConstantIndex offset minLen false]) :
    annealEvalOperandLM2_4PaddedZst localDecls layouts (.Copy p) expectedLayout =
        annealEvalOperandLM2_4 localDecls layouts (.Copy p) expectedLayout ∧
      annealEvalOperandLM2_4PaddedZst localDecls layouts (.Move p) expectedLayout =
        annealEvalOperandLM2_4 localDecls layouts (.Move p) expectedLayout := by
  unfold annealEvalOperandLM2_4PaddedZst
  constructor <;>
  · dsimp only
    split
    · split
      · rename_i j fty hp; exact absurd hp (hproj j fty)
      · rename_i j fty offset minLen hp; exact absurd hp (hidx j fty offset minLen)
      · rfl
    · rfl

/-- `annealEvalOperandLM2_4PaddedZst` is definitionally equal to
`annealEvalOperandLM2_4` on every inhabited `[Field j fty]` union field read
(`isUninhabitedEncodedTyId fty layouts = false`, `G4`). -/
theorem annealEvalOperandLM2_4PaddedZst_eq_of_inhabited_field
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (p : Miri.MIR.Place) (j : Nat) (fty : Miri.MIR.TyId)
    (expectedLayout : Option Miri.Interpreter.LocalLayout)
    (hproj : p.projection.toList = [.Field j fty])
    (hinh : annealEvalOperandLM2_4PaddedZst.isUninhabitedEncodedTyId fty layouts = false) :
    annealEvalOperandLM2_4PaddedZst localDecls layouts (.Copy p) expectedLayout =
        annealEvalOperandLM2_4 localDecls layouts (.Copy p) expectedLayout ∧
      annealEvalOperandLM2_4PaddedZst localDecls layouts (.Move p) expectedLayout =
        annealEvalOperandLM2_4 localDecls layouts (.Move p) expectedLayout := by
  unfold annealEvalOperandLM2_4PaddedZst
  constructor <;>
  · dsimp only
    split
    · rw [hproj]
      dsimp only
      rw [hinh]
      rfl
    · rfl

/-- Additive aggregate hooks extending `annealAggregateHooksLM2_4` so zero-sized
array operands (`src.layout.layout.size.bytes == 0`, such as `[(); N]` in
`_u = PU { z: op_zst }`) succeed as a 0-byte copy into indirect union field
destinations instead of failing `annealReadImmediateLM2_2`'s `.Arbitrary #[] #[]` check. -/
def annealAggregateHooksLM2_4PaddedZst
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    Miri.Interpreter.AggregateHooks
      AnnealProv
      AnnealStepState
      Unit
      (Miri.Interpreter.RuntimePlace AnnealProv) :=
  let base := annealAggregateHooksLM2_4 localDecls layouts
  { base with
    evalOperand := fun _ op known => do
      let opTy ← annealEvalOperandLM2_4PaddedZst localDecls layouts op known
      if opTy.layout.layout.size.bytes == 0 then
        return ⟨.immediate .uninit, opTy.layout⟩
      else
        let imm ← annealReadImmediateLM2_2 opTy
        return ⟨.immediate imm.imm, imm.layout⟩
    evalOperandAt := fun _ _ op known => do
      let opTy ← annealEvalOperandLM2_4PaddedZst localDecls layouts op known
      if opTy.layout.layout.size.bytes == 0 then
        return ⟨.immediate .uninit, opTy.layout⟩
      else
        let imm ← annealReadImmediateLM2_2 opTy
        return ⟨.immediate imm.imm, imm.layout⟩
    copyOpNoValidate := fun c src dest b => do
      if src.layout.layout.size.bytes == 0 && dest.layout.layout.size.bytes == 0 then
        match dest.1 with
        | .memory mp =>
          let st ← get
          match mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId with
          | none => throw (.undefinedBehavior "zero-sized aggregate write without provenance")
          | some allocId =>
            match st.machine.memory.live.find? (fun (id, _) => id == allocId) with
            | none => throw (.undefinedBehavior "zero-sized aggregate write to dead allocation")
            | some (_, _) => pure ()
        | .local .. =>
          base.copyOpNoValidate c src dest b
      else
        base.copyOpNoValidate c src dest b }

/-- Additive rvalue hooks extending `annealRvalueHooksLM2_4` with
`annealEvalOperandLM2_4PaddedZst` and `annealAggregateHooksLM2_4PaddedZst`. -/
def annealRvalueHooksLM2_4PaddedZst
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    Miri.Interpreter.RvalueHooks
      AnnealProv
      AnnealStepState
      Unit
      (Miri.Interpreter.RuntimePlace AnnealProv) :=
  let base := annealRvalueHooksLM2_4 localDecls layouts
  { base with
    evalOperand := fun _ op known =>
      annealEvalOperandLM2_4PaddedZst localDecls layouts op known
    evalOperandAt := fun _ _ op known =>
      annealEvalOperandLM2_4PaddedZst localDecls layouts op known
    evalPlaceToOp := fun _ p known =>
      annealEvalOperandLM2_4PaddedZst localDecls layouts (.Copy p) known
    writeAggregate := fun c k os d =>
      Miri.Interpreter.writeAggregate
        (annealAggregateHooksLM2_4PaddedZst localDecls layouts) c k os d }

/-- Additive step hooks extending `annealStepHooksLM2_4` with
`annealRvalueHooksLM2_4PaddedZst` for padded `[(); N]` union ZST array arms
(`kani#5176` / `kani#5159`). -/
def annealStepHooksLM2_4PaddedZst
    (localDecls : List LocalDecl := .nil) (layouts : LayoutTable := emptyLayoutTable) :
    Miri.Interpreter.StepHooks
      AnnealProv
      Miri.Interpreter.LocalLayout
      Unit
      AnnealMachine
      Unit
      (Miri.Interpreter.RuntimePlace AnnealProv) :=
  let base := annealStepHooksLM2_4 localDecls layouts
  { base with
    assign := fun choice place rvalue state =>
      if lm24Assign localDecls layouts place rvalue then
        Miri.Interpreter.runRvalue
          (Miri.Interpreter.evalRvalueIntoPlace
            (annealRvalueHooksLM2_4PaddedZst localDecls layouts) choice rvalue place)
          state
      else
        base.assign choice place rvalue state }

/-- For any `.Use op` rvalue where `annealEvalOperandLM2_4PaddedZst` agrees with
`annealEvalOperandLM2_4` (including all non-union operands, all `[]`-projected
union copies/moves, and all inhabited `[Field j fty]` union field reads by
`annealEvalOperandLM2_4PaddedZst_eq_of_inhabited_field`), `evalRvalueIntoPlace`
and `StepHooks.assign` under `annealStepHooksLM2_4PaddedZst` are identical to
`annealStepHooksLM2_4` (`G4`). -/
theorem annealStepHooksLM2_4PaddedZst_assign_use_eq
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (choice : Unit) (place : Miri.MIR.Place) (op : Miri.MIR.Operand)
    (retag : Miri.MIR.WithRetag) (state : AnnealStepState)
    (hop : ∀ known,
      annealEvalOperandLM2_4PaddedZst localDecls layouts op known =
        annealEvalOperandLM2_4 localDecls layouts op known) :
    (annealStepHooksLM2_4PaddedZst localDecls layouts).assign choice place (.Use op retag) state =
      (annealStepHooksLM2_4 localDecls layouts).assign choice place (.Use op retag) state := by
  have hrv : Miri.Interpreter.evalRvalueIntoPlace
      (annealRvalueHooksLM2_4PaddedZst localDecls layouts) choice (.Use op retag) place =
    Miri.Interpreter.evalRvalueIntoPlace
      (annealRvalueHooksLM2_4 localDecls layouts) choice (.Use op retag) place := by
    unfold Miri.Interpreter.evalRvalueIntoPlace annealRvalueHooksLM2_4PaddedZst annealRvalueHooksLM2_4
    dsimp only
    congr 1
    funext dest
    rw [hop]
  unfold annealStepHooksLM2_4PaddedZst annealStepHooksLM2_4
  dsimp only
  split
  · rw [hrv]
  · rfl

@[simp] theorem annealStepHooksLM2_4PaddedZst_storageLive_eq
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    (annealStepHooksLM2_4PaddedZst localDecls layouts).storageLive =
      (annealStepHooksLM2_4 localDecls layouts).storageLive := rfl

@[simp] theorem annealStepHooksLM2_4PaddedZst_storageDead_eq
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    (annealStepHooksLM2_4PaddedZst localDecls layouts).storageDead =
      (annealStepHooksLM2_4 localDecls layouts).storageDead := rfl

end LeanMiriSpec.Correspondence
