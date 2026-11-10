/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import LeanMiriSpec.Correspondence.Simulation
import LeanMiriSpec.Correspondence.SimLM1_2
import LeanMiriSpec.Correspondence.SimLM1_4
import LeanMiriSpec.Correspondence.LayoutLM2_2
import LeanMiriSpec.Correspondence.ProjLM2_2

/-!
# Multi-Variant Enum Hooks, `ValidEnumLayout`, and `StateRelLM2_3` (`LM-2.3`)

In `Translate.lean`, `annealStepHooksLM2_2.writeDiscriminant`,
`annealRvalueHooksLM2_2.readDiscriminant`,
`annealRvalueHooksLM2_2.discriminantForVariant`, `annealStructProjectionCx.variant`,
and non-zero `annealAggregateHooksLM2_2` variant downcasts/discriminants fail closed
with `StepError.unsupported`.

This module wires the vendored `lean-miri` multi-variant enum pipelines
(`Miri.Interpreter.Discriminant.{writeDiscriminant, readDiscriminant,
discriminantForVariant, tagForVariant}`, `Miri.Interpreter.writeAggregate`, and
`Miri.Interpreter.{project, projectDowncast, projectField}`) as a conservative
overlay `annealStepHooksLM2_3` over `annealStepHooksLM2_2`
(`step_LM2_3_eq_of_bodyFree`), and defines the modular enum state relation
(`ValidEnumLayout`, `EnumMemRel`, `UninitEnumMemRel`, `LocalRelLM2_3`,
`EnumLocalByteUninit`, `FrameRelLM2_3`, `StateRelLM2_3`, and `StepRelLM2_3`)
consumed by `SimLM2_3.lean` and `WitLM2_3.lean`.
-/

namespace LeanMiriSpec.Correspondence

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

/-! ## 1. Enum Layout Classification, Downcast, and Projection Context -/

/-- Whether `lay` has a multi-variant `Variants.Multiple` enum layout. -/
def isEnumLayout (lay : Miri.Interpreter.LocalLayout) : Bool :=
  match lay.layout.variants with
  | .Multiple _ _ _ _ => true
  | _ => false

/-- Whether `localId` is declared in `localDecls` with a multi-variant enum
layout. -/
def isEnumLocal (localDecls : List LocalDecl) (layouts : LayoutTable)
    (localId : Nat) : Bool :=
  match lookupLocalDeclLayout localDecls layouts localId with
  | some lay => isEnumLayout lay
  | none => false

/-- Downcast a `Variants.Multiple` enum `LocalLayout` to variant `variant`,
installing that variant's `fieldOffsets`, `fieldsInMemoryOrder`, and
`uninhabited` flag while preserving the outer enum `TyId` and byte `size`. -/
def downcastEnumLayout (parent : Miri.Interpreter.LocalLayout) (variant : Nat) :
    Except Miri.Interpreter.ProjectionError Miri.Interpreter.LocalLayout :=
  match parent.layout.variants with
  | .Multiple _ _ _ vars =>
      match vars[variant]? with
      | some vl =>
          .ok { ty := parent.ty
                layout := { parent.layout with
                  fields := .Arbitrary vl.fieldOffsets vl.fieldsInMemoryOrder
                  variants := .Single variant
                  backendRepr := .Memory (sized := true)
                  uninhabited := vl.uninhabited } }
      | none => .error (.invariant "enum variant index out of bounds")
  | .Single actual =>
      if variant == actual then .ok parent
      else .error (.invariant "single-variant downcast mismatch")
  | .Empty => .error (.invariant "downcast on empty variants")

/-- `annealStructProjectionCx` extended with `downcastEnumLayout` so vendored
`Miri.Interpreter.project` (`projectDowncast` + `projectField`) handles
`PlaceElem.Downcast` followed by `PlaceElem.Field`. -/
def annealEnumProjectionCx (layouts : LayoutTable)
    (hintFieldTy : Option Miri.MIR.TyId) :
    Miri.Interpreter.ProjectionCx AnnealProv :=
  { annealStructProjectionCx layouts hintFieldTy with
    variant := downcastEnumLayout }

/-- Project an `OpTy AnnealProv` along a list of `Miri.MIR.ProjectionElem`s
under `annealEnumProjectionCx` using vendored `Miri.Interpreter.project`. -/
def annealEvalEnumProjection (layouts : LayoutTable)
    (base : Miri.Interpreter.OpTy AnnealProv) :
    List Miri.MIR.ProjectionElem →
    Miri.Interpreter.RvalueM AnnealStepState (Miri.Interpreter.OpTy AnnealProv)
  | [] => return base
  | elem :: rest => do
      let hintTy :=
        match elem with
        | .Field _ ft => some ft
        | _ => none
      let next ←
        match Miri.Interpreter.project (annealEnumProjectionCx layouts hintTy)
            base elem with
        | .ok opTy => pure opTy
        | .error err => throw (annealLiftProjectionError err)
      annealEvalEnumProjection layouts next rest

/-- Infer the `LocalLayout` of a `Miri.MIR.Operand` from `localDecls` or its
encoded `Miri.MIR.TyId` when projecting aggregate operand destinations in
`Miri.Interpreter.writeAggregate`. -/
def miriOperandLayout (localDecls : List LocalDecl) (layouts : LayoutTable) :
    Miri.MIR.Operand → Option Miri.Interpreter.LocalLayout
  | .Copy place | .Move place =>
      match place.projection.back? with
      | none => lookupLocalDeclLayout localDecls layouts place.localId
      | some (.Field _ fty) => some (layoutOfEncodedTyId fty layouts)
      | some _ => none
  | .Constant c =>
      let cTyId :=
        match c.value with
        | .Ty ty _ | .Unevaluated _ ty | .Val _ ty => ty
      some (layoutOfEncodedTyId cTyId layouts)
  | .RuntimeChecks _ => none

/-! ## 2. Tag Scalar Layout and `annealDiscriminantHooksLM2_3` -/

/-- Byte width of a `Miri.ABI.Integer`. -/
def abiIntegerByteWidth : Miri.ABI.Integer → Nat
  | .I8 => 1
  | .I16 => 2
  | .I32 => 4
  | .I64 => 8
  | .I128 => 16

/-- Encoded `Miri.MIR.TyId` for an integer scalar of width `intKind` and
signedness `signed`. -/
def abiIntegerTyId : Miri.ABI.Integer → Bool → Miri.MIR.TyId
  | .I8, true => 10
  | .I16, true => 11
  | .I32, true => 12
  | .I64, true => 13
  | .I128, true => 14
  | .I8, false => 20
  | .I16, false => 21
  | .I32, false => 22
  | .I64, false => 23
  | .I128, false => 24

/-- Construct the `LocalLayout` of an integer enum tag `Miri.ABI.Scalar`. -/
def tagLayoutOfAbiScalar (tag : Miri.ABI.Scalar) :
    Option Miri.Interpreter.LocalLayout :=
  match tag with
  | @Miri.ABI.Scalar.Initialized (.Int intKind signed) _ =>
      let sz := abiIntegerByteWidth intKind
      some { ty := abiIntegerTyId intKind signed
             layout := { (scalarLayoutData sz signed) with
               backendRepr := .Scalar tag } }
  | _ => none

/-- Extract the tag field's `LocalLayout` from a `Variants.Multiple` enum
layout. -/
def enumTagLayoutOf (enumLay : Miri.Interpreter.LocalLayout) :
    Option Miri.Interpreter.LocalLayout :=
  match enumLay.layout.variants with
  | .Multiple tag _ _ _ => tagLayoutOfAbiScalar tag
  | _ => none

/-- Run vendored `Miri.Interpreter.forceAllocation` under
`annealMutablePlaceHooks`, mapping `StackError.localExpectedLive` to
`StepError.undefinedBehavior "write to dead local"` to match rustc's
`err_ub!(DeadLocal)` and Anneal's `MirSemantics.evalStmt`. -/
def annealForceEnumAllocation (localDecls : List LocalDecl)
    (layouts : LayoutTable) (dest : Miri.Interpreter.RuntimePlace AnnealProv) :
    Miri.Interpreter.RvalueM AnnealStepState
      (Miri.Interpreter.MPlaceTy AnnealProv) :=
  fun st =>
    match Miri.Interpreter.forceAllocation
        (annealMutablePlaceHooks localDecls layouts) () dest st with
    | .error (.stack (.localExpectedLive _)) st' =>
        .error (.undefinedBehavior "write to dead local") st'
    | res => res

/-- `ProjectionCx` resolving field `fieldIdx` directly to `fixedLay`. -/
def fixedFieldProjectionCx (layouts : LayoutTable)
    (fixedLay : Miri.Interpreter.LocalLayout) :
    Miri.Interpreter.ProjectionCx AnnealProv :=
  { annealStructProjectionCx layouts none with
    field := fun _ _ => .ok fixedLay }

/-- `DiscriminantHooks` instantiated for Anneal's single-threaded machine,
wiring vendored `Miri.Interpreter.Discriminant.{writeDiscriminant,
readDiscriminant, discriminantForVariant, tagForVariant}` to `LayoutTable`
variant counts, `Miri.Interpreter.projectField` tag projection, and
`annealReadImmediateLM2_2` / `annealWriteImmediateLM2_2`.

`discriminantValue` and `variantForDiscriminant` identify each variant's
discriminant with its index, as an `isize` (Rust's default enum discriminant
type). This matches Anneal's `evalRvalue`, which evaluates `.discriminant` to
`⟨variantIdx, 8⟩`. `LayoutTable` records no explicit discriminant values, so
enums declared with explicit discriminants (`A = 5`) are outside this model. -/
def annealDiscriminantHooksLM2_3 (localDecls : List LocalDecl)
    (layouts : LayoutTable) :
    Miri.Interpreter.DiscriminantHooks
      AnnealProv
      AnnealStepState
      Unit
      (Miri.Interpreter.RuntimePlace AnnealProv) where
  runtimeTarget := annealRuntimeDataLayout
  discriminantLayout := fun _ _ =>
    pure (translateTy { kind := .int .isize, layoutIdx := 0 } layouts)
  tagLayout := fun _ tag =>
    match tagLayoutOfAbiScalar tag with
    | some l => pure l
    | none => throw (.unsupported "non-integer enum tag scalar")
  discriminantValue := fun _ tyId variant =>
    if 100 ≤ tyId then
      match layouts.lookup (tyId - 100) with
      | some tl =>
          match tl.variants with
          | .multiple _ _ vs =>
              if variant < vs.length then
                pure (some (15, BitVec.ofNat 128 variant))
              else
                pure none
          | _ => pure none
      | none => pure none
    else
      pure none
  variantForDiscriminant := fun _ tyId discrBits =>
    if 100 ≤ tyId then
      match layouts.lookup (tyId - 100) with
      | some tl =>
          match tl.variants with
          | .multiple _ _ vs =>
              if discrBits.toNat < vs.length then
                pure (some discrBits.toNat)
              else
                pure none
          | _ => pure none
      | none => pure none
    else
      pure none
  adtVariantCount := fun _ tyId =>
    if 100 ≤ tyId then
      match layouts.lookup (tyId - 100) with
      | some tl =>
          match tl.variants with
          | .multiple _ _ vs => pure vs.length
          | .single _ => pure 1
          | .empty => pure 0
      | none => pure 0
    else
      pure 0
  projectRead := fun _ op fieldIdx =>
    match enumTagLayoutOf op.layout with
    | some tagLay =>
        match Miri.Interpreter.projectField
            (fixedFieldProjectionCx layouts tagLay) op fieldIdx with
        | .ok tagOp => pure tagOp
        | .error err => throw (annealLiftProjectionError err)
    | none => throw (.unsupported "enum tag layout missing in projectRead")
  readImmediate := fun _ op => annealReadImmediateLM2_2 op
  destLayout := fun p => p.layout
  projectWrite := fun _ dest fieldIdx => do
    let some tagLay := enumTagLayoutOf dest.layout
      | throw (.unsupported "enum tag layout missing in projectWrite")
    let forced ← annealForceEnumAllocation localDecls layouts dest
    match Miri.Interpreter.projectField
        (fixedFieldProjectionCx layouts tagLay)
        ⟨.indirect forced.mplace, forced.layout⟩ fieldIdx with
    | .ok ⟨.indirect tagMp, lay'⟩ => return ⟨.memory tagMp, lay'⟩
    | .ok ⟨.immediate _, _⟩ =>
        throw (.invalidProgram "enum tag write projected to immediate")
    | .error err => throw (annealLiftProjectionError err)
  writeScalar := fun _ sc dest => annealWriteImmediateLM2_2 (.scalar sc) dest
  toOp := fun _ dest =>
    match dest.ref with
    | .memory mp => pure ⟨.indirect mp, dest.layout⟩
    | .local _ localId none _ =>
        annealEvalOperand localDecls layouts (.Copy ⟨localId, #[]⟩)
          (some dest.layout)
    | _ => throw (.unsupported "projected local in DiscriminantHooks.toOp")
  scalarMayBeNull := fun _ _ =>
    throw (.unsupported "pointer niche nullability in LM-2.3")

/-! ## 3. Enum Operand, Aggregate, `SetDiscriminant`, and `StepHooks` Overlay -/

/-- Whether a `Miri.MIR.ProjectionElem` is a `Downcast`. -/
def isDowncastElem : Miri.MIR.ProjectionElem → Bool
  | .Downcast _ _ => true
  | _ => false

/-- Evaluate a `Copy` / `Move` operand carrying a `Downcast` projection chain on
a local in the top frame. Uninitialized immediate locals project through
`Miri.Interpreter.project` (`projectionImmediateOffset`) to `.immediate .uninit`
so the downstream `annealReadImmediateLM2_2` diagnoses UB, while indirect locals
project directly into the allocation so `annealReadImmediateLM2_2` checks
initialization of the target variant field's byte slice. -/
def annealEvalDowncastOperand (localDecls : List LocalDecl)
    (layouts : LayoutTable) (place : Miri.MIR.Place)
    (known : Option Miri.Interpreter.LocalLayout) :
    Miri.Interpreter.RvalueM AnnealStepState (Miri.Interpreter.OpTy AnnealProv) := do
  let st ← get
  if st.stack.currentFrame?.isNone then
    throw (.stack .emptyStack)
  let (frame', layout) ←
    annealResolveAndCacheLocalLayout localDecls layouts place.localId known
  let operand ← match frame'.getLocalOperand place.localId with
    | .ok op => pure op
    | .error (.localExpectedLive _) =>
        throw (.undefinedBehavior "read of dead local")
    | .error e => throw (.stack e)
  annealEvalEnumProjection layouts ⟨operand, layout⟩ place.projection.toList

/-- Enum-aware operand evaluation: `Copy` / `Move` operands containing a
`Downcast` projection use `annealEvalDowncastOperand`; all other operands
delegate to `annealEvalOperand`. -/
def annealEvalOperandLM2_3 (localDecls : List LocalDecl) (layouts : LayoutTable)
    (op : Miri.MIR.Operand) (known : Option Miri.Interpreter.LocalLayout) :
    Miri.Interpreter.RvalueM AnnealStepState (Miri.Interpreter.OpTy AnnealProv) :=
  match op with
  | .Copy place | .Move place =>
      if place.projection.toList.any isDowncastElem then
        annealEvalDowncastOperand localDecls layouts place known
      else
        annealEvalOperand localDecls layouts op known
  | _ => annealEvalOperand localDecls layouts op known

/-- Project a `RuntimePlace AnnealProv` by one `Miri.MIR.ProjectionElem` under
`annealEnumProjectionCx`, mirroring vendored
`Miri.Interpreter.projectRuntimePlace` (`Miri/Interpreter/Place.lean`) so
destination places carrying `ProjectionElem.Downcast` install the target
variant's `VariantLayout` before subsequent `ProjectionElem.Field` offsets. -/
def annealProjectEnumPlaceElem (layouts : LayoutTable)
    (place : Miri.Interpreter.RuntimePlace AnnealProv)
    (elem : Miri.MIR.ProjectionElem) :
    Except Miri.Interpreter.StepError
      (Miri.Interpreter.RuntimePlace AnnealProv) := do
  let hintTy :=
    match elem with
    | .Field _ ft => some ft
    | _ => none
  let cx := annealEnumProjectionCx layouts hintTy
  match place.ref with
  | .memory mplace =>
      match Miri.Interpreter.project cx
          ⟨.indirect mplace, place.layout⟩ elem with
      | .ok ⟨.indirect mplace', layout'⟩ => return ⟨.memory mplace', layout'⟩
      | .ok ⟨.immediate _, _⟩ =>
          throw (.invalidProgram "memory projection returned immediate")
      | .error err => throw (annealLiftProjectionError err)
  | .local frame localId offset identity =>
      if !place.layout.layout.isSized then
        throw (.invalidProgram "unsized local place")
      let baseOffset := offset.getD Miri.ABI.Size.ZERO
      let carrier : Miri.Interpreter.MemPlace AnnealProv :=
        ⟨⟨baseOffset, none⟩, .none, none⟩
      match Miri.Interpreter.project cx
          ⟨.indirect carrier, place.layout⟩ elem with
      | .ok ⟨.indirect result, layout'⟩ =>
          if !layout'.layout.isSized || result.metadata.hasMeta then
            throw (.invalidProgram "unsized projected local")
          let bound ←
            match result.ptr.offset.add layout'.layout.size with
            | .ok b => pure b
            | .error _ =>
                throw (.invalidProgram "projected local size overflow")
          let endOffset ←
            match baseOffset.add place.layout.layout.size with
            | .ok e => pure e
            | .error _ => throw (.invalidProgram "local size overflow")
          if result.ptr.offset.bytes < baseOffset.bytes ||
              bound.bytes > endOffset.bytes then
            throw (.invalidProgram "projected local is out of bounds")
          else
            return ⟨.local frame localId (some result.ptr.offset) identity,
              layout'⟩
      | .ok ⟨.immediate _, _⟩ =>
          throw (.invalidProgram "local projection returned immediate")
      | .error err => throw (annealLiftProjectionError err)

/-- Project a `RuntimePlace AnnealProv` along a list of
`Miri.MIR.ProjectionElem`s using `annealProjectEnumPlaceElem`. -/
def annealProjectEnumPlaceList (layouts : LayoutTable)
    (place : Miri.Interpreter.RuntimePlace AnnealProv) :
    List Miri.MIR.ProjectionElem →
    Except Miri.Interpreter.StepError
      (Miri.Interpreter.RuntimePlace AnnealProv)
  | [] => .ok place
  | elem :: rest => do
      let next ← annealProjectEnumPlaceElem layouts place elem
      annealProjectEnumPlaceList layouts next rest

/-- Resolve a `Downcast`-projected destination `Miri.MIR.Place` in the top
frame via `annealProjectEnumPlaceList`. -/
def annealEvalEnumProjectedPlace (localDecls : List LocalDecl)
    (layouts : LayoutTable) (place : Miri.MIR.Place) :
    Miri.Interpreter.RvalueM AnnealStepState
      (Miri.Interpreter.RuntimePlace AnnealProv) := do
  let st ← get
  if st.stack.currentFrame?.isNone then
    throw (.stack .emptyStack)
  let frameIdx := st.stack.frames.size - 1
  let (frame', layout) ←
    annealResolveAndCacheLocalLayout localDecls layouts place.localId none
  let base : Miri.Interpreter.RuntimePlace AnnealProv :=
    ⟨.local frameIdx place.localId none frame'.localsIdentity, layout⟩
  match annealProjectEnumPlaceList layouts base place.projection.toList with
  | .ok p => return p
  | .error err => throw err

/-- Enum-aware place evaluation: places carrying a `Downcast` projection use
`annealEvalEnumProjectedPlace`; all other places delegate unchanged to
`annealEvalPlace`. -/
def annealEvalPlaceLM2_3 (localDecls : List LocalDecl)
    (layouts : LayoutTable) (place : Miri.MIR.Place) :
    Miri.Interpreter.RvalueM AnnealStepState
      (Miri.Interpreter.RuntimePlace AnnealProv) :=
  if place.projection.toList.any isDowncastElem then
    annealEvalEnumProjectedPlace localDecls layouts place
  else
    annealEvalPlace localDecls layouts place

/-- `AggregateHooks` for multi-variant enum construction (`LM-2.3`), forcing the
enum destination into memory on `projectDowncast`, projecting each
active-variant payload field via `Miri.Interpreter.projectField`, copying each
evaluated scalar operand into its variant offset, and writing the variant's tag
scalar via vendored `Miri.Interpreter.Discriminant.writeDiscriminant`. -/
def annealAggregateHooksLM2_3 (localDecls : List LocalDecl)
    (layouts : LayoutTable) (operands : Array Miri.MIR.Operand) :
    Miri.Interpreter.AggregateHooks
      AnnealProv
      AnnealStepState
      Unit
      (Miri.Interpreter.RuntimePlace AnnealProv) :=
  let base := annealAggregateHooksLM2_2 localDecls layouts
  { base with
    evalOperand := fun _ op known =>
      annealEvalOperandLM2_3 localDecls layouts op known
    evalOperandAt := fun _ _ op known =>
      annealEvalOperandLM2_3 localDecls layouts op known
    projectDowncast := fun _ dest variant =>
      match dest.layout.layout.variants with
      | .Single actual =>
          if variant == actual then pure dest
          else throw (.invalidProgram "single-variant aggregate downcast mismatch")
      | .Multiple _ _ _ _ => do
          let forced ← annealForceEnumAllocation localDecls layouts dest
          match downcastEnumLayout forced.layout variant with
          | .ok varLay => return ⟨.memory forced.mplace, varLay⟩
          | .error err => throw (annealLiftProjectionError err)
      | .Empty =>
          throw (.undefinedBehavior "aggregate construction of uninhabited enum")
    projectField := fun c dest fieldIdx =>
      match dest.ref with
      | .memory mp =>
          match operands[fieldIdx]? >>= miriOperandLayout localDecls layouts with
          | some fieldLay =>
              match Miri.Interpreter.projectField
                  (fixedFieldProjectionCx layouts fieldLay)
                  ⟨.indirect mp, dest.layout⟩ fieldIdx with
              | .ok ⟨.indirect fieldMp, lay'⟩ => return ⟨.memory fieldMp, lay'⟩
              | .ok ⟨.immediate _, _⟩ =>
                  throw (.invalidProgram "enum aggregate field resolved to immediate")
              | .error err => throw (annealLiftProjectionError err)
          | none => base.projectField c dest fieldIdx
      | _ => base.projectField c dest fieldIdx
    writeDiscriminant := fun c variant dest =>
      match dest.layout.layout.variants with
      | .Single actual =>
          if variant == actual then pure ()
          else throw (.invalidProgram "single-variant aggregate discriminant mismatch")
      | _ =>
          Miri.Interpreter.Discriminant.writeDiscriminant
            (annealDiscriminantHooksLM2_3 localDecls layouts) c variant dest }

/-- `RvalueHooks` extended with multi-variant enum `Aggregate`, `Discriminant`,
and `Downcast` place and operand support. -/
def annealRvalueHooksLM2_3 (localDecls : List LocalDecl)
    (layouts : LayoutTable) :
    Miri.Interpreter.RvalueHooks
      AnnealProv
      AnnealStepState
      Unit
      (Miri.Interpreter.RuntimePlace AnnealProv) :=
  let discrHooks := annealDiscriminantHooksLM2_3 localDecls layouts
  { annealRvalueHooksLM2_2 localDecls layouts with
    evalPlace := fun _ p _ =>
      annealEvalPlaceLM2_3 localDecls layouts p
    evalOperand := fun _ op known =>
      annealEvalOperandLM2_3 localDecls layouts op known
    evalOperandAt := fun _ _ op known =>
      annealEvalOperandLM2_3 localDecls layouts op known
    evalPlaceToOp := fun _ p known =>
      annealEvalOperandLM2_3 localDecls layouts (.Copy p) known
    writeAggregate := fun c k os d =>
      Miri.Interpreter.writeAggregate
        (annealAggregateHooksLM2_3 localDecls layouts os) c k os d
    readDiscriminant := fun c op =>
      Miri.Interpreter.Discriminant.readDiscriminant discrHooks c op
    discriminantForVariant := fun c tyId variant =>
      Miri.Interpreter.Discriminant.discriminantForVariant discrHooks c tyId variant }

/-- Whether a `Miri.MIR.Operand` contains a `Downcast` projection. -/
def lm23Operand : Miri.MIR.Operand → Bool
  | .Copy p | .Move p => p.projection.toList.any isDowncastElem
  | _ => false

/-- Whether an `Assign` statement exercises the `LM-2.3` multi-variant enum
fragment: `Rvalue.Discriminant`, enum `Rvalue.Aggregate (.Adt ...)`, or an
operand/place carrying `ProjectionElem.Downcast`. -/
def lm23Assign (localDecls : List LocalDecl) (layouts : LayoutTable)
    (place : Miri.MIR.Place) (rvalue : Miri.MIR.Rvalue) : Bool :=
  place.projection.toList.any isDowncastElem ||
  match rvalue with
  | .Discriminant _ => true
  | .Aggregate (.Adt _ _ _ _ none) ops =>
      isEnumLocal localDecls layouts place.localId || ops.any lm23Operand
  | .Use op _ | .Repeat op _ | .Cast _ op _ | .UnaryOp _ op | .WrapUnsafeBinder op _ =>
      lm23Operand op
  | .BinaryOp _ l r =>
      lm23Operand l || lm23Operand r
  | _ => false

/-- Conservative `StepHooks` overlay for `LM-2.3`: intercepts only `lm23Assign`
assignments and `StatementKind.SetDiscriminant`, delegating every other
statement and terminator unchanged to `annealStepHooksLM2_2`.

`writeDiscriminant` runs vendored `Discriminant.writeDiscriminant` with no
extra checks, exactly as lean-miri's reference `ExecutionMachine.stepHooks`
does (and as rustc's `write_discriminant` does for direct tags). It does not
read the destination first, so `SetDiscriminant` on an uninitialized enum local
forces the local into memory and writes the tag. A dead destination fails in
`projectWrite`'s `annealForceEnumAllocation` with `"write to dead local"`
(rustc's `DeadLocal`). Anneal's `evalStmt` is stricter on uninitialized
destinations; `step_setDiscriminant_uninit_divergence` in `SimLM2_3.lean`
states that difference. -/
def annealStepHooksLM2_3 (localDecls : List LocalDecl := .nil)
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
      if lm23Assign localDecls layouts place rvalue then
        Miri.Interpreter.runRvalue
          (Miri.Interpreter.evalRvalueIntoPlace
            (annealRvalueHooksLM2_3 localDecls layouts) choice rvalue place)
          state
      else
        base.assign choice place rvalue state
    writeDiscriminant := fun choice variant dest state =>
      Miri.Interpreter.runRvalue
        (Miri.Interpreter.Discriminant.writeDiscriminant
          (annealDiscriminantHooksLM2_3 localDecls layouts) choice variant dest)
        state }

/-- Whether a `Miri.MIR.Statement` is outside the `LM-2.3` overlay (`lm23Assign`
and `.SetDiscriminant`). -/
def stmtFreeOfLM2_3 (localDecls : List LocalDecl) (layouts : LayoutTable)
    (stmt : Miri.MIR.Statement) : Prop :=
  match stmt.kind with
  | .Assign place rvalue => lm23Assign localDecls layouts place rvalue = false
  | .SetDiscriminant _ _ => False
  | _ => True

/-- Whether every basic block of `body` is free of `LM-2.3`-specific
statements. -/
def BodyFreeOfLM2_3 (localDecls : List LocalDecl) (layouts : LayoutTable)
    (body : Miri.MIR.Body) : Prop :=
  ∀ bb ∈ body.basicBlocks.toList,
    ∀ stmt ∈ bb.statements.toList,
      stmtFreeOfLM2_3 localDecls layouts stmt

theorem evalStatement_LM2_3_eq_of_stmtFree {localDecls : List LocalDecl}
    {layouts : LayoutTable} {stmt : Miri.MIR.Statement}
    (hfree : stmtFreeOfLM2_3 localDecls layouts stmt)
    (choice : Unit) (state : AnnealStepState) :
    Miri.Interpreter.Step.evalStatement
        (annealStepHooksLM2_3 localDecls layouts) choice stmt state =
      Miri.Interpreter.Step.evalStatement
        (annealStepHooksLM2_2 localDecls layouts) choice stmt state := by
  rcases stmt with ⟨si, kind⟩
  cases kind with
  | Assign place rvalue =>
      dsimp [stmtFreeOfLM2_3] at hfree
      simp [Miri.Interpreter.Step.evalStatement, annealStepHooksLM2_3, hfree]
  | SetDiscriminant _ _ =>
      exact False.elim hfree
  | StorageLive _ | StorageDead _ | Intrinsic _ | PlaceMention _
  | ConstEvalCounter | FakeRead _ | AscribeUserType _ _ | Coverage _
  | Nop | BackwardIncompatibleDropHint _ _ =>
      rfl

/-- Conservative-extension theorem: on any MIR body whose top-frame statements
contain no `LM-2.3` enum operations (`BodyFreeOfLM2_3`), `annealStepHooksLM2_3`
steps identically to `annealStepHooksLM2_2`. -/
theorem step_LM2_3_eq_of_bodyFree {localDecls : List LocalDecl}
    {layouts : LayoutTable} {state : AnnealStepState}
    (hfree : ∀ frame, state.stack.currentFrame? = some frame →
      BodyFreeOfLM2_3 localDecls layouts frame.body)
    (choice : Unit) :
    Miri.Interpreter.Step.step
        (annealStepHooksLM2_3 localDecls layouts) choice state =
      Miri.Interpreter.Step.step
        (annealStepHooksLM2_2 localDecls layouts) choice state := by
  unfold Miri.Interpreter.Step.step
  cases hcf : state.stack.currentFrame? with
  | none => rfl
  | some frame =>
      dsimp only [Id.run]
      cases hloc : frame.location with
      | unwinding _ => rfl
      | mir loc =>
          dsimp only
          cases hbb : frame.body.basicBlocks[loc.block]? with
          | none => rfl
          | some bb =>
              dsimp only
              cases hst : bb.statements[loc.statementIndex]? with
              | none => rfl
              | some stmt =>
                  have hbb_mem : bb ∈ frame.body.basicBlocks.toList := by
                    obtain ⟨hlt, rfl⟩ := Array.getElem?_eq_some_iff.mp hbb
                    exact Array.getElem_mem_toList hlt
                  have hst_mem : stmt ∈ bb.statements.toList := by
                    obtain ⟨hlt, rfl⟩ := Array.getElem?_eq_some_iff.mp hst
                    exact Array.getElem_mem_toList hlt
                  have hsfree := hfree frame hcf bb hbb_mem stmt hst_mem
                  dsimp only
                  rw [evalStatement_LM2_3_eq_of_stmtFree hsfree]

/-! ## 4. `ValidEnumLayout`, `EnumMemRel`, and `StateRelLM2_3` -/

/-- Well-formedness predicate for a single variant's payload fields inside a
direct-tagged multi-variant enum of byte size `enumSize` and tag width
`tagBytes`:
1. Every field has primitive scalar type (`IsPrimScalarTy`), `fieldLayout =
   (translateTy f.ty layouts).layout`, offset `≥ tagBytes`, and end offset
   `≤ enumSize`.
2. Within the variant, distinct payload fields have pairwise-disjoint byte
   intervals `[offset, offset + size)`.
3. The translated `VariantLayout` has `fieldOffsets` matching `(fields.map
   (·.offset)).toArray` and `uninhabited = false`. -/
structure ValidEnumVariantFields (layouts : LayoutTable) (tagBytes : Nat)
    (enumSize : Nat) (vl : Miri.ABI.VariantLayout)
    (fields : List StructFieldDesc) : Prop where
  vl_offsets_eq : vl.fieldOffsets = (fields.map (·.offset)).toArray
  vl_order_len : vl.fieldsInMemoryOrder.size = fields.length
  vl_inhabited : vl.uninhabited = false
  fields_prim :
    ∀ i (hi : i < fields.length),
      IsPrimScalarTy (fields[i]'hi).ty ∧
      (fields[i]'hi).fieldLayout = (translateTy (fields[i]'hi).ty layouts).layout
  fields_after_tag :
    ∀ i (hi : i < fields.length),
      tagBytes ≤ (fields[i]'hi).offset.bytes.toNat
  fields_in_bounds :
    ∀ i (hi : i < fields.length),
      (fields[i]'hi).offset.bytes.toNat +
        (fields[i]'hi).fieldLayout.size.bytes.toNat ≤ enumSize
  fields_disjoint :
    ∀ i j (hi : i < fields.length) (hj : j < fields.length),
      i ≠ j →
      (fields[i]'hi).offset.bytes.toNat +
        (fields[i]'hi).fieldLayout.size.bytes.toNat ≤
        (fields[j]'hj).offset.bytes.toNat ∨
      (fields[j]'hj).offset.bytes.toNat +
        (fields[j]'hj).fieldLayout.size.bytes.toNat ≤
        (fields[i]'hi).offset.bytes.toNat

/-- Genuine multi-variant direct-tagged enum layout (`LM-2.3`):
* `ty` is an `.adt defPath adtArgs` whose `LayoutTable` entry `tl` has
  `.multiple rawTag 0 rawVarShapes` with `variants.length ≥ 2` (at least two
  variants) and `< 2 ^ (8 * tagBytes)` (fitting in the unsigned tag width
  `tagBytes ∈ {1, 2, 4, 8}`).
* The outer enum layout has `backendRepr = .Memory (sized := true)`,
  `fields = .Arbitrary #[Size.ZERO] #[0]` (direct tag at field `0`, offset `0`),
  `variants = .Multiple tag .Direct 0 vars` where `tag` is an unsigned integer
  scalar of width `tagBytes` whose `validRange` contains every variant index
  `v < variants.length`, `tagBytes ≤ size < 2 ^ 32`, and `align.abi.pow2 ≤ 29`.
* Each variant `v < variants.length` satisfies `ValidEnumVariantFields`, which
  in particular makes every variant inhabited. That excludes no translated
  layout: Anneal's `LayoutTable` cannot express an uninhabited variant
  (`isVariantUninhabited_translateVariantsShape_multiple`), so lean-miri's
  `UninhabitedEnumVariantWritten` UB never fires on a translated enum, and
  Anneal's `evalStmt` has no inhabitedness check to compare it with. -/
structure ValidEnumLayout (ty : Ty) (layouts : LayoutTable) (tagBytes : Nat)
    (variants : List (List StructFieldDesc)) : Prop where
  is_adt : ∃ defPath adtArgs, ty.kind = .adt defPath adtArgs
  not_ordering :
    ∀ defPath adtArgs, ty.kind = .adt defPath adtArgs →
      stringEq defPath "core::cmp::Ordering" = false
  layoutIdx_pos : 0 < ty.layoutIdx
  layoutIdx_lt : ty.layoutIdx < 900
  multi_variant : 2 ≤ variants.length
  tagBytes_valid :
    tagBytes = 1 ∨ tagBytes = 2 ∨ tagBytes = 4 ∨ tagBytes = 8
  variants_fit_tag : variants.length ≤ 2 ^ (8 * tagBytes)
  size_ge_tag :
    tagBytes ≤ (translateTy ty layouts).layout.size.bytes.toNat
  size_lt_4gib :
    (translateTy ty layouts).layout.size.bytes.toNat < 2 ^ 32
  align_pow2_le :
    (translateTy ty layouts).layout.align.abi.pow2 ≤ 29
  backend_memory :
    (translateTy ty layouts).layout.backendRepr = .Memory (sized := true)
  uninhabited_false :
    (translateTy ty layouts).layout.uninhabited = false
  outer_fields_tag0 :
    (translateTy ty layouts).layout.fields =
      .Arbitrary #[Miri.ABI.Size.ZERO] #[0]
  table_entry :
    ∃ tl tagValidRange rawTag rawShapes,
      layouts.lookup ty.layoutIdx = some tl ∧
      tl.variants = .multiple rawTag 0 rawShapes ∧
      rawShapes.length = variants.length ∧
      translateScalarLayout rawTag =
        .Initialized (value := .Int (translateAbiIntegerBytes tagBytes) false)
          (validRange := tagValidRange) ∧
      (∀ v, v < variants.length →
        tagValidRange.contains (BitVec.ofNat 128 v) = true) ∧
        ∃ (vars : Array Miri.ABI.VariantLayout) (hsz : vars.size = variants.length),
          (translateTy ty layouts).layout.variants =
            .Multiple
              (.Initialized
                (value := .Int (translateAbiIntegerBytes tagBytes) false)
                (validRange := tagValidRange))
              .Direct 0 vars ∧
          ∀ v (hv : v < variants.length),
            ValidEnumVariantFields layouts tagBytes
              (translateTy ty layouts).layout.size.bytes.toNat
              (vars[v]'(by omega))
              (variants[v]'hv)

namespace ValidEnumLayout

theorem isRoundtrip {ty : Ty} {layouts : LayoutTable} {tagBytes : Nat}
    {variants : List (List StructFieldDesc)}
    (h : ValidEnumLayout ty layouts tagBytes variants) :
    IsRoundtripTy ty :=
  Or.inr (Or.inr h.is_adt)

theorem encodeTyId_eq {ty : Ty} {layouts : LayoutTable} {tagBytes : Nat}
    {variants : List (List StructFieldDesc)}
    (h : ValidEnumLayout ty layouts tagBytes variants) :
    encodeTyId ty = 100 + ty.layoutIdx := by
  obtain ⟨p, a, hk⟩ := h.is_adt
  rcases ty with ⟨kind, lIdx⟩
  dsimp only at hk
  subst hk
  rfl

theorem translateTy_ty_eq {ty : Ty} {layouts : LayoutTable} {tagBytes : Nat}
    {variants : List (List StructFieldDesc)}
    (h : ValidEnumLayout ty layouts tagBytes variants) :
    (translateTy ty layouts).ty = 100 + ty.layoutIdx := by
  change encodeTyId ty = 100 + ty.layoutIdx
  exact h.encodeTyId_eq

theorem isSized_true {ty : Ty} {layouts : LayoutTable} {tagBytes : Nat}
    {variants : List (List StructFieldDesc)}
    (h : ValidEnumLayout ty layouts tagBytes variants) :
    (translateTy ty layouts).layout.isSized = true := by
  unfold Miri.ABI.LayoutData.isSized
  rw [h.backend_memory]
  rfl

theorem size_pos {ty : Ty} {layouts : LayoutTable} {tagBytes : Nat}
    {variants : List (List StructFieldDesc)}
    (h : ValidEnumLayout ty layouts tagBytes variants) :
    0 < (translateTy ty layouts).layout.size.bytes.toNat := by
  have ht := h.tagBytes_valid
  have hge := h.size_ge_tag
  rcases ht with rfl | rfl | rfl | rfl <;> omega

theorem isEnumLayout_true {ty : Ty} {layouts : LayoutTable} {tagBytes : Nat}
    {variants : List (List StructFieldDesc)}
    (h : ValidEnumLayout ty layouts tagBytes variants) :
    isEnumLayout (translateTy ty layouts) = true := by
  obtain ⟨_, _, _, _, _, _, _, _, _, vars, _, hvars, _⟩ := h.table_entry
  unfold isEnumLayout
  rw [hvars]

end ValidEnumLayout

/-- Anneal's `LayoutTable` records no per-variant inhabitedness:
`translateVariantFieldsShape` sets `uninhabited := false` for every variant of a
`.multiple` layout. So lean-miri's `isVariantUninhabited` is `false` at every
in-range variant of a translated enum layout, its
`UninhabitedEnumVariantWritten` and `UninhabitedEnumVariantRead` UB checks never
fire there, and the `vl_inhabited` field of `ValidEnumVariantFields` excludes no
translated layout. -/
theorem isVariantUninhabited_translateVariantsShape_multiple
    (lay : Miri.ABI.LayoutData) (tag : ScalarLayout) (tagField : Nat)
    (shapes : List FieldsShape)
    (hvars : lay.variants = translateVariantsShape (.multiple tag tagField shapes))
    {v : Nat} (hv : v < shapes.length) :
    lay.isVariantUninhabited v = false := by
  unfold Miri.ABI.LayoutData.isVariantUninhabited
  rw [hvars]
  simp [translateVariantsShape, translateVariantFieldsShape, hv]

/-- Static environment mapping each multi-variant enum `Ty` in `LM-2.3` to its
`(tagBytes, variants)` layout descriptor (`none` for scalar/non-enum types). -/
abbrev EnumTypeEnv :=
  Ty → Option (Nat × List (List StructFieldDesc))

/-- Empty `EnumTypeEnv` under which `StateRelLM2_3` coincides with
`StateRel`. -/
def emptyEnumTypeEnv : EnumTypeEnv := fun _ => none

/-- Memory-place correspondence for an **initialized** multi-variant enum value
`Value.aggregate v_act fieldVals` stored in a live mutable `Allocation` at
offset `0`:
* Tag slice `[0, tagBytes)` is initialized (`maskBlocksGetBit words b = true`
  and `isRangeInitialized = .ok (.ok ())`) and `readScalar` returns the tag
  scalar `msc_tag` (`ScalarRel ⟨v_act, tagBytes⟩ msc_tag`).
* For each payload field `i < (variants[v_act]).length`, either:
  - `get? fieldVals i = some (.scalar sc_i)` and the field slice
    `[f_i.offset, f_i.offset + f_i.size)` is initialized and reads back
    `msc_i` (`ScalarRel sc_i msc_i`), or
  - `get? fieldVals i = none` (e.g. a trailing field after `SetDiscriminant`
    switches from a narrower variant to a wider variant) and at least one byte
    in `[f_i.offset, f_i.offset + f_i.size)` is uninitialized in `words`, so
    reading field `i` of `v_act` raises UB in both Anneal and `lean-miri`. -/
inductive EnumMemRel
    (mach : AnnealMachine)
    (ty : Ty)
    (layouts : LayoutTable)
    (tagBytes : Nat)
    (variants : List (List StructFieldDesc))
    (v_act : Nat)
    (fieldVals : List Value)
    (mp : Miri.Interpreter.MemPlace AnnealProv) : Prop where
  | mk
      (allocId : Miri.Memory.AllocId)
      (borTag : Miri.Memory.BorTag)
      (baseAddr : UInt64)
      (localAlloc : AnnealLocalAlloc)
      (words : Array UInt64)
      (msc_tag : Miri.Memory.ScalarInt)
      (valid_enum : ValidEnumLayout ty layouts tagBytes variants)
      (active_lt : v_act < variants.length)
      (ptr_prov : mp.ptr.provenance = some (.concrete allocId borTag))
      (no_misalign : mp.misaligned = none)
      (thin_meta : mp.metadata = .none)
      (live_entry : LiveAllocEntry mach.memory.live allocId localAlloc)
      (base_lookup : mach.lookupBaseAddr allocId = some baseAddr)
      (ptr_addr_eq : mp.ptr.offset = Miri.ABI.Size.ofBytes baseAddr)
      (addr_no_overflow :
        baseAddr.toNat + (translateTy ty layouts).layout.size.bytes.toNat < 2 ^ 64)
      (mut_alloc : localAlloc.allocation.mutability = .Mut)
      (aligned_ptr :
        mp.ptr.offset.isAligned (translateTy ty layouts).layout.align.abi = .ok true)
      (byteSize_eq :
        localAlloc.allocation.byteSize = (translateTy ty layouts).layout.size)
      (alloc_len_eq :
        localAlloc.allocation.len = localAlloc.allocation.byteSize.bytes.toNat)
      (prov_empty :
        localAlloc.allocation.provenanceMap = Miri.Memory.ProvenanceMap.new)
      (mask_rel :
        InitMaskWordRel localAlloc.allocation.initializationMask
          localAlloc.allocation.byteSize words)
      (tag_scalar_rel : ScalarRel ⟨v_act, tagBytes⟩ msc_tag)
      (tag_bits_init :
        ∀ b, b < tagBytes → maskBlocksGetBit words b = true)
      (tag_range_init :
        localAlloc.allocation.initializationMask.isRangeInitialized
          (Miri.Memory.allocRange Miri.ABI.Size.ZERO
            (translateSizeBytes tagBytes)) = .ok (.ok ()))
      (tag_read :
        localAlloc.allocation.readScalar annealTargetDataLayout
          (Miri.Memory.allocRange Miri.ABI.Size.ZERO
            (translateSizeBytes tagBytes)) false =
          .ok (.fromScalarInt msc_tag))
      (payload_rel :
        ∀ (i : Nat) (hi : i < (variants[v_act]'active_lt).length),
          let f := (variants[v_act]'active_lt)[i]'hi
          (∃ sc msc,
            get? fieldVals i = some (.scalar sc) ∧
            ScalarRel sc msc ∧
            f.fieldLayout.size = translateSizeBytes sc.sizeBytes ∧
            (f.ty.kind = .bool → sc.sizeBytes = 1 ∧ (sc.bits = 0 ∨ sc.bits = 1)) ∧
            (f.ty.kind = .char → sc.sizeBytes = 4 ∧ isValidCharCode sc.bits = true) ∧
            (∀ b, f.offset.bytes.toNat ≤ b →
              b < f.offset.bytes.toNat + f.fieldLayout.size.bytes.toNat →
              maskBlocksGetBit words b = true) ∧
            localAlloc.allocation.initializationMask.isRangeInitialized
              (Miri.Memory.allocRange f.offset f.fieldLayout.size) = .ok (.ok ()) ∧
            localAlloc.allocation.readScalar annealTargetDataLayout
              (Miri.Memory.allocRange f.offset f.fieldLayout.size) false =
              .ok (.fromScalarInt msc)) ∨
          (get? fieldVals i = none ∧
            ∃ b,
              f.offset.bytes.toNat ≤ b ∧
              b < f.offset.bytes.toNat + f.fieldLayout.size.bytes.toNat ∧
              maskBlocksGetBit words b = false)) :
      EnumMemRel mach ty layouts tagBytes variants v_act fieldVals mp

/-- Memory-place correspondence for an **uninitialized** indirect enum local
(`.uninit` in Anneal, `.indirect mp` backed by an all-uninitialized mutable
stack allocation in `lean-miri`). -/
inductive UninitEnumMemRel
    (mach : AnnealMachine)
    (ty : Ty)
    (layouts : LayoutTable)
    (tagBytes : Nat)
    (variants : List (List StructFieldDesc))
    (mp : Miri.Interpreter.MemPlace AnnealProv) : Prop where
  | mk
      (allocId : Miri.Memory.AllocId)
      (borTag : Miri.Memory.BorTag)
      (baseAddr : UInt64)
      (localAlloc : AnnealLocalAlloc)
      (valid_enum : ValidEnumLayout ty layouts tagBytes variants)
      (ptr_prov : mp.ptr.provenance = some (.concrete allocId borTag))
      (no_misalign : mp.misaligned = none)
      (thin_meta : mp.metadata = .none)
      (live_entry : LiveAllocEntry mach.memory.live allocId localAlloc)
      (base_lookup : mach.lookupBaseAddr allocId = some baseAddr)
      (ptr_addr_eq : mp.ptr.offset = Miri.ABI.Size.ofBytes baseAddr)
      (addr_no_overflow :
        baseAddr.toNat + (translateTy ty layouts).layout.size.bytes.toNat < 2 ^ 64)
      (mut_alloc : localAlloc.allocation.mutability = .Mut)
      (aligned_ptr :
        mp.ptr.offset.isAligned (translateTy ty layouts).layout.align.abi = .ok true)
      (byteSize_eq :
        localAlloc.allocation.byteSize = (translateTy ty layouts).layout.size)
      (alloc_len_eq :
        localAlloc.allocation.len = localAlloc.allocation.byteSize.bytes.toNat)
      (prov_empty :
        localAlloc.allocation.provenanceMap = Miri.Memory.ProvenanceMap.new)
      (mask_uninit :
        localAlloc.allocation.initializationMask =
          Miri.Memory.InitMask.new (translateTy ty layouts).layout.size false) :
      UninitEnumMemRel mach ty layouts tagBytes variants mp

namespace EnumMemRel

theorem of_stackAlloc_other {mach : AnnealMachine} {mem' : AnnealMemory}
    {newId : Miri.Memory.AllocId}
    {alloc : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    {ty : Ty} {layouts : LayoutTable} {tagBytes : Nat}
    {variants : List (List StructFieldDesc)} {v_act : Nat}
    {fieldVals : List Value} {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hres : mach.memory.reserveAllocId = (mem', .ok newId))
    (h : EnumMemRel mach ty layouts tagBytes variants v_act fieldVals mp) :
    EnumMemRel (stackAllocMachine mach mem' newId alloc)
      ty layouts tagBytes variants v_act fieldVals mp := by
  rcases h with ⟨allocId, borTag, baseAddr, localAlloc, words, msc_tag,
    valid_enum, active_lt, ptr_prov, no_misalign, thin_meta, live_entry,
    base_lookup, ptr_addr_eq, addr_no_overflow, mut_alloc, aligned_ptr,
    byteSize_eq, alloc_len_eq, prov_empty, mask_rel, tag_scalar_rel,
    tag_bits_init, tag_range_init, tag_read, payload_rel⟩
  obtain ⟨hlive_eq, _⟩ := reserveAllocId_ok_live hres
  obtain ⟨_, _, hbase_all⟩ := stackAllocMachine_live_base alloc hres
  have hmem := live_entry.mem_toList
  have hlive' : LiveAllocEntry
      (stackAllocMachine mach mem' newId alloc).memory.live allocId localAlloc := by
    dsimp [stackAllocMachine]
    rw [hlive_eq]
    exact live_entry.of_push_other _
  exact .mk allocId borTag baseAddr localAlloc words msc_tag valid_enum active_lt
    ptr_prov no_misalign thin_meta hlive'
    ((hbase_all allocId localAlloc hmem).trans base_lookup)
    ptr_addr_eq addr_no_overflow mut_alloc aligned_ptr byteSize_eq alloc_len_eq
    prov_empty mask_rel tag_scalar_rel tag_bits_init tag_range_init tag_read
    payload_rel

theorem of_updateAlloc_ne {mach : AnnealMachine} {u : Nat}
    {updId : Miri.Memory.AllocId} {oldLa : AnnealLocalAlloc}
    {kind : Miri.Memory.MemoryKind Miri.Memory.MiriMemoryKind}
    {alloc' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    {ty : Ty} {layouts : LayoutTable} {tagBytes : Nat}
    {variants : List (List StructFieldDesc)} {v_act : Nat}
    {fieldVals : List Value} {mp : Miri.Interpreter.MemPlace AnnealProv}
    (h : EnumMemRel mach ty layouts tagBytes variants v_act fieldVals mp)
    (hu_lt : u < mach.memory.live.size)
    (hu_eq : mach.memory.live[u]'hu_lt = (updId, oldLa))
    (hne : mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId ≠ some updId) :
    EnumMemRel (updateAllocMachine mach u updId kind alloc')
      ty layouts tagBytes variants v_act fieldVals mp := by
  rcases h with ⟨allocId, borTag, baseAddr, localAlloc, words, msc_tag,
    valid_enum, active_lt, ptr_prov, no_misalign, thin_meta, live_entry,
    base_lookup, ptr_addr_eq, addr_no_overflow, mut_alloc, aligned_ptr,
    byteSize_eq, alloc_len_eq, prov_empty, mask_rel, tag_scalar_rel,
    tag_bits_init, tag_range_init, tag_read, payload_rel⟩
  have hne_id : updId ≠ allocId := by
    intro heq; apply hne; rw [ptr_prov, heq]; rfl
  exact .mk allocId borTag baseAddr localAlloc words msc_tag valid_enum active_lt
    ptr_prov no_misalign thin_meta
    (live_entry.of_set!_ne hu_lt hu_eq hne_id ⟨kind, alloc'⟩)
    base_lookup ptr_addr_eq addr_no_overflow mut_alloc aligned_ptr byteSize_eq
    alloc_len_eq prov_empty mask_rel tag_scalar_rel tag_bits_init tag_range_init
    tag_read payload_rel

theorem of_dealloc {mach : AnnealMachine}
    {v : Miri.Interpreter.LocalValue AnnealProv}
    {ty : Ty} {layouts : LayoutTable} {tagBytes : Nat}
    {variants : List (List StructFieldDesc)} {v_act : Nat}
    {fieldVals : List Value} {mp : Miri.Interpreter.MemPlace AnnealProv}
    (h : EnumMemRel mach ty layouts tagBytes variants v_act fieldVals mp)
    (hdisj : ∀ mp0, v = .live (.indirect mp0) →
      mp0.ptr.provenance.bind Miri.Memory.Provenance.getAllocId ≠
        mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId) :
    EnumMemRel { mach with memory := deallocLocalMemory mach.memory v }
      ty layouts tagBytes variants v_act fieldVals mp := by
  cases v with
  | dead => exact h
  | live op =>
    cases op with
    | immediate _ => exact h
    | indirect mp0 =>
      have hd := hdisj mp0 rfl
      cases hid : mp0.ptr.provenance.bind Miri.Memory.Provenance.getAllocId with
      | none =>
        have hmem : deallocLocalMemory mach.memory (.live (.indirect mp0)) =
            mach.memory := by
          simp [deallocLocalMemory, hid]
        rw [hmem]; exact h
      | some deadId =>
        rcases h with ⟨allocId, borTag, baseAddr, localAlloc, words, msc_tag,
          valid_enum, active_lt, ptr_prov, no_misalign, thin_meta, live_entry,
          base_lookup, ptr_addr_eq, addr_no_overflow, mut_alloc, aligned_ptr,
          byteSize_eq, alloc_len_eq, prov_empty, mask_rel, tag_scalar_rel,
          tag_bits_init, tag_range_init, tag_read, payload_rel⟩
        have hne : allocId ≠ deadId := by
          intro heq; apply hd; rw [hid, ptr_prov, heq]; rfl
        have hmem : deallocLocalMemory mach.memory (.live (.indirect mp0)) =
            { mach.memory with
              live := mach.memory.live.filter (fun entry => entry.1 != deadId) } := by
          simp [deallocLocalMemory, hid]
        rw [hmem]
        exact .mk allocId borTag baseAddr localAlloc words msc_tag valid_enum
          active_lt ptr_prov no_misalign thin_meta (live_entry.of_filter_ne hne)
          base_lookup ptr_addr_eq addr_no_overflow mut_alloc aligned_ptr
          byteSize_eq alloc_len_eq prov_empty mask_rel tag_scalar_rel
          tag_bits_init tag_range_init tag_read payload_rel

theorem of_copy_fresh {mach : AnnealMachine} {mem' : AnnealMemory}
    {id : Miri.Memory.AllocId}
    {ty : Ty} {layouts : LayoutTable} {tagBytes : Nat}
    {variants : List (List StructFieldDesc)} {v_act : Nat}
    {fieldVals : List Value} {srcMp : Miri.Interpreter.MemPlace AnnealProv}
    {srcId : Miri.Memory.AllocId} {srcLocal : AnnealLocalAlloc}
    (h : EnumMemRel mach ty layouts tagBytes variants v_act fieldVals srcMp)
    {tag_s : Miri.Memory.BorTag}
    (hprov_s : srcMp.ptr.provenance = some (.concrete srcId tag_s))
    (hlive_s : LiveAllocEntry mach.memory.live srcId srcLocal)
    (hfresh : mem'.live.any (fun entry => entry.1 == id) = false)
    (hovf : (annealStackBaseAddr id).toNat +
      (translateTy ty layouts).layout.size.bytes.toNat < 2 ^ 64) :
    EnumMemRel
      (stackAllocMachine mach mem' id
        (copyWholeStructAllocation srcLocal.allocation none))
      ty layouts tagBytes variants v_act fieldVals (stackAllocPlace id) := by
  rcases h with ⟨allocId, borTag, baseAddr, localAlloc, words, msc_tag,
    valid_enum, active_lt, ptr_prov, _, _, live_entry, _, _, _, _, _,
    byteSize_eq, alloc_len_eq, prov_empty, mask_rel, tag_scalar_rel,
    tag_bits_init, tag_range_init, tag_read, payload_rel⟩
  rw [ptr_prov] at hprov_s
  injection hprov_s with hprov_eq
  injection hprov_eq with hid_eq _
  subst hid_eq
  have hla_eq : srcLocal = localAlloc := by
    have h1 := hlive_s.1
    rw [live_entry.1] at h1
    injection h1 with hp
    exact (Prod.mk.inj hp).2.symm
  subst hla_eq
  let alloc' := copyWholeStructAllocation srcLocal.allocation none
  obtain ⟨hmut', hbs', hlen', hpmap', hmask_eq, hread_eq⟩ :=
    copyWholeStructAllocation_props srcLocal.allocation none
  refine .mk id Miri.Memory.BorTag.one (annealStackBaseAddr id)
    ⟨.stack, alloc'⟩ words msc_tag valid_enum active_lt rfl rfl rfl
    (LiveAllocEntry.of_push_fresh_self _ hfresh)
    (lookupBaseAddr_stackAllocMachine_self _ _ _ _)
    rfl hovf hmut'
    (annealStackBaseAddr_isAligned id _ valid_enum.align_pow2_le)
    (hbs'.trans byteSize_eq) (by rw [hlen', hbs']; exact alloc_len_eq)
    (hpmap'.trans prov_empty) (by rw [hmask_eq, hbs']; exact mask_rel)
    tag_scalar_rel tag_bits_init
    (by dsimp; rw [hmask_eq]; exact tag_range_init)
    (by dsimp; rw [hread_eq]; exact tag_read) ?_
  intro i hi
  rcases payload_rel i hi with
    ⟨sc, msc, hfv, hrel, hsz, hb, hc, hbits, hinit, hread⟩ | hnone
  · exact Or.inl ⟨sc, msc, hfv, hrel, hsz, hb, hc, hbits,
      by dsimp; rw [hmask_eq]; exact hinit,
      by dsimp; rw [hread_eq]; exact hread⟩
  · exact Or.inr hnone

theorem of_copy_overwrite {mach : AnnealMachine} {u : Nat}
    {destId : Miri.Memory.AllocId} {destBase : UInt64}
    {destLocal : AnnealLocalAlloc}
    {destMp : Miri.Interpreter.MemPlace AnnealProv}
    {ty : Ty} {layouts : LayoutTable} {tagBytes : Nat}
    {variants : List (List StructFieldDesc)} {v_act : Nat}
    {fieldVals : List Value} {srcMp : Miri.Interpreter.MemPlace AnnealProv}
    {srcId : Miri.Memory.AllocId} {srcLocal : AnnealLocalAlloc}
    (h : EnumMemRel mach ty layouts tagBytes variants v_act fieldVals srcMp)
    {tag_s : Miri.Memory.BorTag}
    (hprov_s : srcMp.ptr.provenance = some (.concrete srcId tag_s))
    (hlive_s : LiveAllocEntry mach.memory.live srcId srcLocal)
    {tag_d : Miri.Memory.BorTag}
    (hprov_d : destMp.ptr.provenance = some (.concrete destId tag_d))
    (hmis_d : destMp.misaligned = none)
    (hmeta_d : destMp.metadata = .none)
    (hlive_d : LiveAllocEntry mach.memory.live destId destLocal)
    (hu_lt : u < mach.memory.live.size)
    (hfidx_d : mach.memory.live.findIdx? (fun (k, _) => k == destId) = some u)
    (hbase_d : mach.lookupBaseAddr destId = some destBase)
    (hptr_d : destMp.ptr.offset = Miri.ABI.Size.ofBytes destBase)
    (hovf_d : destBase.toNat +
      (translateTy ty layouts).layout.size.bytes.toNat < 2 ^ 64)
    (halign_d : destMp.ptr.offset.isAligned
      (translateTy ty layouts).layout.align.abi = .ok true) :
    EnumMemRel
      (updateAllocMachine mach u destId destLocal.kind
        (copyWholeStructAllocation srcLocal.allocation
          destLocal.allocation.extra))
      ty layouts tagBytes variants v_act fieldVals destMp := by
  rcases h with ⟨allocId, borTag, baseAddr, localAlloc, words, msc_tag,
    valid_enum, active_lt, ptr_prov, _, _, live_entry, _, _, _, _, _,
    byteSize_eq, alloc_len_eq, prov_empty, mask_rel, tag_scalar_rel,
    tag_bits_init, tag_range_init, tag_read, payload_rel⟩
  rw [ptr_prov] at hprov_s
  injection hprov_s with hprov_eq
  injection hprov_eq with hid_eq _
  subst hid_eq
  have hla_eq : srcLocal = localAlloc := by
    have h1 := hlive_s.1
    rw [live_entry.1] at h1
    injection h1 with hp
    exact (Prod.mk.inj hp).2.symm
  subst hla_eq
  let alloc' := copyWholeStructAllocation srcLocal.allocation
    destLocal.allocation.extra
  obtain ⟨hmut', hbs', hlen', hpmap', hmask_eq, hread_eq⟩ :=
    copyWholeStructAllocation_props srcLocal.allocation
      destLocal.allocation.extra
  have hlive_self : LiveAllocEntry
      (mach.memory.live.set! u (destId, ⟨destLocal.kind, alloc'⟩))
      destId ⟨destLocal.kind, alloc'⟩ :=
    hlive_d.of_set!_self hu_lt hfidx_d ⟨destLocal.kind, alloc'⟩
  refine .mk destId tag_d destBase ⟨destLocal.kind, alloc'⟩ words msc_tag
    valid_enum active_lt hprov_d hmis_d hmeta_d hlive_self hbase_d hptr_d
    hovf_d hmut' halign_d
    (hbs'.trans byteSize_eq) (by rw [hlen', hbs']; exact alloc_len_eq)
    (hpmap'.trans prov_empty) (by rw [hmask_eq, hbs']; exact mask_rel)
    tag_scalar_rel tag_bits_init
    (by dsimp; rw [hmask_eq]; exact tag_range_init)
    (by dsimp; rw [hread_eq]; exact tag_read) ?_
  intro i hi
  rcases payload_rel i hi with
    ⟨sc, msc, hfv, hrel, hsz, hb, hc, hbits, hinit, hread⟩ | hnone
  · exact Or.inl ⟨sc, msc, hfv, hrel, hsz, hb, hc, hbits,
      by dsimp; rw [hmask_eq]; exact hinit,
      by dsimp; rw [hread_eq]; exact hread⟩
  · exact Or.inr hnone

end EnumMemRel

namespace UninitEnumMemRel

theorem of_stackAlloc_other {mach : AnnealMachine} {mem' : AnnealMemory}
    {newId : Miri.Memory.AllocId}
    {alloc : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    {ty : Ty} {layouts : LayoutTable} {tagBytes : Nat}
    {variants : List (List StructFieldDesc)}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hres : mach.memory.reserveAllocId = (mem', .ok newId))
    (h : UninitEnumMemRel mach ty layouts tagBytes variants mp) :
    UninitEnumMemRel (stackAllocMachine mach mem' newId alloc)
      ty layouts tagBytes variants mp := by
  rcases h with ⟨allocId, borTag, baseAddr, localAlloc, valid_enum, ptr_prov,
    no_misalign, thin_meta, live_entry, base_lookup, ptr_addr_eq,
    addr_no_overflow, mut_alloc, aligned_ptr, byteSize_eq, alloc_len_eq,
    prov_empty, mask_uninit⟩
  obtain ⟨hlive_eq, _⟩ := reserveAllocId_ok_live hres
  obtain ⟨_, _, hbase_all⟩ := stackAllocMachine_live_base alloc hres
  have hmem := live_entry.mem_toList
  have hlive' : LiveAllocEntry
      (stackAllocMachine mach mem' newId alloc).memory.live allocId localAlloc := by
    dsimp [stackAllocMachine]
    rw [hlive_eq]
    exact live_entry.of_push_other _
  exact .mk allocId borTag baseAddr localAlloc valid_enum ptr_prov no_misalign
    thin_meta hlive' ((hbase_all allocId localAlloc hmem).trans base_lookup)
    ptr_addr_eq addr_no_overflow mut_alloc aligned_ptr byteSize_eq alloc_len_eq
    prov_empty mask_uninit

theorem of_updateAlloc_ne {mach : AnnealMachine} {u : Nat}
    {updId : Miri.Memory.AllocId} {oldLa : AnnealLocalAlloc}
    {kind : Miri.Memory.MemoryKind Miri.Memory.MiriMemoryKind}
    {alloc' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    {ty : Ty} {layouts : LayoutTable} {tagBytes : Nat}
    {variants : List (List StructFieldDesc)}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    (h : UninitEnumMemRel mach ty layouts tagBytes variants mp)
    (hu_lt : u < mach.memory.live.size)
    (hu_eq : mach.memory.live[u]'hu_lt = (updId, oldLa))
    (hne : mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId ≠ some updId) :
    UninitEnumMemRel (updateAllocMachine mach u updId kind alloc')
      ty layouts tagBytes variants mp := by
  rcases h with ⟨allocId, borTag, baseAddr, localAlloc, valid_enum, ptr_prov,
    no_misalign, thin_meta, live_entry, base_lookup, ptr_addr_eq,
    addr_no_overflow, mut_alloc, aligned_ptr, byteSize_eq, alloc_len_eq,
    prov_empty, mask_uninit⟩
  have hne_id : updId ≠ allocId := by
    intro heq; apply hne; rw [ptr_prov, heq]; rfl
  exact .mk allocId borTag baseAddr localAlloc valid_enum ptr_prov no_misalign
    thin_meta (live_entry.of_set!_ne hu_lt hu_eq hne_id ⟨kind, alloc'⟩)
    base_lookup ptr_addr_eq addr_no_overflow mut_alloc aligned_ptr byteSize_eq
    alloc_len_eq prov_empty mask_uninit

theorem of_dealloc {mach : AnnealMachine}
    {v : Miri.Interpreter.LocalValue AnnealProv}
    {ty : Ty} {layouts : LayoutTable} {tagBytes : Nat}
    {variants : List (List StructFieldDesc)}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    (h : UninitEnumMemRel mach ty layouts tagBytes variants mp)
    (hdisj : ∀ mp0, v = .live (.indirect mp0) →
      mp0.ptr.provenance.bind Miri.Memory.Provenance.getAllocId ≠
        mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId) :
    UninitEnumMemRel { mach with memory := deallocLocalMemory mach.memory v }
      ty layouts tagBytes variants mp := by
  cases v with
  | dead => exact h
  | live op =>
    cases op with
    | immediate _ => exact h
    | indirect mp0 =>
      have hd := hdisj mp0 rfl
      cases hid : mp0.ptr.provenance.bind Miri.Memory.Provenance.getAllocId with
      | none =>
        have hmem : deallocLocalMemory mach.memory (.live (.indirect mp0)) =
            mach.memory := by
          simp [deallocLocalMemory, hid]
        rw [hmem]; exact h
      | some deadId =>
        rcases h with ⟨allocId, borTag, baseAddr, localAlloc, valid_enum,
          ptr_prov, no_misalign, thin_meta, live_entry, base_lookup, ptr_addr_eq,
          addr_no_overflow, mut_alloc, aligned_ptr, byteSize_eq, alloc_len_eq,
          prov_empty, mask_uninit⟩
        have hne : allocId ≠ deadId := by
          intro heq; apply hd; rw [hid, ptr_prov, heq]; rfl
        have hmem : deallocLocalMemory mach.memory (.live (.indirect mp0)) =
            { mach.memory with
              live := mach.memory.live.filter (fun entry => entry.1 != deadId) } := by
          simp [deallocLocalMemory, hid]
        rw [hmem]
        exact .mk allocId borTag baseAddr localAlloc valid_enum ptr_prov
          no_misalign thin_meta (live_entry.of_filter_ne hne) base_lookup
          ptr_addr_eq addr_no_overflow mut_alloc aligned_ptr byteSize_eq
          alloc_len_eq prov_empty mask_uninit

end UninitEnumMemRel

/-- Local storage correspondence for `LM-2.3`, parameterized by `EnumTypeEnv`:
* When `env decl.ty = none`, delegates directly to `LocalRel`.
* When `env decl.ty = some (tagBytes, variants)`, relates:
  - `.dead` ↔ `⟨.dead, cachedLayout⟩` (`enumDead`),
  - `.uninit` ↔ `⟨.live (.immediate .uninit), cachedLayout⟩` (`enumUninitImm`)
    or uninitialized stack allocation (`enumUninitInd` via `UninitEnumMemRel`),
  - `.init (.aggregate v_act fieldVals)` ↔ initialized indirect stack allocation
    (`enumInd` via `EnumMemRel`). -/
inductive LocalRelLM2_3
    (env : EnumTypeEnv)
    (mach : AnnealMachine)
    (decl : LocalDecl)
    (layouts : LayoutTable) :
    LocalSlot →
    Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout →
    Prop where
  | base (slot : LocalSlot)
      (mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout) :
      env decl.ty = none →
      LocalRel mach decl layouts slot mls →
      LocalRelLM2_3 env mach decl layouts slot mls
  | enumDead (tagBytes : Nat) (variants : List (List StructFieldDesc))
      (cachedLayout : Option Miri.Interpreter.LocalLayout) :
      env decl.ty = some (tagBytes, variants) →
      ValidEnumLayout decl.ty layouts tagBytes variants →
      (∀ l ∈ cachedLayout, l = translateTy decl.ty layouts) →
      LocalRelLM2_3 env mach decl layouts .dead ⟨.dead, cachedLayout⟩
  | enumUninitImm (tagBytes : Nat) (variants : List (List StructFieldDesc))
      (cachedLayout : Option Miri.Interpreter.LocalLayout) :
      env decl.ty = some (tagBytes, variants) →
      ValidEnumLayout decl.ty layouts tagBytes variants →
      (∀ l ∈ cachedLayout, l = translateTy decl.ty layouts) →
      LocalRelLM2_3 env mach decl layouts .uninit
        ⟨.live (.immediate .uninit), cachedLayout⟩
  | enumUninitInd (tagBytes : Nat) (variants : List (List StructFieldDesc))
      (mp : Miri.Interpreter.MemPlace AnnealProv)
      (cachedLayout : Option Miri.Interpreter.LocalLayout) :
      env decl.ty = some (tagBytes, variants) →
      (∀ l ∈ cachedLayout, l = translateTy decl.ty layouts) →
      UninitEnumMemRel mach decl.ty layouts tagBytes variants mp →
      LocalRelLM2_3 env mach decl layouts .uninit
        ⟨.live (.indirect mp), cachedLayout⟩
  | enumInd (tagBytes : Nat) (variants : List (List StructFieldDesc))
      (v_act : Nat) (fieldVals : List Value)
      (mp : Miri.Interpreter.MemPlace AnnealProv)
      (cachedLayout : Option Miri.Interpreter.LocalLayout) :
      env decl.ty = some (tagBytes, variants) →
      (∀ l ∈ cachedLayout, l = translateTy decl.ty layouts) →
      EnumMemRel mach decl.ty layouts tagBytes variants v_act fieldVals mp →
      LocalRelLM2_3 env mach decl layouts (.init (.aggregate v_act fieldVals))
        ⟨.live (.indirect mp), cachedLayout⟩

namespace LocalRelLM2_3

theorem cachedLayout_eq {env : EnumTypeEnv} {mach : AnnealMachine}
    {decl : LocalDecl} {layouts : LayoutTable} {slot : LocalSlot}
    {mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout}
    (h : LocalRelLM2_3 env mach decl layouts slot mls) :
    ∀ l ∈ mls.layout, l = translateTy decl.ty layouts := by
  cases h with
  | base _ _ _ hb => exact hb.cachedLayout_eq
  | enumDead _ _ _ _ _ hc => exact hc
  | enumUninitImm _ _ _ _ _ hc => exact hc
  | enumUninitInd _ _ _ _ _ hc _ => exact hc
  | enumInd _ _ _ _ _ _ _ hc _ => exact hc

theorem layout_eq {env : EnumTypeEnv} {mach : AnnealMachine}
    {decl : LocalDecl} {layouts : LayoutTable} {slot : LocalSlot}
    {mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout}
    (h : LocalRelLM2_3 env mach decl layouts slot mls) :
    ∀ l, mls.layout = some l → l = translateTy decl.ty layouts :=
  fun l hl => h.cachedLayout_eq l (Option.mem_def.mpr hl)

theorem cache_layout {env : EnumTypeEnv} {mach : AnnealMachine}
    {decl : LocalDecl} {layouts : LayoutTable} {slot : LocalSlot}
    {mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout}
    (h : LocalRelLM2_3 env mach decl layouts slot mls) :
    LocalRelLM2_3 env mach decl layouts slot
      { mls with layout := some (translateTy decl.ty layouts) } := by
  have hc : ∀ l ∈ (some (translateTy decl.ty layouts)),
      l = translateTy decl.ty layouts :=
    fun _ hl => (Option.some.inj (Option.mem_def.mp hl)).symm
  cases h with
  | base _ _ henv hb =>
    refine .base _ _ henv ?_
    cases hb with
    | dead _ _ => exact .dead _ hc
    | immediate _ i _ _ hv => exact .immediate slot i _ hc hv
    | indirect _ mp _ _ hne hmp => exact .indirect slot mp _ hc hne hmp
  | enumDead tb vs _ henv hv _ => exact .enumDead tb vs _ henv hv hc
  | enumUninitImm tb vs _ henv hv _ => exact .enumUninitImm tb vs _ henv hv hc
  | enumUninitInd tb vs mp _ henv _ hmp => exact .enumUninitInd tb vs mp _ henv hc hmp
  | enumInd tb vs va fv mp _ henv _ hmp => exact .enumInd tb vs va fv mp _ henv hc hmp

theorem allocLive {env : EnumTypeEnv} {mach : AnnealMachine}
    {decl : LocalDecl} {layouts : LayoutTable} {slot : LocalSlot}
    {mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout}
    (h : LocalRelLM2_3 env mach decl layouts slot mls) :
    LocalAllocLive mach.memory mls.value := by
  cases h with
  | base _ _ _ hb => exact hb.allocLive
  | enumDead _ _ _ _ _ _ => intro mp hv; cases hv
  | enumUninitImm _ _ _ _ _ _ => intro mp hv; cases hv
  | enumUninitInd _ _ mp _ _ _ hmp =>
    intro mp' hv
    injection hv with hv; injection hv with hv; subst hv
    rcases hmp with ⟨allocId, _, _, _, _, hprov, _, _, hlive, _, _, _, _, _, _, _, _, _⟩
    exact ⟨allocId, by rw [hprov]; rfl, hlive.any_true⟩
  | enumInd _ _ _ _ mp _ _ _ hmp =>
    intro mp' hv
    injection hv with hv; injection hv with hv; subst hv
    rcases hmp with ⟨allocId, _, _, _, _, _, _, _, hprov, _, _, hlive, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
    exact ⟨allocId, by rw [hprov]; rfl, hlive.any_true⟩

theorem of_stackAlloc_other {env : EnumTypeEnv} {mach : AnnealMachine}
    {mem' : AnnealMemory} {newId : Miri.Memory.AllocId}
    {alloc : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    {decl : LocalDecl} {layouts : LayoutTable} {slot : LocalSlot}
    {mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout}
    (hres : mach.memory.reserveAllocId = (mem', .ok newId))
    (h : LocalRelLM2_3 env mach decl layouts slot mls) :
    LocalRelLM2_3 env (stackAllocMachine mach mem' newId alloc)
      decl layouts slot mls := by
  obtain ⟨hlive, _, hbase⟩ := stackAllocMachine_live_base alloc hres
  cases h with
  | base _ _ henv hb => exact .base slot mls henv (hb.of_live_base hlive hbase)
  | enumDead tb vs c henv hv hc => exact .enumDead tb vs c henv hv hc
  | enumUninitImm tb vs c henv hv hc => exact .enumUninitImm tb vs c henv hv hc
  | enumUninitInd tb vs mp c henv hc hmp =>
    exact .enumUninitInd tb vs mp c henv hc (hmp.of_stackAlloc_other hres)
  | enumInd tb vs va fv mp c henv hc hmp =>
    exact .enumInd tb vs va fv mp c henv hc (hmp.of_stackAlloc_other hres)

theorem of_updateAlloc_ne {env : EnumTypeEnv} {mach : AnnealMachine}
    {u : Nat} {updId : Miri.Memory.AllocId} {oldLa : AnnealLocalAlloc}
    {kind : Miri.Memory.MemoryKind Miri.Memory.MiriMemoryKind}
    {alloc' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    {decl : LocalDecl} {layouts : LayoutTable} {slot : LocalSlot}
    {mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout}
    (h : LocalRelLM2_3 env mach decl layouts slot mls)
    (hu_lt : u < mach.memory.live.size)
    (hu_eq : mach.memory.live[u]'hu_lt = (updId, oldLa))
    (hdisj : ∀ mp', mls.value = .live (.indirect mp') →
      mp'.ptr.provenance.bind Miri.Memory.Provenance.getAllocId ≠ some updId) :
    LocalRelLM2_3 env (updateAllocMachine mach u updId kind alloc')
      decl layouts slot mls := by
  cases h with
  | base _ _ henv hb =>
    refine .base slot mls henv ?_
    cases hb with
    | dead c hc => exact .dead c hc
    | immediate _ i c hc hv => exact .immediate slot i c hc hv
    | indirect _ mp c hc hne hmp =>
      refine .indirect slot mp c hc hne ?_
      cases hmp with
      | mk allocId tag baseAddr relOffset la hprov hmis hmeta hmem hbase hovf
          hptr hmut halign hbnd huninit hval hsc harr =>
        have hne_id : updId ≠ allocId := by
          intro heq; apply hdisj mp rfl; rw [hprov, heq]; rfl
        have hmem' : (allocId, la) ∈
            (updateAllocMachine mach u updId kind alloc').memory.live.toList := by
          dsimp [updateAllocMachine]
          rw [Array.toList_setIfInBounds]
          obtain ⟨j, hj, hget_j⟩ := List.mem_iff_getElem.mp hmem
          have hju : j ≠ u := by
            intro rfl
            simp only [Array.getElem_toList] at hget_j
            rw [hu_eq] at hget_j
            injection hget_j with hid_eq
            exact hne_id hid_eq
          have hj_set :
              j < (mach.memory.live.toList.set u (updId, ⟨kind, alloc'⟩)).length := by
            rw [List.length_set]; exact hj
          have hget_set :
              (mach.memory.live.toList.set u (updId, ⟨kind, alloc'⟩))[j]'hj_set =
              (allocId, la) := by
            rw [List.getElem_set_ne (Ne.symm hju)]; exact hget_j
          rw [← hget_set]
          exact List.getElem_mem hj_set
        exact .mk allocId tag baseAddr relOffset la hprov hmis hmeta hmem' hbase
          hovf hptr hmut halign hbnd huninit hval hsc harr
  | enumDead tb vs c henv hv hc => exact .enumDead tb vs c henv hv hc
  | enumUninitImm tb vs c henv hv hc => exact .enumUninitImm tb vs c henv hv hc
  | enumUninitInd tb vs mp c henv hc hmp =>
    exact .enumUninitInd tb vs mp c henv hc
      (hmp.of_updateAlloc_ne hu_lt hu_eq (hdisj mp rfl))
  | enumInd tb vs va fv mp c henv hc hmp =>
    exact .enumInd tb vs va fv mp c henv hc
      (hmp.of_updateAlloc_ne hu_lt hu_eq (hdisj mp rfl))

theorem of_dealloc {env : EnumTypeEnv} {mach : AnnealMachine}
    {v : Miri.Interpreter.LocalValue AnnealProv}
    {decl : LocalDecl} {layouts : LayoutTable} {slot : LocalSlot}
    {mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout}
    (h : LocalRelLM2_3 env mach decl layouts slot mls)
    (hdisj : ∀ mp mp', v = .live (.indirect mp) →
      mls.value = .live (.indirect mp') →
      mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId ≠
        mp'.ptr.provenance.bind Miri.Memory.Provenance.getAllocId) :
    LocalRelLM2_3 env { mach with memory := deallocLocalMemory mach.memory v }
      decl layouts slot mls := by
  cases h with
  | base _ _ henv hb => exact .base slot mls henv (hb.of_dealloc hdisj)
  | enumDead tb vs c henv hv hc => exact .enumDead tb vs c henv hv hc
  | enumUninitImm tb vs c henv hv hc => exact .enumUninitImm tb vs c henv hv hc
  | enumUninitInd tb vs mp c henv hc hmp =>
    exact .enumUninitInd tb vs mp c henv hc
      (hmp.of_dealloc fun mp0 hv0 => hdisj mp0 mp hv0 rfl)
  | enumInd tb vs va fv mp c henv hc hmp =>
    exact .enumInd tb vs va fv mp c henv hc
      (hmp.of_dealloc fun mp0 hv0 => hdisj mp0 mp hv0 rfl)

end LocalRelLM2_3

/-- Byte-level uninitializedness witness for byte `b` of enum local `localId` in
`m`: when `localId` is backed by indirect stack allocation `mp`, byte `b` has
`initializationMask.get (Size.ofBytes b) = .ok false` (established on all
non-payload bytes upon fresh enum aggregate construction and preserved across
`SetDiscriminant` and unrelated steps). -/
def EnumLocalByteUninit (m : AnnealStepState) (localId : Nat) (b : Nat) : Prop :=
  ∀ topFrame mp c allocId borTag localAlloc,
    m.stack.frames = #[topFrame] →
    topFrame.locals[localId]? = some ⟨.live (.indirect mp), c⟩ →
    mp.ptr.provenance = some (.concrete allocId borTag) →
    m.machine.memory.live.find? (fun (k, _) => k == allocId) =
      some (allocId, localAlloc) →
    localAlloc.allocation.initializationMask.get
      (Miri.ABI.Size.ofBytes (UInt64.ofNat b)) = .ok false

theorem EnumLocalByteUninit.of_cache_layout {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {localId idx : Nat} {hlt : idx < topFrame.locals.size}
    {lay : Miri.Interpreter.LocalLayout} {b : Nat}
    (hframes : m.stack.frames = #[topFrame])
    (h : EnumLocalByteUninit m localId b) :
    EnumLocalByteUninit
      { m with stack := ⟨#[cacheFrameLocalLayout topFrame idx hlt lay]⟩ }
      localId b := by
  intro tf' mp c allocId borTag localAlloc hf' hloc' hprov hfind
  injection hf' with hf_arr
  injection hf_arr with htf_eq
  subst htf_eq
  dsimp [cacheFrameLocalLayout] at hloc'
  by_cases heq : idx = localId
  · subst heq
    rw [Array.getElem?_set_self hlt] at hloc'
    injection hloc' with hls_eq
    have hval : (topFrame.locals[idx]'hlt).value = .live (.indirect mp) := by
      simpa using congrArg Miri.Interpreter.LocalState.value hls_eq
    have hloc0 : topFrame.locals[idx]? =
        some ⟨.live (.indirect mp), (topFrame.locals[idx]'hlt).layout⟩ := by
      rw [Array.getElem?_eq_getElem hlt]
      cases hls : topFrame.locals[idx]'hlt
      rw [hls] at hval; dsimp at hval ⊢; subst hval; rfl
    exact h topFrame mp _ allocId borTag localAlloc hframes hloc0 hprov hfind
  · simp only [Array.getElem?_set, heq, ↓reduceIte] at hloc'
    exact h topFrame mp c allocId borTag localAlloc hframes hloc' hprov hfind

theorem EnumLocalByteUninit.of_replace_other {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {localId otherIdx : Nat} {hlt : otherIdx < topFrame.locals.size}
    {newLs : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout}
    {b : Nat}
    (hne : otherIdx ≠ localId)
    (hframes : m.stack.frames = #[topFrame])
    (h : EnumLocalByteUninit m localId b) :
    EnumLocalByteUninit
      { m with stack := ⟨#[{ topFrame with locals := topFrame.locals.set otherIdx newLs hlt }]⟩ }
      localId b := by
  intro tf' mp c allocId borTag localAlloc hf' hloc' hprov hfind
  injection hf' with hf_arr
  injection hf_arr with htf_eq
  subst htf_eq
  dsimp at hloc'
  simp only [Array.getElem?_set, hne, ↓reduceIte] at hloc'
  exact h topFrame mp c allocId borTag localAlloc hframes hloc' hprov hfind

theorem EnumLocalByteUninit.of_dealloc_other {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {localId otherIdx : Nat} {hlt : otherIdx < topFrame.locals.size}
    {newLs : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout}
    {b : Nat}
    (hne : otherIdx ≠ localId)
    (hframes : m.stack.frames = #[topFrame])
    (h : EnumLocalByteUninit m localId b) :
    EnumLocalByteUninit
      { stack := ⟨#[{ topFrame with
            locals := topFrame.locals.set otherIdx newLs hlt }]⟩
        machine := { m.machine with
          memory := deallocLocalMemory m.machine.memory
            (topFrame.locals[otherIdx]'hlt).value } }
      localId b := by
  intro tf' mp c allocId borTag localAlloc hf' hloc' hprov hfind
  injection hf' with hf_arr
  injection hf_arr with htf_eq
  subst htf_eq
  dsimp at hloc' hfind
  simp only [Array.getElem?_set, hne, ↓reduceIte] at hloc'
  have hfind_orig :
      m.machine.memory.live.find? (fun (k, _) => k == allocId) =
        some (allocId, localAlloc) := by
    cases hv : (topFrame.locals[otherIdx]'hlt).value with
    | dead =>
      rw [hv] at hfind; exact hfind
    | live op =>
      cases op with
      | immediate _ =>
        rw [hv] at hfind; exact hfind
      | indirect mp0 =>
        rw [hv] at hfind
        cases hid : mp0.ptr.provenance.bind Miri.Memory.Provenance.getAllocId with
        | none =>
          have hmem : deallocLocalMemory m.machine.memory (.live (.indirect mp0)) =
              m.machine.memory := by
            simp [deallocLocalMemory, hid]
          rw [hmem] at hfind; exact hfind
        | some deadId =>
          have hmem : deallocLocalMemory m.machine.memory (.live (.indirect mp0)) =
              { m.machine.memory with
                live := m.machine.memory.live.filter
                  (fun entry => entry.1 != deadId) } := by
            simp [deallocLocalMemory, hid]
          rw [hmem] at hfind
          dsimp at hfind
          rw [← Array.find?_toList, Array.toList_filter,
            List.find?_filter] at hfind
          obtain ⟨hmem_f, _⟩ := List.find?_eq_some_iff_append.mp hfind
          have hne_id : allocId ≠ deadId :=
            bne_iff_ne.mp (of_decide_eq_true hmem_f).1
          have hp_imp : ∀ x : Miri.Memory.AllocId × AnnealLocalAlloc,
              decide ((x.1 != deadId) = true ∧
                ((fun (k, _) => k == allocId) x) = true) =
              (fun (k, _) => k == allocId) x := by
            rintro ⟨k, la⟩
            by_cases hk : k == allocId
            · have hk_eq : k = allocId := beq_iff_eq.mp hk
              subst hk_eq
              simp [bne_iff_ne, hne_id]
            · simp [hk]
          have hfun_eq :
              (fun x : Miri.Memory.AllocId × AnnealLocalAlloc =>
                decide ((x.1 != deadId) = true ∧
                  ((fun (k, _) => k == allocId) x) = true)) =
              (fun (k, _) => k == allocId) := funext hp_imp
          rw [hfun_eq, Array.find?_toList] at hfind
          exact hfind
  exact h topFrame mp c allocId borTag localAlloc hframes hloc' hprov hfind_orig

/-- Frame correspondence for `LM-2.3`, parameterized by `EnumTypeEnv`. -/
structure FrameRelLM2_3
    (body : CapturedMir)
    (env : EnumTypeEnv)
    (mach : AnnealMachine)
    (af : StackFrame)
    (mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit) :
    Prop where
  body_eq : mf.body = translateBody body
  location_eq : mf.location = .mir ⟨af.blockIdx, af.stmtIdx⟩
  af_locals_len : length af.locals = length body.localDecls
  mf_locals_size : mf.locals.size = length body.localDecls
  locals_rel :
    ∀ (idx : Nat) (decl : LocalDecl) (slot : LocalSlot)
      (mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout),
      get? body.localDecls idx = some decl →
      get? af.locals idx = some slot →
      mf.locals[idx]? = some mls →
      LocalRelLM2_3 env mach decl body.layouts slot mls

namespace FrameRelLM2_3

theorem lookup_local {body : CapturedMir} {env : EnumTypeEnv}
    {mach : AnnealMachine} {af : StackFrame}
    {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (h : FrameRelLM2_3 body env mach af mf)
    {idx : Nat} {decl : LocalDecl}
    (hdecl : get? body.localDecls idx = some decl) :
    ∃ (slot : LocalSlot)
      (mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout)
      (hlt : idx < mf.locals.size),
      get? af.locals idx = some slot ∧
      mf.locals[idx]'hlt = mls ∧
      LocalRelLM2_3 env mach decl body.layouts slot mls := by
  have hidx_decls : idx < length body.localDecls := by
    unfold get? at hdecl; unfold length
    exact (List.getElem?_eq_some_iff.mp hdecl).1
  have hidx_af : idx < af.locals.length := by
    have hlen := h.af_locals_len
    unfold length at hlen hidx_decls
    omega
  have hlt : idx < mf.locals.size := by
    rw [h.mf_locals_size]; exact hidx_decls
  have haf_get : get? af.locals idx = some (af.locals[idx]'hidx_af) := by
    unfold get?; exact List.getElem?_eq_getElem hidx_af
  have hmf_get : mf.locals[idx]? = some (mf.locals[idx]'hlt) :=
    Array.getElem?_eq_getElem hlt
  exact ⟨af.locals[idx]'hidx_af, mf.locals[idx]'hlt, hlt, haf_get, rfl,
    h.locals_rel idx decl _ _ hdecl haf_get hmf_get⟩

theorem cache_local_layout {body : CapturedMir} {env : EnumTypeEnv}
    {mach : AnnealMachine} {af : StackFrame}
    {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (h : FrameRelLM2_3 body env mach af mf)
    {idx : Nat} {decl : LocalDecl}
    (hdecl : get? body.localDecls idx = some decl)
    (hlt : idx < mf.locals.size) :
    FrameRelLM2_3 body env mach af
      (cacheFrameLocalLayout mf idx hlt (translateTy decl.ty body.layouts)) := by
  refine ⟨h.body_eq, h.location_eq, h.af_locals_len, ?_, ?_⟩
  · dsimp [cacheFrameLocalLayout]; rw [Array.size_set]; exact h.mf_locals_size
  · intro j d s mls hd hs hm
    dsimp [cacheFrameLocalLayout] at hm
    by_cases hij : idx = j
    · subst hij
      rw [hdecl] at hd
      injection hd with hd_eq; subst hd_eq
      rw [Array.getElem?_set_self hlt] at hm
      injection hm with hm_eq; subst hm_eq
      have hmf_old : mf.locals[idx]? = some (mf.locals[idx]'hlt) :=
        Array.getElem?_eq_getElem hlt
      exact (h.locals_rel idx decl s _ hdecl hs hmf_old).cache_layout
    · simp only [Array.getElem?_set, hij, ↓reduceIte] at hm
      exact h.locals_rel j d s mls hd hs hm

theorem update_local {body : CapturedMir} {env : EnumTypeEnv}
    {mach : AnnealMachine} {af : StackFrame}
    {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (h : FrameRelLM2_3 body env mach af mf)
    {idx : Nat} {decl : LocalDecl} {newSlot : LocalSlot}
    {newMls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout}
    {locals' : List LocalSlot}
    (hdecl : get? body.localDecls idx = some decl)
    (hset : set? af.locals idx newSlot = some locals')
    (hlt : idx < mf.locals.size)
    (hnew : LocalRelLM2_3 env mach decl body.layouts newSlot newMls) :
    FrameRelLM2_3 body env mach { af with locals := locals' }
      { mf with locals := mf.locals.set idx newMls hlt } := by
  unfold set? at hset
  split at hset
  case isFalse => cases hset
  case isTrue hidx_af =>
    injection hset with hlocals_eq
    subst hlocals_eq
    refine ⟨h.body_eq, h.location_eq, ?_, ?_, ?_⟩
    · unfold length at *; rw [List.length_set]; exact h.af_locals_len
    · rw [Array.size_set]; exact h.mf_locals_size
    · intro j d s mls hd hs hm
      dsimp only at hs hm
      by_cases hij : idx = j
      · subst hij
        rw [hdecl] at hd; injection hd with hd_eq; subst hd_eq
        unfold get? at hs
        rw [List.getElem?_set_self hidx_af] at hs
        injection hs with hs_eq; subst hs_eq
        rw [Array.getElem?_set_self hlt] at hm; injection hm with hm_eq; subst hm_eq
        exact hnew
      · unfold get? at hs
        simp only [List.getElem?_set, hij, ↓reduceIte] at hs
        simp only [Array.getElem?_set, hij, ↓reduceIte] at hm
        exact h.locals_rel j d s mls hd hs hm

theorem update_local_dealloc {body : CapturedMir} {env : EnumTypeEnv}
    {mach : AnnealMachine} {af : StackFrame}
    {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (h : FrameRelLM2_3 body env mach af mf)
    (hdisj : MemoryAllocDisjoint mf)
    {idx : Nat} {decl : LocalDecl}
    {newSlot : LocalSlot} {newVal : Miri.Interpreter.LocalValue AnnealProv}
    (hdecl : get? body.localDecls idx = some decl)
    {hlt : idx < mf.locals.size}
    (hnew : LocalRelLM2_3 env
      { mach with memory := deallocLocalMemory mach.memory (mf.locals[idx]'hlt).value }
      decl body.layouts newSlot { mf.locals[idx]'hlt with value := newVal }) :
    FrameRelLM2_3 body env
      { mach with memory := deallocLocalMemory mach.memory (mf.locals[idx]'hlt).value }
      { af with locals := af.locals.set idx newSlot }
      { mf with
        locals := mf.locals.set idx
          { mf.locals[idx]'hlt with value := newVal } hlt } := by
  refine ⟨h.body_eq, h.location_eq, ?_, ?_, ?_⟩
  · unfold length at *; rw [List.length_set]; exact h.af_locals_len
  · rw [Array.size_set]; exact h.mf_locals_size
  · intro j d s mls hd hs hm
    have hidx_af : idx < af.locals.length := by
      have hlen := h.af_locals_len
      have hmsz := h.mf_locals_size
      unfold length at hlen hmsz
      omega
    unfold get? at hs
    rw [List.getElem?_set] at hs
    rw [Array.getElem?_set] at hm
    by_cases hij : idx = j
    · subst hij
      simp only [↓reduceIte, hidx_af, Option.some.injEq] at hs hm
      rw [hdecl] at hd; injection hd with hd_eq
      subst hd_eq hs hm
      exact hnew
    · simp only [hij, ↓reduceIte] at hs hm
      apply (h.locals_rel j d s mls hd hs hm).of_dealloc
      intro mp mp' hv hv'
      apply hdisj idx j mp mp' (mf.locals[idx]'hlt).layout mls.layout hij
      · rw [Array.getElem?_eq_getElem hlt, ← hv]
      · rw [hm, ← hv']

theorem step_pc {body : CapturedMir} {env : EnumTypeEnv}
    {mach : AnnealMachine} {af : StackFrame}
    {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (h : FrameRelLM2_3 body env mach af mf) :
    FrameRelLM2_3 body env mach
      { af with stmtIdx := af.stmtIdx + 1 }
      { mf with location := .mir ⟨af.blockIdx, af.stmtIdx + 1⟩ } :=
  ⟨h.body_eq, rfl, h.af_locals_len, h.mf_locals_size, h.locals_rel⟩

end FrameRelLM2_3

/-- Whole-machine simulation relation for `LM-2.3`, parameterized by static
`EnumTypeEnv` and remaining stack-allocation budget `allocBudget`. -/
inductive StateRelLM2_3
    (body : CapturedMir)
    (env : EnumTypeEnv)
    (allocBudget : Nat)
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
      (frame_rel : FrameRelLM2_3 body env m.machine s.frame topFrame)
      (allocSupply_valid : AllocIdSupplyValid allocBudget m.machine.memory)
      (activeCallee_none : s.memory.activeCallee = none)
      (callStack_nil : s.memory.callStack = .nil)
      (borrows_nil : s.memory.borrows = .nil)
      (activeProtectors_nil : s.memory.activeProtectors = .nil)
      (callerLocals_nil : s.memory.callerLocals = .nil)
      (memoryAllocDisjoint : MemoryAllocDisjoint topFrame) :
      StateRelLM2_3 body env allocBudget s m

/-- Outcome correspondence for one `LM-2.3` step (`MirStepNode` ↔ `StepResult`),
covering silent statement/`Goto` steps (`.step`), observable `SwitchInt`
branches (`.emitStep`), root-frame normal returns (`.retRoot`), and lockstep
undefined behavior (`.ub`). -/
inductive StepRelLM2_3
    (body : CapturedMir)
    (env : EnumTypeEnv)
    (allocBudget' : Nat)
    (m : AnnealStepState) :
    MirStepNode →
    Miri.Interpreter.StepResult AnnealStepState Bool →
    Prop where
  | step (s' : MachineState) (m' : AnnealStepState) :
      StateRelLM2_3 body env allocBudget' s' m' →
      StepRelLM2_3 body env allocBudget' m (.step s') (m', .ok true)
  | emitStep (obs : MirObs) (s' : MachineState) (m' : AnnealStepState) :
      StateRelLM2_3 body env allocBudget' s' m' →
      StepRelLM2_3 body env allocBudget' m (.emitStep obs s') (m', .ok true)
  | retRoot (decl0 : LocalDecl) (retVal : Value)
      (imm0 : Miri.Interpreter.Immediate AnnealProv)
      (mem' : Memory) (m' : AnnealStepState) :
      get? body.localDecls 0 = some decl0 →
      annealControlHooks.returnOperand () m = (m, .ok (.immediate imm0)) →
      ImmediateRel decl0.ty body.layouts retVal imm0 →
      m' = { m with stack := ⟨#[]⟩ } →
      StepRelLM2_3 body env allocBudget' m (.retNormal retVal mem') (m', .ok true)
  | ub (m' : AnnealStepState) (msg : String) :
      StepRelLM2_3 body env allocBudget' m (.fail .ub)
        (m', .error (.undefinedBehavior msg))

namespace StepRelLM2_3

theorem ub_iff {body : CapturedMir} {env : EnumTypeEnv}
    {allocBudget' : Nat} {m : AnnealStepState}
    {aRes : MirStepNode} {mRes : Miri.Interpreter.StepResult AnnealStepState Bool}
    (h : StepRelLM2_3 body env allocBudget' m aRes mRes) :
    (aRes = .fail .ub) ↔ (∃ msg, mRes.2 = .error (.undefinedBehavior msg)) := by
  cases h with
  | step _ _ _ =>
    exact ⟨fun h => (by cases h), fun ⟨_, h⟩ => (by cases h)⟩
  | emitStep obs _ _ _ =>
    exact ⟨fun h => (by cases obs <;> cases h), fun ⟨_, h⟩ => (by cases h)⟩
  | retRoot _ _ _ _ _ _ _ _ _ =>
    exact ⟨fun h => (by cases h), fun ⟨_, h⟩ => (by cases h)⟩
  | ub _ msg =>
    exact ⟨fun _ => ⟨msg, rfl⟩, fun _ => rfl⟩

end StepRelLM2_3

/-- Every base `StateRel body s m` embeds into
`StateRelLM2_3 body env allocBudget s m` whenever every enum-typed local in
`env` starts `.dead` or `.uninit` immediate and `AllocIdSupplyValid allocBudget
m.machine.memory` holds (in particular unconditionally for `emptyEnumTypeEnv`
and `allocBudget = 0`). -/
theorem StateRel.toLM2_3_empty {body : CapturedMir} {s : MachineState}
    {m : AnnealStepState} (h : StateRel body s m) :
    StateRelLM2_3 body emptyEnumTypeEnv 0 s m := by
  rcases h with ⟨tf, hf, hrc, hrp, hfr, hcal, hst, hbor, hprot, hcaller, hdisj⟩
  exact .mk tf hf hrc hrp
    ⟨hfr.body_eq, hfr.location_eq, hfr.af_locals_len, hfr.mf_locals_size,
      fun i d sl ml hd hs hm =>
        .base sl ml rfl (hfr.locals_rel i d sl ml hd hs hm)⟩
    (Or.inl rfl)
    hcal hst hbor hprot hcaller hdisj

/-- Lift an entry-point `StateRel body s m` (where enum locals in `env` are
`.dead` or `.uninit` immediate, as produced by `initMachineState` /
`annealInitFrame`) into `StateRelLM2_3 body env allocBudget s m`. -/
theorem StateRel.toLM2_3 {body : CapturedMir} {env : EnumTypeEnv}
    {allocBudget : Nat} {s : MachineState} {m : AnnealStepState}
    (h : StateRel body s m)
    (henv_valid : ∀ ty tb vs, env ty = some (tb, vs) →
      ValidEnumLayout ty body.layouts tb vs)
    (henv_entry : ∀ idx decl slot mls,
      get? body.localDecls idx = some decl →
      (env decl.ty).isSome = true →
      get? s.frame.locals idx = some slot →
      (∀ tf, m.stack.frames = #[tf] → tf.locals[idx]? = some mls →
        slot = .dead ∨
          (slot = .uninit ∧ mls.value = .live (.immediate .uninit))))
    (halloc : AllocIdSupplyValid allocBudget m.machine.memory) :
    StateRelLM2_3 body env allocBudget s m := by
  rcases h with ⟨tf, hf, hrc, hrp, hfr, hcal, hst, hbor, hprot, hcaller, hdisj⟩
  refine .mk tf hf hrc hrp
    ⟨hfr.body_eq, hfr.location_eq, hfr.af_locals_len, hfr.mf_locals_size, ?_⟩
    halloc hcal hst hbor hprot hcaller hdisj
  intro idx decl slot mls hd hs hm
  have hbase := hfr.locals_rel idx decl slot mls hd hs hm
  cases henv : env decl.ty with
  | none => exact .base slot mls henv hbase
  | some pair =>
    rcases pair with ⟨tb, vs⟩
    have hv := henv_valid decl.ty tb vs henv
    have hentry := henv_entry idx decl slot mls hd (by rw [henv]; rfl) hs tf hf hm
    cases hbase with
    | dead c hc => exact .enumDead tb vs c henv hv hc
    | immediate _ imm c hc himm =>
      rcases himm with ⟨rfl, rfl⟩ | ⟨v, hv_eq, _⟩
      · exact .enumUninitImm tb vs c henv hv hc
      · rcases hentry with hdead | ⟨huninit, _⟩
        · rw [hdead] at hv_eq; cases hv_eq
        · rw [huninit] at hv_eq; cases hv_eq
    | indirect _ mp c hc hne _ =>
      rcases hentry with rfl | ⟨_, hval⟩
      · exact False.elim (hne rfl)
      · cases hval

end LeanMiriSpec.Correspondence
