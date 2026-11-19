/-
Copyright 2026 The Fuchsia Authors
Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/
import Lean
import LeanMiriSpec.Correspondence.WitLM4_1
import LeanMiriSpec.Correspondence.WideSliceDstLM
import LeanMiriSpec.Correspondence.SimLM2_3
set_option Elab.async false
/-! # Unwind, SetDiscriminant, Cast, Projection & Closure Correspondence
(LM) Two-sided step simulations (`stepMirFn` vs.
`Miri.Interpreter.Step.step`), conservative hook-extension guarantees
(`step_overlay_eq_base_of_free`), concrete execution/UB witnesses, and
explicit divergence characterizations for `C1` (`setDiscriminant`), `C2`
(`unwindResume`), `C3` (`unwindTerminate`), `C4` (`coverage`), `C5`
(`backwardIncompatibleDropHint`), `C6` (`fnPtrToPtr`), `C7` (`subtype`),
`C8` (all 5 non-`Unsize` `pointerCoercion`s), `C9`
(`unwrapUnsafeBinder`), and `C10` (`AggregateKind.closure`). -/
namespace LeanMiriSpec.UnwindSetDiscrAndFnPtrLM
open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open LeanMiriSpec.Correspondence

/-! ## Section 1. Conservative Hook Overlay & `step_overlay_eq_base_of_free` -/
/-- Canonical `Miri.MIR.TyId` for an unsized `dyn Trait` pointee. -/
def dynPointeeTyId : Miri.MIR.TyId := 3400
/-- Canonical `Miri.MIR.TyId` for `*const dyn Trait` / `*mut dyn Trait`. -/
def wideRawDynPtrTyId : Miri.MIR.TyId := 3401
/-- 16-byte `BackendRepr.ScalarPair` layout for `*const/*mut dyn Trait`. -/
def wideDynPointerLayoutData (nonNull : Bool := false) : Miri.ABI.LayoutData :=
  let ptrPrim : Miri.ABI.Primitive := .Pointer Miri.ABI.AddressSpace.ZERO
  let dataRange : Miri.ABI.WrappingRange :=
    { start := BitVec.ofNat 128 (if nonNull then 1 else 0)
      «end» := BitVec.ofNat 128 ((2 ^ 64) - 1) }
  let vtRange : Miri.ABI.WrappingRange := { start := 1, «end» := BitVec.ofNat 128 ((2 ^ 64) - 1) }
  let dataScalar : Miri.ABI.Scalar := .Initialized (value := ptrPrim) (validRange := dataRange)
  let vtScalar : Miri.ABI.Scalar := .Initialized (value := ptrPrim) (validRange := vtRange)
  { fields := .Arbitrary #[Miri.ABI.Size.ZERO, Miri.ABI.Size.ofBytes 8] #[0, 1]
    variants := .Single 0
    backendRepr :=
      .ScalarPair (a := dataScalar) (b := vtScalar) (bOffset := Miri.ABI.Size.ofBytes 8)
    largestNiche := none
    uninhabited := false
    align := ⟨Miri.ABI.Align.EIGHT⟩
    size := Miri.ABI.Size.ofBytes 16
    maxReprAlign := none
    unadjustedAbiAlign := Miri.ABI.Align.EIGHT
    reprC := false
    randomizationSeed := 0 }
/-- Whether `ty` is a wide raw trait-object pointer `*const/*mut dyn Trait`. -/
def isWideDynRawPtrTy (ty : Ty) : Bool :=
  match ty.kind with
  | .rawPtr _ (.dynamic _) => true
  | _ => false
/-- Overlay `TyId` encoder extending `encodeTyIdWideSlice` with `dyn Trait`. -/
def encodeTyIdOverlay (ty : Ty) : Miri.MIR.TyId :=
  match ty.kind with
  | .dynamic _ => dynPointeeTyId
  | .rawPtr _ (.dynamic _) => wideRawDynPtrTyId
  | _ => encodeTyIdWideSlice ty
/-- Overlay `LocalLayout` translator extending `translateTyWideSlice`. -/
def translateTyOverlay (ty : Ty) (layouts : LayoutTable := emptyLayoutTable) :
    Miri.Interpreter.LocalLayout :=
  match ty.kind with
  | .rawPtr _ (.dynamic _) =>
      { ty := wideRawDynPtrTyId, layout := wideDynPointerLayoutData false }
  | _ => translateTyWideSlice ty layouts
/-- Reconstruct a `LocalLayout` from an overlay `TyId`. -/
def layoutOfEncodedTyIdOverlay (tyId : Miri.MIR.TyId) (layouts : LayoutTable := emptyLayoutTable) : Miri.Interpreter.LocalLayout :=
  if tyId == wideRawDynPtrTyId then
    { ty := wideRawDynPtrTyId, layout := wideDynPointerLayoutData false }
  else if 1000 ≤ tyId then
    match layouts.lookup ((tyId - 1000) / 100) with
    | some tl => { ty := tyId, layout := translateTypeLayout tl }
    | none => layoutOfEncodedTyIdWideSlice tyId layouts
  else
    layoutOfEncodedTyIdWideSlice tyId layouts
/-- Whether `elem` is a source-MIR `UnwrapUnsafeBinder` (not `Rvalue.len`). -/
def isRealUnwrapUnsafeBinderElem : Miri.MIR.ProjectionElem → Bool
  | .UnwrapUnsafeBinder ty => ty != arraySliceMetaTyId
  | _ => false
/-- Whether `place.projection` contains a source-MIR `UnwrapUnsafeBinder`. -/
def hasRealUnwrapUnsafeBinder (place : Miri.MIR.Place) : Bool :=
  place.projection.toList.any isRealUnwrapUnsafeBinderElem
/-- Whether `op` reads a place containing a source-MIR `UnwrapUnsafeBinder`. -/
def operandHasRealUnwrapUnsafeBinder : Miri.MIR.Operand → Bool
  | .Copy p | .Move p => hasRealUnwrapUnsafeBinder p
  | _ => false
/-- Whether `place.localId` has a closure type in `localDecls`. -/
def isClosureLocalPlace (localDecls : List LocalDecl) (place : Miri.MIR.Place) : Bool :=
  match get? localDecls place.localId with
  | some { ty := { kind := .closure _ _, .. }, .. } => true
  | _ => false
/-- Whether `op` is a projected read of a closure local in `localDecls`. -/
def isProjectedClosureOperand (localDecls : List LocalDecl) : Miri.MIR.Operand → Bool
  | .Copy p | .Move p => !p.projection.isEmpty && isClosureLocalPlace localDecls p
  | _ => false
/-- Whether `place.localId` has a wide slice or wide `dyn Trait` pointer type.
-/
def isWideOverlayPlace (localDecls : List LocalDecl) (place : Miri.MIR.Place) : Bool :=
  match get? localDecls place.localId with
  | some decl => isWideSliceOrPointeeTy decl.ty || isWideDynRawPtrTy decl.ty
  | none => false
/-- Whether `rvalue` uses a source-MIR `UnwrapUnsafeBinder` or closure field. -/
def rvalueUsesPlaceOrClosureOverlay (localDecls : List LocalDecl) : Miri.MIR.Rvalue → Bool
  | .Use op _ | .Repeat op _ | .UnaryOp _ op | .Cast _ op _ | .WrapUnsafeBinder op _ =>
      operandHasRealUnwrapUnsafeBinder op || isProjectedClosureOperand localDecls op
  | .BinaryOp _ lhs rhs =>
      operandHasRealUnwrapUnsafeBinder lhs || operandHasRealUnwrapUnsafeBinder rhs ||
      isProjectedClosureOperand localDecls lhs || isProjectedClosureOperand localDecls rhs
  | .Ref _ _ p | .RawPtr _ p | .Reborrow _ _ p | .Discriminant p | .CopyForDeref p =>
      hasRealUnwrapUnsafeBinder p
  | .Aggregate _ ops =>
      ops.toList.any (fun op =>
        operandHasRealUnwrapUnsafeBinder op || isProjectedClosureOperand localDecls op)
  | .ThreadLocalRef _ => false
/-- Cast kinds handled by the overlay (`ReifyFnPointer` stays on `LM-4.1`). -/
def isOverlayCastKind : Miri.MIR.CastKind → Bool
  | .FnPtrToPtr => true
  | .Subtype => true
  | .PointerCoercion (.ClosureFnPointer _) _ => true
  | .PointerCoercion .UnsafeFnPointer _ => true
  | .PointerCoercion .MutToConstPointer _ => true
  | .PointerCoercion .ArrayToPointer _ => true
  | _ => false
/-- Syntactic predicate for `Assign` statements routed through the overlay. -/
def isUnwindFnPtrClosureAssign (localDecls : List LocalDecl) (place : Miri.MIR.Place) (rvalue : Miri.MIR.Rvalue) : Bool :=
  hasRealUnwrapUnsafeBinder place ||
  rvalueUsesPlaceOrClosureOverlay localDecls rvalue ||
  match rvalue with
  | .Aggregate (.Closure _ _) _ => true
  | .Cast kind _ _ => isOverlayCastKind kind
  | _ => false
/-- Resolve and cache a local's overlay `LocalLayout` in the top frame. -/
def annealResolveAndCacheLocalLayoutOverlay (localDecls : List LocalDecl) (layouts : LayoutTable) (localId : Miri.MIR.LocalId) (known : Option Miri.Interpreter.LocalLayout := none) :
    Miri.Interpreter.RvalueM AnnealStepState
      (Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit ×
        Miri.Interpreter.LocalLayout) := do
  let st ← get
  let some frame := st.stack.currentFrame?
    | throw (.stack .emptyStack)
  let ls ←
    match frame.getLocal localId with
    | .ok ls => pure ls
    | .error e => throw (.stack e)
  let declLayOpt := (get? localDecls localId).map (translateTyOverlay ·.ty layouts)
  let computed ←
    match declLayOpt <|> ls.layout <|> known with
    | some l => pure l
    | none =>
        match frame.body.locals[localId]? with
        | some tyId => pure (layoutOfEncodedTyIdOverlay tyId layouts)
        | none => throw (.stack (.missingLocalType localId))
  match frame.getOrCacheLocalLayout localId computed with
  | .error e => throw (.stack e)
  | .ok (frame', _) =>
      let frame'' := if h : localId < frame'.locals.size then
          if isWideOverlayPlace localDecls ⟨localId, #[]⟩ then
            { frame' with
              locals := frame'.locals.set localId
                { (frame'.locals[localId]'h) with layout := some computed } h }
          else frame'
        else frame'
      let idx := st.stack.frames.size - 1
      if h : idx < st.stack.frames.size then
        set { st with stack := { frames := st.stack.frames.set idx frame'' h } }
        return (frame'', computed)
      else
        throw (.stack .emptyStack)
/-- Provenance-aware `readImmediate` over `OpTy AnnealProv` that never masks
misalignment or bounds UB behind fallback reads. -/
def annealReadImmediateOverlay (op : Miri.Interpreter.OpTy AnnealProv) : Miri.Interpreter.RvalueM AnnealStepState (Miri.Interpreter.RvalueImmTy AnnealProv) :=
  match op.op with
  | .immediate (.scalar s) => return ⟨.scalar s, op.layout⟩
  | .immediate (.scalarPair s1 s2) => return ⟨.scalarPair s1 s2, op.layout⟩
  | .immediate .uninit =>
      if op.layout.layout.size == Miri.ABI.Size.ZERO && !op.layout.layout.isUninhabited then
        return ⟨.uninit, op.layout⟩
      else throw (.undefinedBehavior "read of uninitialized local")
  | .indirect mp =>
      match op.layout.layout.fields with
      | .Array _ _ => annealReadImmediate op
      | _ =>
          if op.layout.ty == wideRawStrPtrTyId ||
             (3100 ≤ op.layout.ty && op.layout.ty < 3300) then
            annealReadImmediate op
          else
            match op.layout.layout.backendRepr with
            | .ScalarPair =>
                if mp.misaligned.isSome then
                  throw (.undefinedBehavior "misaligned pointer dereference")
                else annealReadIndirectImmediate mp op.layout
            | _ => annealReadMemoryPlace mp op.layout
/-- Build an unchecked `MemPlace` by dereferencing a scalar pointer immediate.
-/
private def annealRawDerefImmediate (imm : Miri.Interpreter.Immediate AnnealProv) (ptLay : Miri.Interpreter.LocalLayout) : Miri.Interpreter.RvalueM AnnealStepState (Miri.Interpreter.OpTy AnnealProv) := do
  let sc ← match imm.toScalar with
    | .ok s => pure s
    | .error e => throw (Miri.Interpreter.ScalarOps.immediateError e)
  let ptr ← match sc.toPointer annealTargetDataLayout with
    | .ok p => pure p
    | .error e => throw (Miri.Interpreter.ScalarOps.scalarError e)
  let mismatch ← match annealOffsetMisalignment ptr.offset ptLay.layout.align.abi with
    | .ok m => pure m
    | .error e => throw (.invalidProgram (toString e))
  return ⟨.indirect ⟨ptr, .none, mismatch⟩, ptLay⟩
/-- Dereference a thin or wide pointer `OpTy AnnealProv` to its pointee. -/
def annealDerefOpTyOverlay (layouts : LayoutTable) (refPointeeOpt : Option Miri.Interpreter.LocalLayout) (base : Miri.Interpreter.OpTy AnnealProv) (skipValidity : Bool := false) :
    Miri.Interpreter.RvalueM AnnealStepState (Miri.Interpreter.OpTy AnnealProv) := do
  let imm ← annealReadImmediate base
  if isWideSlicePtrTyId base.layout.ty then
    if !skipValidity && isWideSafeRefTyId base.layout.ty then
      annealValidateSafeWideSliceRef layouts ⟨imm.imm, base.layout⟩ (nullFirst := true)
    let some ptId := wideSlicePointeeTyId? base.layout.ty
      | throw (.unsupported "wide slice deref without pointee layout")
    let ptLay := layoutOfEncodedTyIdWideSlice ptId layouts
    match annealDerefWideSliceImmediate imm.imm ptLay with
    | .ok mp => return ⟨.indirect mp, ptLay⟩
    | .error err => throw err
  else if base.layout.ty == 41 then
    let some ptLay := refPointeeOpt
      | throw (.unsupported "safe reference deref without pointee layout")
    if skipValidity then annealRawDerefImmediate imm.imm ptLay
    else
      let st ← get
      match annealSafeRefDerefCheck st.machine imm.imm ptLay with
      | .ok mp => return ⟨.indirect mp, ptLay⟩
      | .error err => throw err
  else
    let some ptId := rawPtrPointeeEncodedTyId? base.layout.ty
      | throw (.unsupported s!"raw pointer deref pointee not encoded for TyId {base.layout.ty}")
    annealRawDerefImmediate imm.imm (layoutOfEncodedTyId ptId layouts)
/-- Extract the pointee `LocalLayout` of a safe reference `declTy`. -/
def unwrapRefPointeeLayout? (layouts : LayoutTable) (ty : Ty) : Option Miri.Interpreter.LocalLayout :=
  match ty.kind with
  | .ref _ pt =>
      if derefPointeeKindHasExactLayout pt then
        some (translateTy { kind := pt, layoutIdx := 0 } layouts)
      else none
  | _ => none
/-- Sequentially project an `OpTy AnnealProv` via `Miri.Interpreter.project`. -/
def annealEvalUnwrapChainOp (localDecls : List LocalDecl) (layouts : LayoutTable) (localId : Miri.MIR.LocalId) (frame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit) (base : Miri.Interpreter.OpTy AnnealProv) :
    List Miri.MIR.ProjectionElem →
    Miri.Interpreter.RvalueM AnnealStepState (Miri.Interpreter.OpTy AnnealProv)
  | [] => return base
  | .UnwrapUnsafeBinder ty :: rest => do
      let st ← get
      if ty == arraySliceMetaTyId then
        match base.op with
        | .indirect mp =>
            if base.layout.ty == strPointeeTyId ||
               (2100 ≤ base.layout.ty && base.layout.ty < 2200) then
              match mp.toRef annealTargetDataLayout with
              | .ok imm =>
                  return ⟨.immediate imm,
                          { ty := wideRawStrPtrTyId, layout := widePointerLayoutData false }⟩
              | .error err => throw (.invalidProgram s!"slice len reference: {repr err}")
            else
              let cxArr : Miri.Interpreter.ProjectionCx AnnealProv :=
                { annealProjectionCx frame layouts st.machine with
                  layoutOf := fun _ =>
                    match base.layout.layout.fields with
                    | .Array _ _ => .ok { ty := arraySliceMetaTyId, layout := base.layout.layout }
                    | _ => .error (.obligation "len on non-array") }
              match Miri.Interpreter.project cxArr base (.UnwrapUnsafeBinder arraySliceMetaTyId) with
              | .ok next => annealEvalUnwrapChainOp localDecls layouts localId frame next rest
              | .error err => throw (annealLiftProjectionError err)
        | _ => throw (.unsupported "len on immediate non-array/slice")
      else
        match base.op with
        | .immediate .uninit =>
            if base.layout.layout.size != Miri.ABI.Size.ZERO then
              throw (.undefinedBehavior "projected read of uninitialized local")
        | _ => pure ()
        let cx : Miri.Interpreter.ProjectionCx AnnealProv :=
          { annealProjectionCx frame layouts st.machine with
            layoutOf := fun t => .ok (layoutOfEncodedTyIdOverlay t layouts)
            memoryOffset := fun place offset mode metaVal =>
              let effMeta := if !base.layout.layout.isSized then place.metadata else metaVal
              Miri.Interpreter.projectionMemoryOffset
                annealPointerArithmetic
                (annealPointerResolver st.machine)
                (annealLiveAllocationLookup st.machine)
                place offset mode effMeta }
        if !base.layout.layout.isSized then
          let targetLay := layoutOfEncodedTyIdOverlay ty layouts
          if targetLay.layout.isSized then
            throw (.invalidProgram "transmute requires equally sized layouts")
          else
            match base.op with
            | .indirect mp =>
                annealEvalUnwrapChainOp localDecls layouts localId frame ⟨.indirect mp, targetLay⟩ rest
            | .immediate _ => throw (.invalidProgram "unsized immediate in UnwrapUnsafeBinder")
        else
          match Miri.Interpreter.project cx base (.UnwrapUnsafeBinder ty) with
          | .ok next => annealEvalUnwrapChainOp localDecls layouts localId frame next rest
          | .error err => throw (annealLiftProjectionError err)
  | .Deref :: rest => do
      let refPt := (get? localDecls localId).bind (fun d => unwrapRefPointeeLayout? layouts d.ty)
      let derefed ← annealDerefOpTyOverlay layouts refPt base false
      annealEvalUnwrapChainOp localDecls layouts localId frame derefed rest
  | .Field idx fTy :: rest => do
      match base.op with
      | .immediate (.scalarPair s0 s1) =>
          if idx == 0 then
            annealEvalUnwrapChainOp localDecls layouts localId frame
              ⟨.immediate (.scalar s0), layoutOfEncodedTyIdOverlay fTy layouts⟩ rest
          else if idx == 1 then
            annealEvalUnwrapChainOp localDecls layouts localId frame
              ⟨.immediate (.scalar s1), layoutOfEncodedTyIdOverlay fTy layouts⟩ rest
          else
            throw (.invalidProgram "scalarPair field index out of bounds")
      | _ =>
          match Miri.Interpreter.project (annealStructProjectionCx layouts (some fTy))
              base (.Field idx fTy) with
          | .ok next => annealEvalUnwrapChainOp localDecls layouts localId frame next rest
          | .error err => throw (annealLiftProjectionError err)
  | elem :: rest => do
      let st ← get
      match Miri.Interpreter.project (annealProjectionCx frame layouts st.machine) base elem with
      | .ok next => annealEvalUnwrapChainOp localDecls layouts localId frame next rest
      | .error err => throw (annealLiftProjectionError err)
/-- Overlay operand evaluator handling `UnwrapUnsafeBinder` chains and wide
slice/`dyn Trait` pointer locals while delegating all others to
`annealEvalOperand`. -/
def annealEvalOperandOverlay (localDecls : List LocalDecl) (layouts : LayoutTable) (op : Miri.MIR.Operand) (known : Option Miri.Interpreter.LocalLayout) :
    Miri.Interpreter.RvalueM AnnealStepState (Miri.Interpreter.OpTy AnnealProv) := do
  match op with
  | .Copy place | .Move place =>
      if hasRealUnwrapUnsafeBinder place then
        let st ← get
        if st.stack.currentFrame?.isNone then
          throw (.stack .emptyStack)
        let (frame', layout) ←
          annealResolveAndCacheLocalLayoutOverlay localDecls layouts place.localId known
        let operand ←
          match frame'.getLocalOperand place.localId with
          | .ok opVal => pure opVal
          | .error (.localExpectedLive _) => throw (.undefinedBehavior "read of dead local")
          | .error e => throw (.stack e)
        match operand with
        | .indirect mp =>
            match place.projection.toList with
            | .Deref :: _ => pure ()
            | _ =>
                let stNow ← get
                match annealCheckIndirectInitialized stNow.machine mp layout.layout.size with
                | .ok () => pure ()
                | .error err => throw err
        | _ => pure ()
        annealEvalUnwrapChainOp localDecls layouts place.localId frame' ⟨operand, layout⟩
          place.projection.toList
      else if place.projection.isEmpty && isWideOverlayPlace localDecls place then
        let st ← get
        if st.stack.currentFrame?.isNone then
          throw (.stack .emptyStack)
        let (frame', layout) ←
          annealResolveAndCacheLocalLayoutOverlay localDecls layouts place.localId known
        let operand ←
          match frame'.getLocalOperand place.localId with
          | .ok opVal => pure opVal
          | .error (.localExpectedLive _) => throw (.undefinedBehavior "read of dead local")
          | .error e => throw (.stack e)
        match op with
        | .Move _ =>
            match frame'.replaceLocalValue place.localId (.live (.immediate .uninit)) with
            | .ok frame'' =>
                let stNow ← get
                let idx := stNow.stack.frames.size - 1
                if h : idx < stNow.stack.frames.size then
                  set { stNow with stack := { frames := stNow.stack.frames.set idx frame'' h } }
                  return ⟨operand, layout⟩
                else throw (.stack .emptyStack)
            | .error e => throw (.stack e)
        | _ => return ⟨operand, layout⟩
      else
        annealEvalOperand localDecls layouts op known
  | _ => annealEvalOperand localDecls layouts op known
/-- `PlaceProjectionHooks` instantiated for
`Miri.Interpreter.PlaceDynamic.evalPlace`. -/
def annealPlaceProjectionHooksOverlay (localDecls : List LocalDecl := .nil)
    (layouts : LayoutTable := emptyLayoutTable) :
    Miri.Interpreter.PlaceProjectionHooks AnnealProv AnnealStepState Unit Unit where
  place := {
    annealMutablePlaceHooks localDecls layouts with
    resolveLayout := fun _ localId =>
      match get? localDecls localId with
      | some decl => pure (translateTyOverlay decl.ty layouts)
      | none => throw (.stack (.missingLocalType localId))
    deref := fun _ base skipValidity => do
      let st ← get
      let some frame := st.stack.currentFrame?
        | throw (.stack .emptyStack)
      let operand ←
        match base.ref with
        | .local _ localId offOpt _ =>
            match frame.getLocalOperand localId with
            | .ok opVal =>
                match offOpt, opVal with
                | some off, .indirect mp =>
                    if off == Miri.ABI.Size.ZERO then pure (.indirect mp)
                    else throw (.unsupported "nonzero local offset in deref")
                | _, _ => pure opVal
            | .error (.localExpectedLive _) => throw (.undefinedBehavior "read of dead local")
            | .error e => throw (.stack e)
        | .memory mp => pure (.indirect mp)
      let refPt :=
        match base.ref with
        | .local _ localId _ _ =>
            (get? localDecls localId).bind (fun d => unwrapRefPointeeLayout? layouts d.ty)
        | _ => none
      let derefed ← annealDerefOpTyOverlay layouts refPt ⟨operand, base.layout⟩ skipValidity
      match derefed.op with
      | .indirect mp => return ⟨.memory mp, derefed.layout⟩
      | .immediate _ => throw (.invalidProgram "deref produced immediate")
    checkPlaceType := fun _ _ _ => pure ()
    memoryOffset := fun _ place amount mode metaValue => do
      let st ← get
      match Miri.Interpreter.projectionMemoryOffset
          annealPointerArithmetic
          (annealPointerResolver st.machine)
          (annealLiveAllocationLookup st.machine)
          place amount mode metaValue with
      | .ok mp' => return mp'
      | .error err => throw (annealLiftProjectionError err) }
  target := annealTargetDataLayout
  maxSizeOfVal := Miri.ABI.Size.ofBytes 0x7fff_ffff_ffff_ffff
  dynamic := annealDynamicLayoutHooksWideSlice layouts
  dynamicFuel := 8
  isSliceOrStr := fun _ tyId =>
    pure (tyId == strPointeeTyId || (2100 ≤ tyId && tyId < 2200))
  field := fun _ baseLay idx =>
    match annealFieldLayout layouts none baseLay idx with
    | .ok fLay => pure fLay
    | .error err => throw (annealLiftProjectionError err)
  variant := fun _ baseLay vIdx =>
    if vIdx == 0 then pure baseLay
    else throw (.unsupported "multi-variant downcast in overlay PlaceProjectionHooks")
  packedAlign := fun _ _ => pure none
  subsliceLayout := fun _ _ _ =>
    throw (.unsupported "subslice in overlay PlaceProjectionHooks")
  layoutOf := fun _ tyId => pure (layoutOfEncodedTyIdOverlay tyId layouts)
  localIndex := fun _ localId => do
    let st ← get
    let some frame := st.stack.currentFrame?
      | throw (.stack .emptyStack)
    match annealLocalIndex frame st.machine localId with
    | .ok idx => return idx
    | .error err => throw (annealLiftProjectionError err)
/-- Canonical destination evaluator via
`Miri.Interpreter.PlaceDynamic.evalPlace`. -/
def annealEvalPlaceDynamicCanonical (localDecls : List LocalDecl) (layouts : LayoutTable) (place : Miri.MIR.Place) (skipValidity : Bool) : Miri.Interpreter.RvalueM AnnealStepState (Miri.Interpreter.RuntimePlace AnnealProv) := do
  let (_, baseLay) ← annealResolveAndCacheLocalLayoutOverlay localDecls layouts place.localId none
  let rp ←
    Miri.Interpreter.PlaceDynamic.evalPlace
      (annealPlaceProjectionHooksOverlay localDecls layouts) () place skipValidity
  match rp.ref with
  | .local fIdx locId (some off) id =>
      if off == Miri.ABI.Size.ZERO && rp.layout.layout.size == baseLay.layout.size then
        return ⟨.local fIdx locId none id, rp.layout⟩
      else
        return rp
  | _ => return rp
/-- Overlay destination place evaluator routing `UnwrapUnsafeBinder` directly
to canonical `Miri.Interpreter.PlaceDynamic.evalPlace`. -/
def annealEvalPlaceOverlay (localDecls : List LocalDecl) (layouts : LayoutTable) (place : Miri.MIR.Place) (skipValidity : Bool := false) :
    Miri.Interpreter.RvalueM AnnealStepState (Miri.Interpreter.RuntimePlace AnnealProv) := do
  if hasRealUnwrapUnsafeBinder place then
    annealEvalPlaceDynamicCanonical localDecls layouts place skipValidity
  else if place.projection.isEmpty && isWideOverlayPlace localDecls place then
    let st ← get
    if st.stack.currentFrame?.isNone then
      throw (.stack .emptyStack)
    let frameIdx := st.stack.frames.size - 1
    let (frame', layout) ←
      annealResolveAndCacheLocalLayoutOverlay localDecls layouts place.localId none
    return ⟨.local frameIdx place.localId none frame'.localsIdentity, layout⟩
  else
    annealEvalPlace localDecls layouts place
/-- Function-pointer validity check (`CastHooks.checkFunctionPointer`). -/
def annealCheckFnPointerOverlay (fnPtrs : List FnPtrEntry) (ptr : Miri.Memory.Pointer (Option AnnealProv)) : Miri.Interpreter.RvalueM AnnealStepState Unit := do
  let st ← get
  match ptr.intoPointerOrAddr with
  | .error _ => throw (.undefinedBehavior "DanglingIntPointer")
  | .ok _ =>
      match annealResolvePtr st.machine ptr 0 with
      | .error _ => throw (.undefinedBehavior "DanglingIntPointer")
      | .ok resolved =>
          if resolved.offset != Miri.ABI.Size.ZERO then
            throw (.undefinedBehavior "InvalidFunctionPointer")
          else
            let isFn :=
              match fnPtrs with
              | [] => isFnPtrAllocId resolved.allocId.value.toNat
              | _ :: _ => (lookupFnPtr fnPtrs resolved.allocId.value.toNat).isSome
            if isFn then pure ()
            else throw (.undefinedBehavior "InvalidFunctionPointer")
/-- Recover the source MIR `PointerCoercion` string at the current PC. -/
def activeCastCoercionKind? (currentBody : CapturedMir) (st : AnnealStepState) : Option String :=
  match st.stack.currentFrame? with
  | some frame =>
      match frame.location with
      | .mir loc =>
          match get? currentBody.basicBlocks loc.block with
          | some bb =>
              match get? bb.statements loc.statementIndex with
              | some { kind := .assign _ (.cast (.pointerCoercion ck) _ _), .. } => some ck
              | _ => none
          | none => none
      | .unwinding _ => none
  | none => none
/-- Extract `(defPath, typeArgs)` for `ClosureFnPointer` coercions. -/
def extractOverlayCoercionTarget? (coercionKind : String) (tyOpt : Option Ty) : Option (DefPath × List RigidTy) :=
  if stringEq coercionKind "ClosureFnPointer(Normal)" then
    match tyOpt with
    | some { kind := .closure defPath .nil, .. } => some (defPath, .nil)
    | _ => none
  else
    extractReifyCoercionTarget? coercionKind tyOpt
/-- Function-pointer allocation hook for `ClosureFnPointer`. -/
def annealReifyOrClosureFnPointerAlloc (currentBody : CapturedMir) (fnPtrs : List FnPtrEntry) : Miri.Interpreter.RvalueM AnnealStepState (Miri.Memory.Pointer (Option AnnealProv)) :=
  fun st =>
    match st.stack.currentFrame? with
    | none => .error (.stack .emptyStack) st
    | some frame =>
      match frame.location with
      | .unwinding _ => .error .expectedMirLocation st
      | .mir loc =>
        match get? currentBody.basicBlocks loc.block with
        | none => .error (.invalidBlock loc.block) st
        | some bb =>
          match get? bb.statements loc.statementIndex with
          | some { kind := .assign _ (.cast (.pointerCoercion ck) op targetTy), .. } =>
            match extractOverlayCoercionTarget? ck
                (operandTy currentBody.localDecls currentBody.layouts op) with
            | some (defPath, []) =>
              let allocId : Nat :=
                match findFnPtrEntry? fnPtrs defPath [] (some targetTy.kind) with
                | some existing => existing.allocId
                | none => nextFnPtrAllocId fnPtrs
              if h : UInt64.ofNat allocId ≠ 0 then
                let mAllocId : Miri.Memory.AllocId := ⟨UInt64.ofNat allocId, h⟩
                match st.machine.lookupBaseAddr mAllocId with
                | some baseAddr =>
                  .ok ⟨Miri.ABI.Size.ofBytes (baseAddr + UInt64.ofNat 0),
                       some (.concrete mAllocId Miri.Memory.BorTag.one)⟩ st
                | none =>
                  let baseAddr := annealStackBaseAddr mAllocId
                  let addresses' :=
                    { st.machine.addresses with
                      baseAddr := #[⟨mAllocId, baseAddr⟩] ++ st.machine.addresses.baseAddr }
                  .ok ⟨Miri.ABI.Size.ofBytes (baseAddr + UInt64.ofNat 0),
                       some (.concrete mAllocId Miri.Memory.BorTag.one)⟩
                    { st with machine := { st.machine with addresses := addresses' } }
              else
                .error (.resourceExhaustion "function pointer allocation ID wrap") st
            | some (_, _ :: _) =>
              .error (.unsupported "polymorphic function reification") st
            | none =>
              .error (.invalidProgram "closure fn pointer on invalid source type") st
          | _ => .error (.invalidProgram "expected pointerCoercion cast statement") st
/-- Validate a transmuted scalar `sc` against `destLay : LocalLayout`. -/
def annealValidateTransmutedScalar (destLay : Miri.Interpreter.LocalLayout) (sc : Miri.Memory.Scalar AnnealProv) : Bool :=
  if !annealValidateScalarForTyId destLay.ty sc then
    false
  else
    match destLay.layout.backendRepr with
    | .Scalar (.Initialized (value := .Int _ _) (validRange := vr)) =>
        match sc.toScalarInt with
        | .ok msc =>
            (msc.size == destLay.layout.size) && vr.contains msc.data
        | .error _ => false
    | .Scalar (.Initialized (value := .Pointer _) (validRange := vr)) =>
        match sc.toPointer annealTargetDataLayout with
        | .ok p =>
            let provOk := !((destLay.ty == 41 || destLay.ty == 42) && p.provenance.isNone)
            provOk && vr.contains (BitVec.ofNat 128 p.offset.bytes.toNat)
        | .error _ => false
    | _ => true
/-- `CastHooks.copyAllowTransmute` implementation for `CastKind.Subtype`. -/
def annealCopyAllowTransmuteOverlay (source : Miri.Interpreter.OpTy AnnealProv) (dest : Miri.Interpreter.RuntimePlace AnnealProv) : Miri.Interpreter.RvalueM AnnealStepState Unit := do
  let imm ← annealReadImmediateOverlay source
  if dest.layout.layout.isUninhabited then
    throw (.undefinedBehavior "transmute to uninhabited type")
  else if dest.layout.layout.isZst then
    annealWriteImmediateLM2_2 .uninit dest
  else
    match imm.imm with
    | .uninit => throw (.undefinedBehavior "transmute of uninitialized value")
    | .scalar sc =>
        if annealValidateTransmutedScalar dest.layout sc then
          annealWriteImmediateLM2_2 (.scalar sc) dest
        else
          throw (.undefinedBehavior "transmute produced invalid value for target layout")
    | .scalarPair s0 s1 =>
        annealWriteImmediateLM2_2 (.scalarPair s0 s1) dest
/-- Active closure source `CastTypeInfo` lookup for `ClosureFnPointer`. -/
def activeClosureCastTypeInfo? (currentBody : CapturedMir) (st : AnnealStepState) (tyId : Miri.MIR.TyId) : Option Miri.Interpreter.CastTypeInfo :=
  match st.stack.currentFrame? with
  | some frame =>
      match frame.location with
      | .mir loc =>
          match get? currentBody.basicBlocks loc.block with
          | some bb =>
              match get? bb.statements loc.statementIndex with
              | some { kind := .assign _ (.cast (.pointerCoercion _) op _), .. } =>
                  match operandTy currentBody.localDecls currentBody.layouts op with
                  | some srcTy =>
                      match srcTy.kind with
                      | .closure _ upvars =>
                          if encodeTyId srcTy == tyId then
                            some (.closure 0 #[] upvars.length)
                          else none
                      | _ => none
                  | none => none
              | _ => none
          | none => none
      | .unwinding _ => none
  | none => none
/-- Extended `CastTypeInfo` classifier covering thin/wide pointers, function
pointers, and closure sources. -/
def castTypeInfoOverlay (currentBody : CapturedMir) (st : AnnealStepState) (tyId : Miri.MIR.TyId) : Except Miri.Interpreter.StepError Miri.Interpreter.CastTypeInfo :=
  if let some info := activeClosureCastTypeInfo? currentBody st tyId then
    .ok info
  else if tyId == 40 then
    .ok (.rawPointer 40)
  else if tyId == 41 then
    .ok (.reference 1)
  else if tyId == 42 then
    .ok .fnPointer
  else if tyId == wideRawDynPtrTyId then
    .ok (.rawPointer dynPointeeTyId)
  else
    castTypeInfoOfEncodedTyIdWideSlice tyId
/-- Validate wide raw pointer immediates (`derefPointer` in `Cast.cast`). -/
def annealDerefPointerCastOverlay (layouts : LayoutTable) (op : Miri.Interpreter.OpTy AnnealProv) : Miri.Interpreter.RvalueM AnnealStepState Unit := do
  let imm ← annealReadImmediate op
  if imm.layout.ty == wideRawDynPtrTyId then
    match imm.imm with
    | .scalarPair dSc vtSc =>
        match dSc.toPointer annealTargetDataLayout, vtSc.toPointer annealTargetDataLayout with
        | .ok _, .ok _ => pure ()
        | _, _ => throw (.invalidProgram "malformed wide dyn raw pointer immediate")
    | .uninit => throw (.undefinedBehavior "read of uninitialized local")
    | _ => throw (.invalidProgram "expected scalarPair for wide dyn raw pointer")
  else
    annealDerefValidityWideSlice layouts imm
/-- `CastHooks` overlay for `FnPtrToPtr`, `Subtype`, `ClosureFnPointer`,
`UnsafeFnPointer`, `MutToConstPointer`, and `ArrayToPointer`. -/
def annealCastHooksUnwindFnPtrClosure (currentBody : CapturedMir) (fnPtrs : List FnPtrEntry := .nil) :
    Miri.Interpreter.CastHooks AnnealProv AnnealStepState Unit
      (Miri.Interpreter.RuntimePlace AnnealProv) :=
  { annealCastHooksLM4_1 currentBody fnPtrs with
    typeInfo := fun _ tyId => do
      let st ← get
      match castTypeInfoOverlay currentBody st tyId with
      | .ok info => pure info
      | .error err => throw err
    layoutOf := fun _ tyId => pure (layoutOfEncodedTyIdOverlay tyId currentBody.layouts)
    readImmediate := fun _ op => annealReadImmediateOverlay op
    writeImmediate := fun _ val dest => annealWriteImmediateLM2_2 val dest
    writePointer := fun _ ptr dest =>
      match ptr.provenance with
      | some prov =>
        annealWriteImmediateLM2_2
          (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout ⟨ptr.offset, prov⟩))
          dest
      | none =>
        throw (.invalidProgram "function pointer coercion produced provenance-free pointer")
    derefPointer := fun _ op => annealDerefPointerCastOverlay currentBody.layouts op
    checkFunctionPointer := fun _ ptr => annealCheckFnPointerOverlay fnPtrs ptr
    resolveFunction := fun _ _ _ => pure (some ⟨.Item 0, #[]⟩)
    resolveClosureFnOnce := fun _ _ _ => pure ⟨.Item 0, #[]⟩
    functionPointer := fun _ _ => annealReifyOrClosureFnPointerAlloc currentBody fnPtrs
    copyAllowTransmute := fun _ src dest => annealCopyAllowTransmuteOverlay src dest }
/-- `AggregateHooks` overlay for `AggregateKind.Closure` (`C10`), rejecting
dead local destinations via `validate`. -/
def annealAggregateHooksUnwindFnPtrClosure (localDecls : List LocalDecl := .nil)
    (layouts : LayoutTable := emptyLayoutTable) :
    Miri.Interpreter.AggregateHooks AnnealProv AnnealStepState Unit
      (Miri.Interpreter.RuntimePlace AnnealProv) :=
  { annealAggregateHooksLM2_2 localDecls layouts with
    evalOperand := fun _ op known => annealEvalOperandOverlay localDecls layouts op known
    evalOperandAt := fun _ _ op known => do
      let opTy ← annealEvalOperandOverlay localDecls layouts op known
      match opTy.op with
      | .immediate _ =>
          let imm ← annealReadImmediateOverlay opTy
          return ⟨.immediate imm.imm, imm.layout⟩
      | .indirect _ =>
          return opTy
    copyOp := fun _ src dest =>
      if usesStructMemCopyDest ⟨dest.ref, src.layout⟩ && usesStructMemCopyDest dest then
        annealStructMemCopyOp localDecls layouts src dest
      else do
        let imm ← annealReadImmediateOverlay src
        annealWriteImmediateLM2_2 imm.imm dest
    copyOpNoValidate := fun _ src dest _ =>
      if usesStructMemCopyDest ⟨dest.ref, src.layout⟩ && usesStructMemCopyDest dest then
        annealStructMemCopyOp localDecls layouts src dest
      else do
        let imm ← annealReadImmediateOverlay src
        annealWriteImmediateLM2_2 imm.imm dest
    validate := fun _ dest =>
      match dest.ref with
      | .local _ localId _ _ => do
          let st ← get
          let some frame := st.stack.currentFrame?
            | throw (.stack .emptyStack)
          match frame.getLocalOperand localId with
          | .ok _ => pure ()
          | .error (.localExpectedLive _) =>
              throw (.undefinedBehavior "write to dead local")
          | .error e => throw (.stack e)
      | .memory _ => pure () }
/-- `RvalueHooks` overlay routing `UnwrapUnsafeBinder`,
`AggregateKind.Closure`, and overlay casts while failing closed on
unrecognized coercion tags. -/
def annealRvalueHooksUnwindFnPtrClosure (currentBody : CapturedMir) (fnPtrs : List FnPtrEntry := .nil) :
    Miri.Interpreter.RvalueHooks AnnealProv AnnealStepState Unit
      (Miri.Interpreter.RuntimePlace AnnealProv) :=
  let decls := currentBody.localDecls
  let layouts := currentBody.layouts
  { annealRvalueHooksLM4_1 currentBody fnPtrs with
    evalPlace := fun _ p skipValidity => annealEvalPlaceOverlay decls layouts p skipValidity
    evalOperand := fun _ op known => annealEvalOperandOverlay decls layouts op known
    evalOperandAt := fun _ _ op known => annealEvalOperandOverlay decls layouts op known
    evalPlaceToOp := fun _ p known => annealEvalOperandOverlay decls layouts (.Copy p) known
    readImmediate := fun _ op => annealReadImmediateOverlay op
    writeImmediate := fun _ val dest => annealWriteImmediateLM2_2 val dest
    copyOp := fun _ src dest => do
      let imm ← annealReadImmediateOverlay src
      annealWriteImmediateLM2_2 imm.imm dest
    copyOpAllowTransmute := fun _ src dest => annealCopyAllowTransmuteOverlay src dest
    unaryOp := fun c op v =>
      let sh := { annealScalarOpsHooksWideSlice decls layouts with
        derefValidity := fun _ val =>
          if val.layout.ty == arraySliceMetaTyId then pure ()
          else annealDerefValidityWideSlice layouts val }
      Miri.Interpreter.ScalarOps.unary sh c op v
    writeAggregate := fun c k os d =>
      match k with
      | .Closure _ _ =>
          Miri.Interpreter.writeAggregate
            (annealAggregateHooksUnwindFnPtrClosure decls layouts) c k os d
      | _ =>
          Miri.Interpreter.writeAggregate (annealAggregateHooks decls layouts) c k os d
    cast := fun c src kind ty dest =>
      let castHooks := annealCastHooksUnwindFnPtrClosure currentBody fnPtrs
      match kind with
      | .PointerCoercion .MutToConstPointer _ | .PointerCoercion .ArrayToPointer _ => do
          let st ← get
          match activeCastCoercionKind? currentBody st with
          | some "MutToConstPointer" | some "ArrayToPointer" =>
              let refinedTy := if ty == 40 then dest.layout.ty else ty
              Miri.Interpreter.Cast.cast castHooks c 16 src .PtrToPtr refinedTy dest
          | _ =>
              Miri.Interpreter.Cast.cast castHooks c 16 src kind ty dest
      | _ =>
          if isOverlayCastKind kind then
            Miri.Interpreter.Cast.cast castHooks c 16 src kind ty dest
          else
            (annealRvalueHooksLM4_1 currentBody fnPtrs).cast c src kind ty dest }
/-- Conservative `StepHooks` overlay extending `annealStepHooksLM4_1`. -/
def annealStepHooksUnwindFnPtrClosure (currentBody : CapturedMir) (callees : List CapturedMir := .nil)
    (poppedFrame : Miri.TreeBorrows.FrameState := {})
    (fnPtrs : List FnPtrEntry := .nil) :
    Miri.Interpreter.StepHooks AnnealProv Miri.Interpreter.LocalLayout Unit
      AnnealMachine Unit
      (Miri.Interpreter.RuntimePlace AnnealProv) :=
  let base := annealStepHooksLM4_1 currentBody callees poppedFrame fnPtrs
  { base with
    assign := fun choice place rvalue state =>
      if isUnwindFnPtrClosureAssign currentBody.localDecls place rvalue then
        Miri.Interpreter.runRvalue
          (Miri.Interpreter.evalRvalueIntoPlace
            (annealRvalueHooksUnwindFnPtrClosure currentBody fnPtrs)
            choice rvalue place)
          state
      else
        base.assign choice place rvalue state
    evalPlace := fun choice place skipValidity state =>
      if hasRealUnwrapUnsafeBinder place then
        Miri.Interpreter.runRvalue
          (annealEvalPlaceOverlay currentBody.localDecls currentBody.layouts place skipValidity)
          state
      else
        base.evalPlace choice place skipValidity state }
/-- State-indexed `annealStepHooksUnwindFnPtrClosure` at `(rootBody, s)`. -/
def annealStepHooksUnwindFnPtrClosureForState (rootBody : CapturedMir) (s : MachineState) : Miri.Interpreter.StepHooks AnnealProv Miri.Interpreter.LocalLayout Unit AnnealMachine Unit (Miri.Interpreter.RuntimePlace AnnealProv) :=
  annealStepHooksUnwindFnPtrClosure
    (activeMirBody rootBody s)
    s.memory.callees
    (annealPoppedFrameState s)
    s.memory.fnPtrs
/-- Direct-unwind variant combining `annealStepHooksWithDirectUnwind` with
overlay `assign` and `evalPlace`. -/
def annealStepHooksUnwindFnPtrClosureDirectUnwind (rootBody : CapturedMir) (s : MachineState) : Miri.Interpreter.StepHooks AnnealProv Miri.Interpreter.LocalLayout Unit AnnealMachine Unit (Miri.Interpreter.RuntimePlace AnnealProv) :=
  let base := annealStepHooksWithDirectUnwind rootBody s
  let overlay := annealStepHooksUnwindFnPtrClosureForState rootBody s
  { base with
    assign := overlay.assign
    evalPlace := overlay.evalPlace }
/-- Syntactic predicate for `Miri.MIR.Statement`s untouched by the overlay. -/
def stmtFreeOfUnwindFnPtrClosureOverlay (localDecls : List LocalDecl) (stmt : Miri.MIR.Statement) : Prop :=
  match stmt.kind with
  | .Assign place rvalue =>
      isUnwindFnPtrClosureAssign localDecls place rvalue = false
  | .SetDiscriminant place _ | .PlaceMention place =>
      hasRealUnwrapUnsafeBinder place = false
  | _ => True
/-- Syntactic predicate for `Miri.MIR.Body`s whose statements are overlay-free.
-/
def BodyFreeOfUnwindFnPtrClosureOverlay (localDecls : List LocalDecl) (body : Miri.MIR.Body) : Prop :=
  ∀ bb ∈ body.basicBlocks.toList,
    ∀ stmt ∈ bb.statements.toList,
      stmtFreeOfUnwindFnPtrClosureOverlay localDecls stmt
/-- Statement-level conservative extension: overlay and `LM-4.1` agree on every
overlay-free statement (including `ReifyFnPointer` and `SetDiscriminant`). -/
theorem evalStatement_overlay_eq_base_of_stmtFree {currentBody : CapturedMir} {callees : List CapturedMir} {poppedFrame : Miri.TreeBorrows.FrameState} {fnPtrs : List FnPtrEntry} {stmt : Miri.MIR.Statement}
    (hfree : stmtFreeOfUnwindFnPtrClosureOverlay currentBody.localDecls stmt) (choice : Unit) (state : AnnealStepState) :
    Miri.Interpreter.Step.evalStatement (annealStepHooksUnwindFnPtrClosure currentBody callees poppedFrame fnPtrs) choice stmt state = Miri.Interpreter.Step.evalStatement (annealStepHooksLM4_1 currentBody callees poppedFrame fnPtrs)
        choice stmt state := by
  rcases stmt with ⟨si, kind⟩
  cases kind with
  | Assign place rvalue =>
      dsimp only [stmtFreeOfUnwindFnPtrClosureOverlay] at hfree; simp [Miri.Interpreter.Step.evalStatement, annealStepHooksUnwindFnPtrClosure, hfree]
  | SetDiscriminant place variant =>
      dsimp only [stmtFreeOfUnwindFnPtrClosureOverlay] at hfree; simp [Miri.Interpreter.Step.evalStatement, annealStepHooksUnwindFnPtrClosure, hfree]
  | PlaceMention place =>
      dsimp only [stmtFreeOfUnwindFnPtrClosureOverlay] at hfree; simp [Miri.Interpreter.Step.evalStatement, annealStepHooksUnwindFnPtrClosure, hfree]
  | StorageLive _ | StorageDead _ | Intrinsic _ | ConstEvalCounter
  | FakeRead _ | AscribeUserType _ _ | Coverage _ | Nop
  | BackwardIncompatibleDropHint _ _ =>
      rfl
/-- Shared step-equality lift from statement-level equality on overlay-free
bodies. -/
private theorem step_eq_of_stmtFree_eval {PlaceTy : Type} (h1 h2 : Miri.Interpreter.StepHooks AnnealProv Miri.Interpreter.LocalLayout Unit AnnealMachine Unit PlaceTy)
    {localDecls : List LocalDecl} {state : AnnealStepState} (choice : Unit) (hfree : ∀ frame, state.stack.currentFrame? = some frame → BodyFreeOfUnwindFnPtrClosureOverlay localDecls frame.body)
    (hret : h1.returnFromCurrentFrame = h2.returnFromCurrentFrame) (hbef : h1.beforeTerminator = h2.beforeTerminator) (hterm : h1.terminator = h2.terminator) (hstmt : ∀ stmt, stmtFreeOfUnwindFnPtrClosureOverlay localDecls stmt →
      Miri.Interpreter.Step.evalStatement h1 choice stmt state = Miri.Interpreter.Step.evalStatement h2 choice stmt state) :
    Miri.Interpreter.Step.step h1 choice state = Miri.Interpreter.Step.step h2 choice state := by
  cases h1; cases h2; dsimp only at hret hbef hterm hstmt ⊢
  subst hret hbef hterm; unfold Miri.Interpreter.Step.step
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
                  obtain ⟨hlt_b, rfl⟩ := Array.getElem?_eq_some_iff.mp hbb; obtain ⟨hlt_s, rfl⟩ := Array.getElem?_eq_some_iff.mp hst
                  have hsfree := hfree frame hcf _ (Array.getElem_mem_toList hlt_b) _ (Array.getElem_mem_toList hlt_s); dsimp only; rw [hstmt _ hsfree]
/-- **Conservative-Extension Theorem (`step_overlay_eq_base_of_free`)**:
`annealStepHooksUnwindFnPtrClosure` agrees identically with
`annealStepHooksLM4_1` on every overlay-free body. -/
theorem step_overlay_eq_base_of_free {currentBody : CapturedMir} {callees : List CapturedMir} {poppedFrame : Miri.TreeBorrows.FrameState} {fnPtrs : List FnPtrEntry} {state : AnnealStepState}
    (hfree : ∀ frame, state.stack.currentFrame? = some frame → BodyFreeOfUnwindFnPtrClosureOverlay currentBody.localDecls frame.body) (choice : Unit) :
    Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosure currentBody callees poppedFrame fnPtrs) choice state = Miri.Interpreter.Step.step (annealStepHooksLM4_1 currentBody callees poppedFrame fnPtrs) choice state :=
  step_eq_of_stmtFree_eval _ _ choice hfree rfl rfl rfl (fun _ hs => evalStatement_overlay_eq_base_of_stmtFree hs choice state)
/-- State-indexed corollary of `step_overlay_eq_base_of_free` over
`annealStepHooksForState`. -/
theorem step_overlayForState_eq_baseForState_of_free {rootBody : CapturedMir} {s : MachineState} {state : AnnealStepState} (hfree : ∀ frame, state.stack.currentFrame? = some frame →
      BodyFreeOfUnwindFnPtrClosureOverlay (activeMirBody rootBody s).localDecls frame.body)
    (choice : Unit) :
    Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosureForState rootBody s) choice state = Miri.Interpreter.Step.step (annealStepHooksForState rootBody s) choice state :=
  step_overlay_eq_base_of_free hfree choice
/-- Conservative-extension corollary for the direct-unwind overlay over
`annealStepHooksWithDirectUnwind`. -/
theorem step_overlayDirectUnwind_eq_baseDirectUnwind_of_free {rootBody : CapturedMir} {s : MachineState} {state : AnnealStepState} (hfree : ∀ frame, state.stack.currentFrame? = some frame →
      BodyFreeOfUnwindFnPtrClosureOverlay (activeMirBody rootBody s).localDecls frame.body)
    (choice : Unit) :
    Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosureDirectUnwind rootBody s) choice state = Miri.Interpreter.Step.step (annealStepHooksWithDirectUnwind rootBody s) choice state :=
  step_eq_of_stmtFree_eval _ _ choice hfree rfl rfl rfl (fun stmt hs => by
    rcases stmt with ⟨si, kind⟩
    cases kind with
    | Assign place rvalue | SetDiscriminant place _ | PlaceMention place =>
        dsimp only [stmtFreeOfUnwindFnPtrClosureOverlay] at hs
        simp [Miri.Interpreter.Step.evalStatement, annealStepHooksUnwindFnPtrClosureDirectUnwind, annealStepHooksUnwindFnPtrClosureForState, annealStepHooksUnwindFnPtrClosure,
          annealStepHooksWithDirectUnwind, annealStepHooksForState, hs]
    | StorageLive _ | StorageDead _ | Intrinsic _ | ConstEvalCounter
    | FakeRead _ | AscribeUserType _ _ | Coverage _ | Nop
    | BackwardIncompatibleDropHint _ _ => rfl)

/-! ## Section 2. `C1` (`StatementKind.setDiscriminant`) Cross-Reference &
Bridge -/
/-- **`C1` Bridge 1 (`c1_step_setDiscriminant_simulation_bridge`)**. -/
theorem c1_step_setDiscriminant_simulation_bridge {body : CapturedMir} {env : EnumTypeEnv} {allocBudget : Nat} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_3 body env allocBudget s m) (hphase : ∀ p, body.phase ≠ .other p) (henv_valid : ∀ t tb vs, env t = some (tb, vs) → ValidEnumLayout t body.layouts tb vs)
    {bb : BasicBlockData} {stmt : Statement} {dstIdx : Local} {dstDecl : LocalDecl} {variantIdx : Nat} {tagBytes : Nat} {variants : List (List StructFieldDesc)} (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some stmt) (hkind : stmt.kind = .setDiscriminant ⟨dstIdx, .nil⟩ variantIdx) (hdst_decl : get? body.localDecls dstIdx = some dstDecl)
    (henv_dst : env dstDecl.ty = some (tagBytes, variants)) (hv_lt : variantIdx < variants.length) (hnot_uninit : get? s.frame.locals dstIdx ≠ some .uninit) (hpayload_compat : ∀ v_act (hv_act : v_act < variants.length) fieldVals,
        get? s.frame.locals dstIdx = some (.init (.aggregate v_act fieldVals)) → ∀ i (hi : i < (variants[variantIdx]'hv_lt).length), (∃ (hi_act : i < (variants[v_act]'hv_act).length),
            (variants[variantIdx]'hv_lt)[i]'hi = (variants[v_act]'hv_act)[i]'hi_act) ∨
          (get? fieldVals i = none ∧ ∃ b, ((variants[variantIdx]'hv_lt)[i]'hi).offset.bytes.toNat ≤ b ∧ b < ((variants[variantIdx]'hv_lt)[i]'hi).offset.bytes.toNat + ((variants[variantIdx]'hv_lt)[i]'hi).fieldLayout.size.bytes.toNat ∧
              EnumLocalByteUninit m dstIdx b)) :
    StepRelLM2_3 body env allocBudget m (stepMirFn body s) (Miri.Interpreter.Step.step (annealStepHooksLM2_3 body.localDecls body.layouts) () m) :=
  (step_setDiscriminant_simulation hstate hphase henv_valid hbb hstmt hkind hdst_decl henv_dst hv_lt hnot_uninit hpayload_compat).1
/-- **`C1` Bridge 2**. -/
theorem c1_step_setDiscriminant_uninit_simulation_bridge {body : CapturedMir} {env : EnumTypeEnv} {allocBudget : Nat} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_3 body env (allocBudget + 1) s m) (hphase : ∀ p, body.phase ≠ .other p) (henv_valid : ∀ t tb vs, env t = some (tb, vs) → ValidEnumLayout t body.layouts tb vs)
    {bb : BasicBlockData} {stmt : Statement} {dstIdx : Local} {dstDecl : LocalDecl} {variantIdx : Nat} {tagBytes : Nat} {variants : List (List StructFieldDesc)} (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some stmt) (hkind : stmt.kind = .setDiscriminant ⟨dstIdx, .nil⟩ variantIdx) (hdst_decl : get? body.localDecls dstIdx = some dstDecl)
    (henv_dst : env dstDecl.ty = some (tagBytes, variants)) (hv_lt : variantIdx < variants.length) (huninit : get? s.frame.locals dstIdx = some .uninit) :
    StepRelLM2_3 body env allocBudget m (stepMirFn body s) (Miri.Interpreter.Step.step (annealStepHooksLM2_3 body.localDecls body.layouts) () m) :=
  (step_setDiscriminant_uninit_simulation hstate hphase henv_valid hbb hstmt hkind hdst_decl henv_dst hv_lt huninit).2.1
/-- Overlay preservation on non-`UnwrapUnsafeBinder` `SetDiscriminant`. -/
theorem c1_evalStatement_overlay_eq_lm4_1 {currentBody : CapturedMir} {callees : List CapturedMir} {poppedFrame : Miri.TreeBorrows.FrameState} {fnPtrs : List FnPtrEntry}
    {place : Miri.MIR.Place} {variantIdx : Nat} (hno_unwrap : hasRealUnwrapUnsafeBinder place = false) (si : Miri.MIR.SourceInfo) (m : AnnealStepState) :
    Miri.Interpreter.Step.evalStatement (annealStepHooksUnwindFnPtrClosure currentBody callees poppedFrame fnPtrs) () ⟨si, .SetDiscriminant place variantIdx⟩ m = Miri.Interpreter.Step.evalStatement
        (annealStepHooksLM4_1 currentBody callees poppedFrame fnPtrs) () ⟨si, .SetDiscriminant place variantIdx⟩ m :=
  evalStatement_overlay_eq_base_of_stmtFree (stmt := ⟨si, .SetDiscriminant place variantIdx⟩) hno_unwrap () m

/-! ## Section 3. `C2` (`TerminatorKind.unwindResume`) & `C3`
(`TerminatorKind.unwindTerminate`) -/
/-- `annealStepHooksUnwindFnPtrClosure` agrees with `annealStepHooksLM4_1` at
every terminator and unwinding location. -/
theorem step_overlay_eq_lm4_1_at_terminator_or_unwinding {currentBody : CapturedMir} {callees : List CapturedMir} {poppedFrame : Miri.TreeBorrows.FrameState} {fnPtrs : List FnPtrEntry} {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit} (hback : m.stack.frames.back? = some topFrame) (hmode : (∃ span, topFrame.location = .unwinding span) ∨ (∃ loc bb,
        topFrame.location = .mir loc ∧ topFrame.body.basicBlocks[loc.block]? = some bb ∧ bb.statements[loc.statementIndex]? = none)) :
    Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosure currentBody callees poppedFrame fnPtrs) () m = Miri.Interpreter.Step.step (annealStepHooksLM4_1 currentBody callees poppedFrame fnPtrs) () m := by
  unfold Miri.Interpreter.Step.step Miri.Interpreter.Stack.currentFrame?; rw [hback]; dsimp only [Id.run]
  rcases hmode with ⟨span, hloc⟩ | ⟨loc, bb, hloc, hbb, hst⟩
  · rw [hloc]; rfl
  · rw [hloc]; dsimp only; rw [hbb]; dsimp only; rw [hst]; rfl
theorem step_overlay_eq_forState_at_terminator {rootBody : CapturedMir} {s : MachineState} {m : AnnealStepState} {bb : BasicBlockData} (hstate : MultiFrameStateRel rootBody s m)
    (hbb : get? (activeMirBody rootBody s).basicBlocks s.frame.blockIdx = some bb) (hstmt_none : get? bb.statements s.frame.stmtIdx = none) :
    Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosureForState rootBody s) () m = Miri.Interpreter.Step.step (annealStepHooksForState rootBody s) () m := by
  rcases hstate with ⟨topFrame, hback, _, _, _, hlinks, _, _, _, _, _, _, _, _⟩
  have hforall := hlinks.toForall2
  rcases hmfs : m.stack.frames.toList.reverse with _ | ⟨tf₀, _⟩
  · rw [hmfs] at hforall; cases hforall
  · rw [hmfs] at hforall
    cases hforall with
    | cons hframe _ =>
        have hback₀ : m.stack.frames.back? = some tf₀ := by rw [array_eq_of_toList_reverse_cons hmfs]; simp
        have htf : topFrame = tf₀ := Option.some.inj (hback.symm.trans hback₀)
        subst htf; exact step_overlay_eq_lm4_1_at_terminator_or_unwinding hback (Or.inr ⟨⟨s.frame.blockIdx, s.frame.stmtIdx⟩, translateBasicBlockData bb, hframe.location_eq,
            by rw [hframe.body_eq, translateBody_basicBlocks_getElem?, hbb]; rfl, by rw [translateBasicBlockData_statements_getElem?, hstmt_none]; rfl⟩)
/-- `k`-step `Miri.Interpreter.Step.step` unwinding trace under the overlay. -/
inductive MiriOverlayUnwindSteps (rootBody : CapturedMir) : Nat → MachineState → AnnealStepState → Miri.Interpreter.StepResult AnnealStepState Bool → Prop where
  | single (s₀ : MachineState) (m₀ m₁ : AnnealStepState)
      (out : Except Miri.Interpreter.StepError Bool) :
      Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosureForState rootBody s₀) () m₀ = (m₁, out) → MiriOverlayUnwindSteps rootBody 1 s₀ m₀ (m₁, out)
  | cons {k : Nat} (s₀ s₁ : MachineState) (m₀ m₁ : AnnealStepState)
      (res : Miri.Interpreter.StepResult AnnealStepState Bool) :
      s₀.memory.callStack ≠ [] → Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosureForState rootBody s₀) () m₀ = (m₁, .ok true) → UnwindingStateRel rootBody s₁ m₁ → MiriOverlayUnwindSteps rootBody k s₁ m₁ res →
      MiriOverlayUnwindSteps rootBody (k + 1) s₀ m₀ res
theorem step_overlay_eq_forState_at_unwinding {rootBody : CapturedMir} {s : MachineState} {m : AnnealStepState} (hunw : UnwindingStateRel rootBody s m) : Miri.Interpreter.Step.step
      (annealStepHooksUnwindFnPtrClosureForState rootBody s) () m =
    Miri.Interpreter.Step.step (annealStepHooksForState rootBody s) () m := by
  rcases hunw with ⟨m_mir, topFrame, span, hback_mir, rfl, _⟩
  have hne : m_mir.stack.frames ≠ #[] := by intro hemp; rw [hemp] at hback_mir; cases hback_mir
  have hback_unw : (m_mir.stack.frames.pop.push { topFrame with location := .unwinding span }).back? = some { topFrame with location := .unwinding span } := by simp
  exact step_overlay_eq_lm4_1_at_terminator_or_unwinding hback_unw (Or.inl ⟨span, rfl⟩)
theorem miriOverlayUnwindSteps_of_unwinding {rootBody : CapturedMir} {k : Nat} {s : MachineState} {m : AnnealStepState} {res : Miri.Interpreter.StepResult AnnealStepState Bool} (hunw : UnwindingStateRel rootBody s m)
    (hsteps : MiriUnwindSteps rootBody k s m res) :
    MiriOverlayUnwindSteps rootBody k s m res := by
  induction hsteps with
  | single s₀ m₀ m₁ out hstep =>
      exact .single s₀ m₀ m₁ out ((step_overlay_eq_forState_at_unwinding hunw).trans hstep)
  | cons s₀ s₁ m₀ m₁ res hne hstep hunw₁ _ ih =>
      exact .cons s₀ s₁ m₀ m₁ res hne ((step_overlay_eq_forState_at_unwinding hunw).trans hstep) hunw₁ (ih hunw₁)
theorem miriOverlayUnwindSteps_of_terminator {rootBody : CapturedMir} {k : Nat} {s : MachineState} {m : AnnealStepState} {bb : BasicBlockData}
    {res : Miri.Interpreter.StepResult AnnealStepState Bool} (hstate : MultiFrameStateRel rootBody s m) (hbb : get? (activeMirBody rootBody s).basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none) (hsteps : MiriUnwindSteps rootBody k s m res) :
    MiriOverlayUnwindSteps rootBody k s m res := by
  cases hsteps with
  | single _ _ m₁ out hstep =>
      exact .single s m m₁ out ((step_overlay_eq_forState_at_terminator hstate hbb hstmt_none).trans hstep)
  | cons _ s₁ _ m₁ res hne hstep hunw₁ hrest =>
      exact .cons s s₁ m m₁ res hne ((step_overlay_eq_forState_at_terminator hstate hbb hstmt_none).trans hstep) hunw₁ (miriOverlayUnwindSteps_of_unwinding hunw₁ hrest)
/-- **`C2` Regimes (a) & (c)**. -/
theorem step_unwindResume_cleanup_and_unreachable_simulation {rootBody : CapturedMir} {s : MachineState} {m : AnnealStepState} {cf : SavedCallerFrame} {restStack : List SavedCallerFrame} (hstate : MultiFrameStateRel rootBody s m)
    (hstack : s.memory.callStack = cf :: restStack) (hva : ∀ tf, m.stack.frames.back? = some tf → tf.vaList = #[]) (hphase : ∀ p, (activeMirBody rootBody s).phase ≠ .other p) {bb : BasicBlockData} {decl0 : LocalDecl}
    (hbb : get? (activeMirBody rootBody s).basicBlocks s.frame.blockIdx = some bb) (hstmt_none : get? bb.statements s.frame.stmtIdx = none) (hstmt_len : s.frame.stmtIdx = length bb.statements)
    (hcleanup : bb.isCleanup = true) (hterm : bb.terminator.kind = .unwindResume) (hdecl0 : get? (activeMirBody rootBody s).localDecls 0 = some decl0) (hlive0 : get? s.frame.locals 0 ≠ some .dead) (hunwind :
      cf.returnUnwind = .unreachable ∨ ∃ cleanupBb, cf.returnUnwind = .cleanup cleanupBb) :
    StepRelMultiFrame rootBody m (stepMirFn rootBody s) (Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosureForState rootBody s) () m) := by
  rw [step_overlay_eq_forState_at_terminator hstate hbb hstmt_none]; exact step_terminator_unwindResume_callee_simulation hstate hstack hva hphase hbb hstmt_none hstmt_len hcleanup hterm hdecl0 hlive0 hunwind s.memory.fnPtrs
/-- **`C2` Regimes (b), (a), (c), (d), (e) Multi-Frame Propagation**. -/
theorem step_unwindResume_continue_multiFrame_simulation {rootBody : CapturedMir} {s : MachineState} {m : AnnealStepState} (hstate : MultiFrameStateRel rootBody s m)
    (hwf : UnwindChainWf rootBody s m) (hphase : ∀ p, (activeMirBody rootBody s).phase ≠ .other p) {bb : BasicBlockData} (hbb : get? (activeMirBody rootBody s).basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none) (hstmt_len : s.frame.stmtIdx = length bb.statements) (hcleanup : bb.isCleanup = true) (hterm : bb.terminator.kind = .unwindResume) : (∀ s', stepMirFn rootBody s = .step s' →
      ∃ k m', 1 ≤ k ∧ k ≤ s.memory.callStack.length ∧ s'.memory.activeProtectors = releaseCallProtectors k s.memory.callStack s.memory.activeProtectors ∧ MiriOverlayUnwindSteps rootBody k s m (m', .ok true) ∧
        MultiFrameStateRel rootBody s' m') ∧
    (stepMirFn rootBody s = .fail .ub → ∃ k m', 1 ≤ k ∧ k ≤ s.memory.callStack.length ∧ MiriOverlayUnwindSteps rootBody k s m (m', .error (.undefinedBehavior "unwinding past a frame that does not allow unwinding"))) ∧
    (stepMirFn rootBody s = .retOutcome .panic → ∃ m', MiriOverlayUnwindSteps rootBody (s.memory.callStack.length + 1) s m (m', .error (.undefinedBehavior "unwinding past the topmost stack frame"))) ∧
    (stepMirFn rootBody s = .retOutcome .abort → ∃ k m', 1 ≤ k ∧ k ≤ s.memory.callStack.length ∧ MiriOverlayUnwindSteps rootBody k s m (m', .error (.unsupported "unwindTerminate"))) := by
  obtain ⟨hstep, hub, hpan, habort⟩ := step_terminator_unwindResume_multiFrame_simulation hstate hwf hphase hbb hstmt_none hstmt_len hcleanup hterm; refine ⟨?_, ?_, ?_, ?_⟩
  · intro s' hs'; obtain ⟨k, m', hk1, hk2, hprot, hm, hrel⟩ := hstep s' hs'; exact ⟨k, m', hk1, hk2, hprot, miriOverlayUnwindSteps_of_terminator hstate hbb hstmt_none hm, hrel⟩
  · intro hs; obtain ⟨k, m', hk1, hk2, hm⟩ := hub hs; exact ⟨k, m', hk1, hk2, miriOverlayUnwindSteps_of_terminator hstate hbb hstmt_none hm⟩
  · intro hs; obtain ⟨m', hm⟩ := hpan hs; exact ⟨m', miriOverlayUnwindSteps_of_terminator hstate hbb hstmt_none hm⟩
  · intro hs; obtain ⟨k, m', hk1, hk2, hm⟩ := habort hs; exact ⟨k, m', hk1, hk2, miriOverlayUnwindSteps_of_terminator hstate hbb hstmt_none hm⟩
/-- **`C2` Regime (d) Direct-Unwind Lockstep `.abort` Simulation**. -/
theorem step_unwindResume_terminate_directUnwind_simulation {rootBody : CapturedMir} {s : MachineState} {m : AnnealStepState} {cf : SavedCallerFrame} {restStack : List SavedCallerFrame} (hstate : MultiFrameStateRel rootBody s m)
    (hstack : s.memory.callStack = cf :: restStack) (hva : ∀ tf, m.stack.frames.back? = some tf → tf.vaList = #[]) (hphase : ∀ p, (activeMirBody rootBody s).phase ≠ .other p) {bb : BasicBlockData} {decl0 : LocalDecl}
    (hbb : get? (activeMirBody rootBody s).basicBlocks s.frame.blockIdx = some bb) (hstmt_none : get? bb.statements s.frame.stmtIdx = none) (hstmt_len : s.frame.stmtIdx = length bb.statements)
    (hcleanup : bb.isCleanup = true) (hterm : bb.terminator.kind = .unwindResume) (hdecl0 : get? (activeMirBody rootBody s).localDecls 0 = some decl0) (hlive0 : get? s.frame.locals 0 ≠ some .dead)
    (hterminate : cf.returnUnwind = .terminate) :
    stepMirFn rootBody s = MirStepNode.retOutcome .abort ∧ ∃ m', Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosureDirectUnwind rootBody s) () m =
      (m', .error (.termination (.abort "panic in a function that cannot unwind"))) := by
  have ha : stepMirFn rootBody s = MirStepNode.retOutcome .abort := by
    rw [stepMirFn_activeMirBody_eq rootBody s hphase]; have hbeq : (s.frame.stmtIdx == length bb.statements) = true := by simp [hstmt_len]
    simp only [hbb, hstmt_none, hbeq, ↓reduceIte]; unfold evalTerminator; rw [hterm, hstack]; simp [unwindFromCallStack, hterminate]
  rcases hstate with ⟨topFrame, hback, _, _, _, hlinks, hdisj, _, _, _, _, _, _, _⟩
  generalize hmfs : m.stack.frames.toList.reverse = mfs at hlinks
  generalize hprots : s.memory.activeProtectors = prots at hlinks
  generalize hcur : activeMirBody rootBody s = curBody at hlinks
  rw [hstack] at hlinks
  cases hlinks with
  | cons _ _ _ _ _ _ calleeMf callerMf restMfs hretCont _ hfr_callee _ _ _ _ =>
      subst hcur; have harr := array_eq_of_toList_reverse_cons hmfs; have hback_c : m.stack.frames.back? = some calleeMf := by rw [harr]; simp
      have harr_two : m.stack.frames = ⟨(restMfs.reverse ++ [callerMf]) ++ [calleeMf]⟩ := by rw [harr]; apply Array.ext'; simp [List.reverse_cons]
      have hd_callee : MemoryAllocDisjoint calleeMf := by
        apply hdisj.intra_frame calleeMf
        rw [harr]; simp
      have hretCont' : calleeMf.returnContinuation = .goto (if cf.isDiverging then none else some cf.returnTarget) (.Terminate .Abi) := by rw [hretCont, hterminate]; rfl
      let bt' := popFrameBorrowTracker (annealPoppedFrameState s) m.machine.borrowTracker; let m₀ : AnnealStepState := { stack := m.stack, machine := { m.machine with borrowTracker := bt' } }
      have hfr_callee' := hfr_callee.of_borrowTracker (bt' := bt'); obtain ⟨slot0, mls0, _, _, hslot0, hmls0, _, hloc0⟩ := hfr_callee'.lookup_local hdecl0; have hget0 := frame_getLocal_of_getElem? calleeMf 0 mls0 hmls0
      have hop0 : ∃ op0, (annealControlHooksWithDirectUnwind (activeMirBody rootBody s).localDecls (activeMirBody rootBody s).layouts (annealPoppedFrameState s)).returnOperand () m = (m, .ok op0) := by
        cases hloc0 with
        | dead _ _ => exact False.elim (hlive0 hslot0)
        | immediate _ imm0 _ _ _ =>
            exact ⟨.immediate imm0, by
              unfold annealControlHooksWithDirectUnwind; exact annealControlHooks_returnOperand_cleanup_live_back (poppedFrame := annealPoppedFrameState s) hback_c hfr_callee'.body_eq hfr_callee'.location_eq hbb hcleanup hget0 hdecl0⟩
        | indirect _ mp0 _ _ _ _ =>
            exact ⟨.indirect mp0, by
              unfold annealControlHooksWithDirectUnwind; exact annealControlHooks_returnOperand_cleanup_live_back (poppedFrame := annealPoppedFrameState s) hback_c hfr_callee'.body_eq hfr_callee'.location_eq hbb hcleanup hget0 hdecl0⟩
      obtain ⟨op0, hop0⟩ := hop0
      have hpop : (annealControlHooksWithDirectUnwind (activeMirBody rootBody s).localDecls (activeMirBody rootBody s).layouts (annealPoppedFrameState s)).popFrame () m =
          ({ m₀ with stack := ⟨⟨restMfs.reverse ++ [callerMf]⟩⟩ }, .ok calleeMf) := by
        unfold annealControlHooksWithDirectUnwind annealControlHooksLM4_1; exact annealPopFrameLM4_1_callee_append_singleton harr_two
      have hclean : (annealControlHooksWithDirectUnwind (activeMirBody rootBody s).localDecls (activeMirBody rootBody s).layouts (annealPoppedFrameState s)).cleanupFrame ()
            true calleeMf { m₀ with stack := ⟨⟨restMfs.reverse ++ [callerMf]⟩⟩ } =
          ({ stack := ⟨⟨restMfs.reverse ++ [callerMf]⟩⟩, machine := { m₀.machine with memory := deallocFrameLocals m₀.machine.memory calleeMf } }, .ok .normal) := by
        unfold annealControlHooksWithDirectUnwind annealControlHooksLM4_1; dsimp only
        rw [cleanupStackFrame_callee_goto_any_unwinding (activeMirBody rootBody s).localDecls (activeMirBody rootBody s).layouts ⟨⟨restMfs.reverse ++ [callerMf]⟩⟩ m₀.machine.memory true calleeMf hretCont' (hva calleeMf hback_c)
          hfr_callee'.allSlotsAllocLive hd_callee.slotsAllocDisjoint]
      have hsize_ne : (m.stack.frames.size == 1) = false := by rw [harr]; simp [List.reverse_cons]
      refine ⟨ha, { stack := ⟨⟨restMfs.reverse ++ [{ callerMf with location := .unwinding defaultSpanRef }]⟩⟩, machine := { m₀.machine with memory := deallocFrameLocals m₀.machine.memory calleeMf } }, ?_⟩
      have hstep_term : Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosureDirectUnwind rootBody s) () m =
          let res := Miri.Interpreter.ControlFlow.evalTerminator (annealTerminatorHooksWithDirectUnwind (activeMirBody rootBody s) s.memory.callees (annealPoppedFrameState s) s.memory.fnPtrs) () (translateTerminator bb.terminator) m
          (res.1, res.2.map fun _ => true) := by
        unfold Miri.Interpreter.Step.step Miri.Interpreter.Stack.currentFrame?; rw [hback_c]; dsimp only; rw [hfr_callee'.location_eq, hfr_callee'.body_eq]; dsimp only; rw [translateBody_basicBlocks_getElem?, hbb]
        dsimp only [Option.map]; rw [translateBasicBlockData_statements_getElem?, hstmt_none]; rfl
      rw [hstep_term]; unfold translateTerminator Miri.Interpreter.ControlFlow.evalTerminator annealTerminatorHooksWithDirectUnwind; rw [hterm]; dsimp only [translateTerminatorKind]
      unfold Miri.Interpreter.ControlFlow.returnFromCurrentFrame Miri.Interpreter.Stack.currentFrame?; rw [hback_c]; dsimp only; rw [hfr_callee'.location_eq, hfr_callee'.body_eq]; dsimp only
      rw [translateBody_basicBlocks_getElem?, hbb]; dsimp only [Option.map, translateBasicBlockData]
      have hbodySpan : ∀ f, (annealControlHooksWithDirectUnwind (activeMirBody rootBody s).localDecls (activeMirBody rootBody s).layouts (annealPoppedFrameState s)).bodySpan f = .ok defaultSpanRef := fun _ => rfl
      have htermHook : ∀ st, (annealControlHooksWithDirectUnwind (activeMirBody rootBody s).localDecls (activeMirBody rootBody s).layouts (annealPoppedFrameState s)).unwindTerminate () .Abi st =
            (st, .error (.termination (.abort "panic in a function that cannot unwind"))) :=
        fun _ => rfl
      simp only [Id.run, Bind.bind, Pure.pure, bne_self_eq_false, Bool.true_and, Bool.false_eq_true, ↓reduceIte, Bool.not_true, hcleanup, hsize_ne, hop0, hpop, hclean, hretCont', Miri.Interpreter.ControlFlow.unwindToBlock,
        Miri.Interpreter.ControlFlow.setLocation, Miri.Interpreter.Stack.currentFrame?, array_back?_append_singleton, array_pop_append_singleton, hbodySpan, htermHook, Except.map]
      congr 3
      apply Array.ext'
      simp
/-- **`C2` Regime (e) (`unwindResume_root_panic_vs_ub_divergence`)**. -/
theorem unwindResume_root_panic_vs_ub_divergence {rootBody : CapturedMir} {s : MachineState} {m : AnnealStepState} (hstate : MultiFrameStateRel rootBody s m)
    (hstack : s.memory.callStack = .nil) (hphase : ∀ p, rootBody.phase ≠ .other p) {bb : BasicBlockData} (hbb : get? rootBody.basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none) (hstmt_len : s.frame.stmtIdx = length bb.statements) (hcleanup : bb.isCleanup = true) (hterm : bb.terminator.kind = .unwindResume) :
    unwindFromCallStack s.memory.callStack s.memory = .halted .panic ∧ stepMirFn rootBody s = MirStepNode.retOutcome .panic ∧ (Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosureForState rootBody s) () m).2 =
      .error (.undefinedBehavior "unwinding past the topmost stack frame") := by
  have hdiv := step_terminator_unwindResume_root_panic_vs_ub_divergence hstate hstack hphase hbb hstmt_none hstmt_len hcleanup hterm s.memory.fnPtrs; have hstate₀ := hstate
  rcases hstate with ⟨_, _, hcal_root, _, _, _, _, _, _, _, _, _, _, _⟩
  have hact : activeMirBody rootBody s = rootBody := by
    unfold activeMirBody
    rcases hcal_root hstack with hnone | hsome <;> simp [*]
  have hbb' : get? (activeMirBody rootBody s).basicBlocks s.frame.blockIdx = some bb := by rw [hact]; exact hbb
  refine ⟨by rw [hstack]; rfl, hdiv.1, ?_⟩
  rw [step_overlay_eq_forState_at_terminator hstate₀ hbb' hstmt_none]; exact hdiv.2
/-- **`C3` Canonical Boundary**. -/
theorem step_unwindTerminate_canonical_boundary {rootBody : CapturedMir} {s : MachineState} {m : AnnealStepState} (hstate : MultiFrameStateRel rootBody s m)
    (hphase : ∀ p, (activeMirBody rootBody s).phase ≠ .other p) {bb : BasicBlockData} (hbb : get? (activeMirBody rootBody s).basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none) (hstmt_len : s.frame.stmtIdx = length bb.statements) (hterm : bb.terminator.kind = .unwindTerminate) :
    stepMirFn rootBody s = MirStepNode.retOutcome .abort ∧ Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosureForState rootBody s) () m = (m, .error (.unsupported "unwindTerminate")) := by
  have hbase := step_terminator_unwindTerminate_abort_vs_unsupported hstate hphase hbb hstmt_none hstmt_len hterm; exact ⟨hbase.1, (step_overlay_eq_forState_at_terminator hstate hbb hstmt_none).trans hbase.2⟩
/-- **`C3` Direct-Unwind Lockstep `.abort` Simulation**. -/
theorem step_unwindTerminate_directUnwind_abort_simulation {rootBody : CapturedMir} {s : MachineState} {m : AnnealStepState} (hstate : MultiFrameStateRel rootBody s m)
    (hphase : ∀ p, (activeMirBody rootBody s).phase ≠ .other p) {bb : BasicBlockData} (hbb : get? (activeMirBody rootBody s).basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none) (hstmt_len : s.frame.stmtIdx = length bb.statements) (hterm : bb.terminator.kind = .unwindTerminate) :
    stepMirFn rootBody s = MirStepNode.retOutcome .abort ∧ Miri.Interpreter.Step.step (annealStepHooksWithDirectUnwind rootBody s) () m = (m, .error (.termination (.abort "panic in a function that cannot unwind"))) ∧
    Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosureDirectUnwind rootBody s) () m = (m, .error (.termination (.abort "panic in a function that cannot unwind"))) := by
  have hsim := step_terminator_unwindTerminate_termination_abort_simulation hstate hphase hbb hstmt_none hstmt_len hterm
  rcases hstate with ⟨topFrame, hback, _, _, _, hlinks, _, _, _, _, _, _, _, _⟩
  have hforall := hlinks.toForall2
  rcases hmfs : m.stack.frames.toList.reverse with _ | ⟨tf₀, _⟩
  · rw [hmfs] at hforall; cases hforall
  · rw [hmfs] at hforall
    cases hforall with
    | cons hframe _ =>
        have hback₀ : m.stack.frames.back? = some tf₀ := by rw [array_eq_of_toList_reverse_cons hmfs]; simp
        have htf : topFrame = tf₀ := Option.some.inj (hback.symm.trans hback₀); subst htf
        have heq : Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosureDirectUnwind rootBody s) () m = Miri.Interpreter.Step.step (annealStepHooksWithDirectUnwind rootBody s) () m := by
          unfold Miri.Interpreter.Step.step Miri.Interpreter.Stack.currentFrame?; rw [hback]; dsimp only [Id.run]; rw [hframe.location_eq, hframe.body_eq]; dsimp only
          rw [translateBody_basicBlocks_getElem?, hbb]; dsimp only [Option.map]; rw [translateBasicBlockData_statements_getElem?, hstmt_none]; rfl
        exact ⟨hsim.1, hsim.2.1, heq.trans hsim.2.1⟩
private theorem step_eq_fst_of_snd {α β : Type} {p : α × β} {b : β} (h : p.2 = b) : p = (p.1, b) := Prod.ext rfl h
section UnwindWitnesses
open WitnessLM4_1
private def witUnwind3MiriStep1 : AnnealStepState := (Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosureForState witCallerBody witUnwind3Anneal) () witUnwind3Miri).1
private def witUnwind3MiriStep2 : AnnealStepState := (Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosure witMidCallerBody witUnwind3Anneal.memory.callees {}) () witUnwind3MiriStep1).1
/-- **Concrete `C2` & `C3` Witness Suite**: exercises 3-frame `.continue_` ->
`.cleanup` unwinding, non-vacuous callee-borrow disabling &
`GlobalState.endCall` protector release, `.unreachable` UB, root `.panic`
vs. Miri UB divergence, and both canonical & direct-unwind `.terminate` /
`UnwindTerminate`. -/
theorem w_c2_c3_unwind_all_regimes_and_terminate :
    let callerBor : BorrowEntry := { tag := 10, parentTag := none, targetLocal := 0, targetProjection := .nil, perm := .frozen, protector := some 1, targetFrameDepth := 0 }
    let calleeBor : BorrowEntry := { tag := 20, parentTag := none, targetLocal := 0, targetProjection := .nil, perm := .frozen, protector := some 2, targetFrameDepth := 1 }; let sCleanBase := mkWitUnwindAnneal (.cleanup 1)
    let savedCf : SavedCallerFrame := { (mkWitUnwindSavedCaller (.cleanup 1)) with calleeProtectors := [1] }
    let sCleanBor : MachineState :=
      { sCleanBase with
        memory :=
          { sCleanBase.memory with
            callStack := [savedCf], borrows := [calleeBor, callerBor], activeProtectors := [2, 1], nextProtector := 3 } }
    let btInit : Miri.Interpreter.MachineHooks.BorrowState :=
      { global := { protectedTags := { entries := #[(⟨10, by decide⟩, .StrongProtector), (⟨20, by decide⟩, .StrongProtector)] }, rootPointerTags := #[(⟨1, by decide⟩, ⟨5, by decide⟩)] }, retagMode := .Default }
    let mCleanBor : AnnealStepState :=
      { mkWitUnwindMiri (.Cleanup 1) with
        machine := { AnnealMachine.empty with borrowTracker := some btInit } }
    let mCleanRes := Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosureForState witCallerBody sCleanBor) () mCleanBor
    (∃ s' m₁ m₂, stepMirFn witCallerBody witUnwind3Anneal = .step s' ∧ s'.frame.blockIdx = 1 ∧ s'.memory.activeProtectors = [] ∧ Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosureForState witCallerBody witUnwind3Anneal)
        () witUnwind3Miri = (m₁, .ok true) ∧
      m₁.stack.frames.size = 2 ∧ Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosure witMidCallerBody witUnwind3Anneal.memory.callees {}) () m₁ = (m₂, .ok true) ∧ m₂.stack.frames.size = 1 ∧
      (m₂.stack.currentFrame?.map (·.location)) = some (.mir ⟨1, 0⟩)) ∧
    (∃ s', stepMirFn witCallerBody sCleanBor = .step s' ∧ s'.frame.blockIdx = 1 ∧ s'.memory.activeProtectors = [1] ∧ (lookupBorrow s'.memory.borrows 20).map (·.perm) = some .disabled ∧
      (lookupBorrow s'.memory.borrows 10).map (·.perm) = some .frozen ∧ mCleanRes.2 = .ok true ∧ (mCleanRes.1.stack.currentFrame?.map (·.location)) = some (.mir ⟨1, 0⟩) ∧
      (mCleanRes.1.machine.borrowTracker.map (·.global.protectedTags.entries)) = some #[(⟨10, by decide⟩, .StrongProtector)]) ∧
    (stepMirFn witCallerBody (mkWitUnwindAnneal .unreachable) = .fail .ub ∧ (Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosureForState witCallerBody (mkWitUnwindAnneal .unreachable)) () (mkWitUnwindMiri .Unreachable)).2 =
      .error (.undefinedBehavior "unwinding past a frame that does not allow unwinding")) ∧
    (stepMirFn witUnwindCalleeBody witUnwindRootAnneal = .retOutcome .panic ∧ (Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosureForState witUnwindCalleeBody witUnwindRootAnneal) () witUnwindRootMiri).2 =
      .error (.undefinedBehavior "unwinding past the topmost stack frame")) ∧
    (stepMirFn witCallerBody (mkWitUnwindAnneal .terminate) = .retOutcome .abort ∧ (Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosureForState witCallerBody (mkWitUnwindAnneal .terminate))
        () (mkWitUnwindMiri (.Terminate .Abi))).2 =
      .error (.unsupported "unwindTerminate") ∧ (Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosureDirectUnwind witCallerBody (mkWitUnwindAnneal .terminate)) () (mkWitUnwindMiri (.Terminate .Abi))).2 =
      .error (.termination (.abort "panic in a function that cannot unwind")) ∧ stepMirFn witAssertTermPanicBody (mkWitAssertTermPanicAnneal 0 .uninit) = .retOutcome .abort ∧ (Miri.Interpreter.Step.step
        (annealStepHooksUnwindFnPtrClosureForState witAssertTermPanicBody (mkWitAssertTermPanicAnneal 0 .uninit)) () (mkWitAssertTermPanicMiri 0 ⟨.live (.immediate .uninit), none⟩)).2 =
      .error (.unsupported "unwindTerminate") ∧ (Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosureDirectUnwind witAssertTermPanicBody (mkWitAssertTermPanicAnneal 0 .uninit))
        () (mkWitAssertTermPanicMiri 0 ⟨.live (.immediate .uninit), none⟩)).2 =
      .error (.termination (.abort "panic in a function that cannot unwind"))) := by
  refine ⟨⟨_, witUnwind3MiriStep1, witUnwind3MiriStep2, rfl, rfl, rfl, step_eq_fst_of_snd rfl, rfl, step_eq_fst_of_snd rfl, rfl, rfl⟩, ⟨_, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩,
    ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩ <;> (with_unfolding_all rfl)
end UnwindWitnesses

/-! ## Section 4. `C4` (`StatementKind.coverage`) & `C5`
(`StatementKind.backwardIncompatibleDropHint`) -/
/-- Trace-only statement kinds (`coverage` and `backwardIncompatibleDropHint`).
-/
def IsTraceOnlyStmt (stmt : Statement) : Prop := stmt.kind = .coverage ∨ ∃ place, stmt.kind = .backwardIncompatibleDropHint place
theorem evalStmt_traceOnly {s : MachineState} {stmt : Statement} (h : IsTraceOnlyStmt stmt) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalStmt s stmt localDecls layouts = MirStepNode.step (advanceStmt s s.frame.locals) := by
  rcases h with h | ⟨_, h⟩ <;> (unfold evalStmt; rw [h])
theorem miri_evalStatement_traceOnly {PlaceTy : Type} (hooks : Miri.Interpreter.StepHooks AnnealProv Miri.Interpreter.LocalLayout Unit AnnealMachine Unit PlaceTy) {stmt : Statement} (h : IsTraceOnlyStmt stmt) (m : AnnealStepState) :
    Miri.Interpreter.Step.evalStatement hooks () (translateStmt stmt) m = (m, .ok ()) := by
  rcases h with h | ⟨_, h⟩ <;>
    (unfold Miri.Interpreter.Step.evalStatement translateStmt; rw [h]; rfl)
theorem miri_step_traceOnly_multiFrame {PlaceTy : Type} (hooks : Miri.Interpreter.StepHooks AnnealProv Miri.Interpreter.LocalLayout Unit AnnealMachine Unit PlaceTy) {body : CapturedMir} {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit} {restMfs : List (Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)}
    {blockIdx stmtIdx : Nat} {bb : BasicBlockData} {stmt : Statement} (hframes : m.stack.frames = ⟨restMfs.reverse ++ [topFrame]⟩) (hbody : topFrame.body = translateBody body)
    (hloc : topFrame.location = .mir ⟨blockIdx, stmtIdx⟩) (hbb : get? body.basicBlocks blockIdx = some bb) (hstmt : get? bb.statements stmtIdx = some stmt) (htrace : IsTraceOnlyStmt stmt) :
    Miri.Interpreter.Step.step hooks () m = ({ m with stack := ⟨⟨restMfs.reverse ++ [{ topFrame with location := .mir ⟨blockIdx, stmtIdx + 1⟩ }]⟩⟩ }, .ok true) := by
  have hback : m.stack.frames.back? = some topFrame := by rw [hframes]; simp
  have hsize : m.stack.frames.size - 1 < m.stack.frames.size := by rw [hframes]; simp
  unfold Miri.Interpreter.Step.step Miri.Interpreter.Stack.currentFrame?; rw [hback]; dsimp only; rw [hloc, hbody]; dsimp only; rw [translateBody_basicBlocks_getElem?, hbb]
  dsimp only [Option.map]; rw [translateBasicBlockData_statements_getElem?, hstmt]; dsimp only [Option.map]; rw [miri_evalStatement_traceOnly hooks htrace m]
  simp only [Id.run, hback, hloc, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hsize, ↓reduceDIte, pure]
  congr 2; congr 1; apply Array.ext'; simp [hframes, hbody]
/-- **Hook-Independent Multi-Frame Trace-Only Simulation**. -/
theorem step_traceOnly_stmt_multiFrame_simulation {PlaceTy : Type} (hooks : Miri.Interpreter.StepHooks AnnealProv Miri.Interpreter.LocalLayout Unit AnnealMachine Unit PlaceTy)
    {rootBody : CapturedMir} {s : MachineState} {m : AnnealStepState} (hstate : MultiFrameStateRel rootBody s m) (hphase : ∀ p, (activeMirBody rootBody s).phase ≠ .other p) {bb : BasicBlockData} {stmt : Statement}
    (hbb : get? (activeMirBody rootBody s).basicBlocks s.frame.blockIdx = some bb) (hstmt : get? bb.statements s.frame.stmtIdx = some stmt) (htrace : IsTraceOnlyStmt stmt) :
    StepRelMultiFrame rootBody m (stepMirFn rootBody s) (Miri.Interpreter.Step.step hooks () m) ∧ stepMirFn rootBody s = MirStepNode.step (advanceStmt s s.frame.locals) ∧
    (Miri.Interpreter.Step.step hooks () m).1.machine = m.machine := by
  rcases hstate with
    ⟨topFrame, hback, hcal_root, hcal_nonroot, _, hlinks, hdisj, htb, hvalid, hcid_pos, hcid_act, hcid_bor, hbt, hbfv⟩
  have hforall := hlinks.toForall2
  rcases hmfs : m.stack.frames.toList.reverse with _ | ⟨tf₀, restMfs⟩
  · rw [hmfs] at hforall; cases hforall
  · rw [hmfs] at hlinks hforall
    cases hforall with
    | cons hframe _ =>
        dsimp only at hframe; have harr := array_eq_of_toList_reverse_cons hmfs; have hback₀ : m.stack.frames.back? = some tf₀ := by rw [harr]; simp
        have htf : topFrame = tf₀ := Option.some.inj (hback.symm.trans hback₀); subst htf
        have ha : stepMirFn rootBody s = MirStepNode.step (advanceStmt s s.frame.locals) := by rw [stepMirFn_activeMirBody_eq rootBody s hphase]; simp only [hbb, hstmt]; exact evalStmt_traceOnly htrace _ _
        have hm := miri_step_traceOnly_multiFrame hooks harr hframe.body_eq hframe.location_eq hbb hstmt htrace; let topFrame' := { topFrame with location := .mir ⟨s.frame.blockIdx, s.frame.stmtIdx + 1⟩ }
        have hfr' : FrameRel (activeMirBody rootBody s) m.machine (advanceStmt s s.frame.locals).frame topFrame' := ⟨hframe.body_eq, rfl, hframe.af_locals_len, hframe.mf_locals_size, hframe.locals_rel⟩
        have hlinks' : CallerStackLinksRel rootBody m.machine (activeMirBody rootBody s) (advanceStmt s s.frame.locals).frame s.memory.callStack s.memory.activeProtectors (topFrame' :: restMfs) :=
          hlinks.update_top_frame rfl rfl rfl hfr' (fun mp0 lay0 h0 => ⟨⟨lay0, h0⟩, Or.inl rfl⟩)
        have hd_tf : MemoryAllocDisjoint topFrame' := hdisj.intra_frame topFrame (by rw [harr]; simp)
        have hdisj' : MultiFrameAllocDisjoint ⟨restMfs.reverse ++ [topFrame']⟩ := by rw [harr] at hdisj; exact hdisj.replace_top hd_tf (fun _ _ lay hi => ⟨lay, hi⟩)
        rw [ha, hm]; refine ⟨.step _ _ ?_, rfl, rfl⟩
        exact .mk topFrame' (by simp [topFrame']) hcal_root hcal_nonroot (by simpa [FrameStackRel, annealFrameStackTopDown, activeMirBody, advanceStmt] using hlinks'.toForall2) (by simpa [activeMirBody, advanceStmt] using hlinks')
          hdisj' htb hvalid hcid_pos hcid_act hcid_bor hbt hbfv
/-- **`C4` Theorem (`step_coverage_multiFrame_simulation`)**: `1:1` lockstep
PC-advance simulation across arbitrary stack depth. -/
theorem step_coverage_multiFrame_simulation {PlaceTy : Type} (hooks : Miri.Interpreter.StepHooks AnnealProv Miri.Interpreter.LocalLayout Unit AnnealMachine Unit PlaceTy)
    {rootBody : CapturedMir} {s : MachineState} {m : AnnealStepState} (hstate : MultiFrameStateRel rootBody s m) (hphase : ∀ p, (activeMirBody rootBody s).phase ≠ .other p) {bb : BasicBlockData} {stmt : Statement}
    (hbb : get? (activeMirBody rootBody s).basicBlocks s.frame.blockIdx = some bb) (hstmt : get? bb.statements s.frame.stmtIdx = some stmt) (hkind : stmt.kind = .coverage) :
    StepRelMultiFrame rootBody m (stepMirFn rootBody s) (Miri.Interpreter.Step.step hooks () m) ∧ stepMirFn rootBody s = MirStepNode.step (advanceStmt s s.frame.locals) ∧ (Miri.Interpreter.Step.step hooks () m).1.machine = m.machine :=
  step_traceOnly_stmt_multiFrame_simulation hooks hstate hphase hbb hstmt (Or.inl hkind)
/-- **`C5` Theorem**: `1:1` lockstep PC-advance simulation for
`StatementKind.backwardIncompatibleDropHint` without dereferencing `place`. -/
theorem step_backwardIncompatibleDropHint_multiFrame_simulation {PlaceTy : Type} (hooks : Miri.Interpreter.StepHooks AnnealProv Miri.Interpreter.LocalLayout Unit AnnealMachine Unit PlaceTy)
    {rootBody : CapturedMir} {s : MachineState} {m : AnnealStepState} (hstate : MultiFrameStateRel rootBody s m) (hphase : ∀ p, (activeMirBody rootBody s).phase ≠ .other p) {bb : BasicBlockData} {stmt : Statement} (place : Place)
    (hbb : get? (activeMirBody rootBody s).basicBlocks s.frame.blockIdx = some bb) (hstmt : get? bb.statements s.frame.stmtIdx = some stmt) (hkind : stmt.kind = .backwardIncompatibleDropHint place) :
    StepRelMultiFrame rootBody m (stepMirFn rootBody s) (Miri.Interpreter.Step.step hooks () m) ∧ stepMirFn rootBody s = MirStepNode.step (advanceStmt s s.frame.locals) ∧ (Miri.Interpreter.Step.step hooks () m).1.machine = m.machine :=
  step_traceOnly_stmt_multiFrame_simulation hooks hstate hphase hbb hstmt (Or.inr ⟨place, hkind⟩)
private theorem step_traceOnly_stmt_simulation {PlaceTy : Type} (hooks : Miri.Interpreter.StepHooks AnnealProv Miri.Interpreter.LocalLayout Unit AnnealMachine Unit PlaceTy)
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState} (hstate : StateRel body s m) (hphase : ∀ p, body.phase ≠ .other p) {bb : BasicBlockData} {stmt : Statement} (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some stmt) (htrace : IsTraceOnlyStmt stmt) :
    StepRel body m (stepMirFn body s) (Miri.Interpreter.Step.step hooks () m) := by
  rcases hstate with ⟨tf, hf, hrc, hrp, hfr, hcal, hst, hbor, hprot, hcaller, hdisj⟩
  have hm := miri_step_traceOnly_multiFrame hooks (restMfs := []) hf hfr.body_eq hfr.location_eq hbb hstmt htrace
  have ha : stepMirFn body s = MirStepNode.step (advanceStmt s s.frame.locals) := by
    have hact : activeMirBody body s = body := by simp [activeMirBody, hcal]
    rw [stepMirFn_activeMirBody_eq body s (by rw [hact]; exact hphase)]; simp only [hact, hbb, hstmt]; exact evalStmt_traceOnly htrace _ _
  rw [ha, hm]
  exact .step _ _ (StateRel.mk { tf with location := .mir ⟨s.frame.blockIdx, s.frame.stmtIdx + 1⟩ }
    rfl hrc hrp ⟨hfr.body_eq, rfl, hfr.af_locals_len, hfr.mf_locals_size, hfr.locals_rel⟩
    hcal hst hbor hprot hcaller hdisj)
/-- Root-frame `StateRel` / `StepRel` corollary for `StatementKind.coverage`. -/
theorem step_coverage_simulation {PlaceTy : Type} (hooks : Miri.Interpreter.StepHooks AnnealProv Miri.Interpreter.LocalLayout Unit AnnealMachine Unit PlaceTy)
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState} (hstate : StateRel body s m) (hphase : ∀ p, body.phase ≠ .other p) {bb : BasicBlockData} {stmt : Statement} (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some stmt) (hkind : stmt.kind = .coverage) :
    StepRel body m (stepMirFn body s) (Miri.Interpreter.Step.step hooks () m) :=
  step_traceOnly_stmt_simulation hooks hstate hphase hbb hstmt (Or.inl hkind)
/-- Root-frame `StateRel` / `StepRel` corollary for
`StatementKind.backwardIncompatibleDropHint`. -/
theorem step_backwardIncompatibleDropHint_simulation {PlaceTy : Type} (hooks : Miri.Interpreter.StepHooks AnnealProv Miri.Interpreter.LocalLayout Unit AnnealMachine Unit PlaceTy)
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState} (hstate : StateRel body s m) (hphase : ∀ p, body.phase ≠ .other p) {bb : BasicBlockData} {stmt : Statement} (place : Place)
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb) (hstmt : get? bb.statements s.frame.stmtIdx = some stmt) (hkind : stmt.kind = .backwardIncompatibleDropHint place) :
    StepRel body m (stepMirFn body s) (Miri.Interpreter.Step.step hooks () m) :=
  step_traceOnly_stmt_simulation hooks hstate hphase hbb hstmt (Or.inr ⟨place, hkind⟩)
section Ep2SharedWitnessHelpers
private def ep2U8Ty : Ty := { kind := .uint .u8, layoutIdx := 0 }
private def ep2U32Ty : Ty := { kind := .uint .u32, layoutIdx := 0 }
private def ep2I32Ty : Ty := { kind := .int .i32, layoutIdx := 0 }
private def ep2UsizeTy : Ty := { kind := .uint .usize, layoutIdx := 0 }
private def ep2BoolTy : Ty := { kind := .bool, layoutIdx := 0 }
private def ep2UnitTy : Ty := { kind := .tuple .nil, layoutIdx := 0 }
private def ep2Tuple1U8Ty : Ty := { kind := .tuple [.uint .u8], layoutIdx := 0 }
private def ep2RefU32Ty : Ty := { kind := .ref .not (.uint .u32), layoutIdx := 0 }
private def ep2RawU8PtrTy : Ty := { kind := .rawPtr .not (.uint .u8), layoutIdx := 0 }
private def ep2RawMutU8PtrTy : Ty := { kind := .rawPtr .mut (.uint .u8), layoutIdx := 0 }
private def ep2RawUnitPtrTy : Ty := { kind := .rawPtr .not (.tuple .nil), layoutIdx := 0 }
private def mkEp2Decl (ty : Ty) : LocalDecl := { mutability := .mut, ty := ty, debugName := none }
private def mkEp2Stmt (k : StatementKind) : MirAst.Statement := { kind := k, span := "ep2-lm" }
private def mkEp2Term (k : TerminatorKind) : MirAst.Terminator := { kind := k, span := "ep2-lm" }
private def mkEp2Body (name : String) (tys : List Ty) (stmts : List StatementKind) (lays : LayoutTable := emptyLayoutTable) (term : TerminatorKind := .return_) : CapturedMir :=
  { defPath := name, phase := .runtimePostCleanup, role := .subject, argCount := 0, localDecls := tys.map mkEp2Decl, basicBlocks := [{ statements := stmts.map mkEp2Stmt, terminator := mkEp2Term term, isCleanup := false }],
    fnAbi := Witness.fnAbi0, layouts := lays, allocations := [] }
private def mkEp2MiriState (body : CapturedMir) (retTy : Ty) (locs : Array (Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout)) (mach : AnnealMachine := AnnealMachine.empty) : AnnealStepState :=
  { stack := { frames := #[{
      body := translateBody body, bodyIdentity := .ofCanonicalIndex 0, functionInstance := { kind := .Item 0, args := #[] }, extra := (), returnContinuation := .stop false,
      returnPlace := .frameLocal 0 0 none (translateTyOverlay retTy body.layouts) (.ofAllocationToken 0), localsIdentity := .ofAllocationToken 0, locals := locs, vaList := #[], trackCallerArg := none, location := .mir ⟨0, 0⟩ }] },
    machine := mach }
private def miriScalarUInt (bits : Nat) (szBytes : UInt64) : Miri.Memory.Scalar AnnealProv := match Miri.Memory.Scalar.fromUInt (BitVec.ofNat 128 bits) (Miri.ABI.Size.ofBytes szBytes) with
  | .ok s => s
  | .error _ => Miri.Memory.Scalar.fromPointer annealTargetDataLayout ⟨.ZERO, .wildcard⟩
private def mkEp2AddrMachine (aid : Miri.Memory.AllocId) (base : UInt64) : AnnealMachine :=
  { AnnealMachine.empty with
    addresses := { AnnealMachine.empty.addresses with baseAddr := #[⟨aid, base⟩] } }
private def miriLocalVal? (st : AnnealStepState) (idx : Nat) : Option (Miri.Interpreter.LocalValue AnnealProv) := st.stack.frames[0]?.bind (fun f => f.locals[idx]?.map (·.value))
end Ep2SharedWitnessHelpers
section TraceOnlyWitnesses
private def witCoverageBody : CapturedMir := mkEp2Body "wit_c4_coverage" [ep2U32Ty] [.coverage, .assign ⟨0, .nil⟩ (.use (.constant { ty := ep2U32Ty, val := .scalar (.int ⟨42, 4⟩) })), .coverage]
private def witCoverageAnneal0 : MachineState := { frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit] }, memory := emptyMemory }
private def witCoverageMiri0 : AnnealStepState := mkEp2MiriState witCoverageBody ep2U32Ty #[⟨.live (.immediate .uninit), some (translateTy ep2U32Ty)⟩]
private def witCoverageMiri1 : AnnealStepState := (Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosure witCoverageBody) () witCoverageMiri0).1
private def witCoverageMiri2 : AnnealStepState := (Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosure witCoverageBody) () witCoverageMiri1).1
private def witCoverageMiri3 : AnnealStepState := (Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosure witCoverageBody) () witCoverageMiri2).1
private def witCoverageMiri4 : AnnealStepState := (Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosure witCoverageBody) () witCoverageMiri3).1
/-- **Concrete `C4` Witness (`w_c4_coverage_multiStep`)**: 4-step lockstep
execution across `coverage`, assignment, `coverage`, and `return_`. -/
theorem w_c4_coverage_multiStep : ∃ s₁ s₂ s₃, stepMirFn witCoverageBody witCoverageAnneal0 = .step s₁ ∧ s₁.frame.stmtIdx = 1 ∧ stepMirFn witCoverageBody s₁ = .step s₂ ∧ stepMirFn witCoverageBody s₂ = .step s₃ ∧ s₃.frame.stmtIdx = 3 ∧
      stepMirFn witCoverageBody s₃ = .retNormal (.scalar ⟨42, 4⟩) emptyMemory ∧ Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosure witCoverageBody) () witCoverageMiri0 = (witCoverageMiri1, .ok true) ∧
      Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosure witCoverageBody) () witCoverageMiri1 = (witCoverageMiri2, .ok true) ∧ Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosure witCoverageBody)
        () witCoverageMiri2 = (witCoverageMiri3, .ok true) ∧
      Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosure witCoverageBody) () witCoverageMiri3 = (witCoverageMiri4, .ok true) ∧ witCoverageMiri4.stack.frames = #[] :=
  ⟨_, _, _, rfl, rfl, rfl, rfl, rfl, rfl, step_eq_fst_of_snd rfl, step_eq_fst_of_snd rfl, step_eq_fst_of_snd rfl, step_eq_fst_of_snd rfl, rfl⟩
private def mkDropHintOrMentionBody (isHint : Bool) (place : Place) : CapturedMir := mkEp2Body "wit_c5_drophint" [ep2UnitTy, ep2RawU8PtrTy, ep2RawU8PtrTy] [if isHint then .backwardIncompatibleDropHint place else .placeMention place]
private def witDropHintAnneal0 : MachineState := { frame := { blockIdx := 0, stmtIdx := 0, locals := [.init .unit, .dead, .uninit] }, memory := emptyMemory }
private def mkDropHintMiri0 (b : CapturedMir) : AnnealStepState := mkEp2MiriState b ep2UnitTy #[⟨.live (.immediate .uninit), some (translateTy ep2UnitTy)⟩, ⟨.dead, some (translateTy ep2RawU8PtrTy)⟩,
      ⟨.live (.immediate .uninit), some (translateTy ep2RawU8PtrTy)⟩]
/-- **Concrete `C5` Witness**. -/
theorem w_c5_dropHint_dead_uninit_dangling_vs_placeMention_ub :
    let pDeadDeref : Place := ⟨1, [.deref]⟩; let pUninitDeref : Place := ⟨2, [.deref]⟩; let pOob : Place := ⟨99, .nil⟩; let bHintDead := mkDropHintOrMentionBody true pDeadDeref; let bMentDead := mkDropHintOrMentionBody false pDeadDeref
    let bHintUninit := mkDropHintOrMentionBody true pUninitDeref; let bMentUninit := mkDropHintOrMentionBody false pUninitDeref; let bHintOob := mkDropHintOrMentionBody true pOob
    (∃ s', stepMirFn bHintDead witDropHintAnneal0 = .step s' ∧ s'.frame.stmtIdx = 1) ∧ (Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosure bHintDead) () (mkDropHintMiri0 bHintDead)).2 = .ok true ∧
    stepMirFn bMentDead witDropHintAnneal0 = .fail .ub ∧ (∃ msg, (Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosure bMentDead) () (mkDropHintMiri0 bMentDead)).2 = .error (.undefinedBehavior msg)) ∧
    (∃ s', stepMirFn bHintUninit witDropHintAnneal0 = .step s' ∧ s'.frame.stmtIdx = 1) ∧ (Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosure bHintUninit) () (mkDropHintMiri0 bHintUninit)).2 = .ok true ∧
    stepMirFn bMentUninit witDropHintAnneal0 = .fail .ub ∧ (∃ msg, (Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosure bMentUninit) () (mkDropHintMiri0 bMentUninit)).2 = .error (.undefinedBehavior msg)) ∧
    (∃ s', stepMirFn bHintOob witDropHintAnneal0 = .step s' ∧ s'.frame.stmtIdx = 1) ∧ (Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosure bHintOob) () (mkDropHintMiri0 bHintOob)).2 = .ok true := by
  refine ⟨⟨_, rfl, rfl⟩, rfl, rfl, ⟨_, rfl⟩, ⟨_, rfl, rfl⟩, rfl, rfl, ?_, ⟨_, rfl, rfl⟩, rfl⟩
  with_unfolding_all exact ⟨_, rfl⟩
end TraceOnlyWitnesses
/-! ## Shared Overlay Place / Operand / Immediate-Write Reduction Lemmas -/
private theorem validScalarBytes_size_inj {a b : Nat} (ha : ValidScalarBytes a) (hb : ValidScalarBytes b) (h : translateSizeBytes a = translateSizeBytes b) : a = b := by
  rcases ha with rfl | rfl | rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl | rfl | rfl <;> first | rfl | cases h
theorem cacheFrameLocalLayout_getElem?_preserve (tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit) {localDecls : List LocalDecl} {dstIdx srcIdx : Nat} {dstDecl srcDecl : LocalDecl} {layouts : LayoutTable}
    {v : Miri.Interpreter.LocalValue AnnealProv} {cSrc : Option Miri.Interpreter.LocalLayout} (hdst_decl : get? localDecls dstIdx = some dstDecl) (hsrc_decl : get? localDecls srcIdx = some srcDecl)
    (hlt_d : dstIdx < tf.locals.size) (hmls_s : tf.locals[srcIdx]? = some ⟨v, cSrc⟩) (hc_s : ∀ l, cSrc = some l → l = translateTy srcDecl.ty layouts) :
    ∃ cSrc', (cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty layouts)).locals[srcIdx]? = some ⟨v, cSrc'⟩ ∧ (∀ l, cSrc' = some l → l = translateTy srcDecl.ty layouts) := by
  dsimp [cacheFrameLocalLayout]
  by_cases hsd : dstIdx = srcIdx
  · subst hsd
    have hd_eq : dstDecl = srcDecl := Option.some.inj (hdst_decl.symm.trans hsrc_decl); subst hd_eq; rw [Array.getElem?_eq_getElem hlt_d] at hmls_s; injection hmls_s with h_eq
    exact ⟨some (translateTy dstDecl.ty layouts), by simp [h_eq], fun _ h => Option.some.inj h.symm⟩
  · exact ⟨cSrc, by simp [hsd, hmls_s], hc_s⟩
theorem annealEvalPlaceOverlay_unprojected_nonWide (localDecls : List LocalDecl) (layouts : LayoutTable) (idx : Miri.MIR.LocalId) (skipValidity : Bool) (hno_wide : isWideOverlayPlace localDecls ⟨idx, #[]⟩ = false) :
    annealEvalPlaceOverlay localDecls layouts ⟨idx, #[]⟩ skipValidity = annealEvalPlace localDecls layouts ⟨idx, #[]⟩ := by
  funext st; unfold annealEvalPlaceOverlay
  have huw : hasRealUnwrapUnsafeBinder ⟨idx, #[]⟩ = false := rfl; simp [huw, hno_wide]
theorem annealEvalOperandOverlay_copy_nonWide (localDecls : List LocalDecl) (layouts : LayoutTable) (idx : Miri.MIR.LocalId) (known : Option Miri.Interpreter.LocalLayout) (hno_wide : isWideOverlayPlace localDecls ⟨idx, #[]⟩ = false) :
    annealEvalOperandOverlay localDecls layouts (.Copy ⟨idx, #[]⟩) known = annealEvalOperand localDecls layouts (.Copy ⟨idx, #[]⟩) known := by
  funext st; unfold annealEvalOperandOverlay
  have huw : hasRealUnwrapUnsafeBinder ⟨idx, #[]⟩ = false := rfl; simp [huw, hno_wide]
theorem annealEvalOperandOverlay_move_nonWide (localDecls : List LocalDecl) (layouts : LayoutTable) (idx : Miri.MIR.LocalId) (known : Option Miri.Interpreter.LocalLayout) (hno_wide : isWideOverlayPlace localDecls ⟨idx, #[]⟩ = false) :
    annealEvalOperandOverlay localDecls layouts (.Move ⟨idx, #[]⟩) known = annealEvalOperand localDecls layouts (.Move ⟨idx, #[]⟩) known := by
  funext st; unfold annealEvalOperandOverlay
  have huw : hasRealUnwrapUnsafeBinder ⟨idx, #[]⟩ = false := rfl; simp [huw, hno_wide]
theorem annealEvalPlace_unprojected_multiFrame {body : CapturedMir} {m : AnnealStepState} {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {restMfs : List (Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)} {dstIdx : Nat} {dstDecl : LocalDecl} (hframes : m.stack.frames = ⟨restMfs.reverse ++ [topFrame]⟩)
    (hlt_d : dstIdx < topFrame.locals.size) (hdst_decl : get? body.localDecls dstIdx = some dstDecl) (hc_d : ∀ l, (topFrame.locals[dstIdx]'hlt_d).layout = some l → l = translateTy dstDecl.ty body.layouts) :
    annealEvalPlace body.localDecls body.layouts ⟨dstIdx, #[]⟩ m = .ok ⟨.local restMfs.length dstIdx none topFrame.localsIdentity, translateTy dstDecl.ty body.layouts⟩
        { m with stack := ⟨⟨restMfs.reverse ++ [cacheFrameLocalLayout topFrame dstIdx hlt_d (translateTy dstDecl.ty body.layouts)]⟩⟩ } := by
  have hres := annealResolveAndCacheLocalLayout_multiFrame_eq (body := body) (known := none) hframes hlt_d hdst_decl hc_d
  with_unfolding_all
    unfold annealEvalPlace
    simp only [Array.isEmpty_empty, Bool.not_true, Bool.false_eq_true, ↓reduceIte, get, getThe, MonadStateOf.get, EStateM.get, Bind.bind, EStateM.bind,
      Pure.pure, EStateM.pure, stack_currentFrame?_append_singleton m.stack restMfs topFrame hframes, Option.isNone_some, hframes, array_size_append_singleton, List.length_reverse, Nat.add_sub_cancel, hres]
    rfl
theorem isWideOverlayPlace_eq_false_of_decl {localDecls : List LocalDecl} {idx : Nat} {decl : LocalDecl} (hdecl : get? localDecls idx = some decl) (h1 : isWideSliceOrPointeeTy decl.ty = false) (h2 : isWideDynRawPtrTy decl.ty = false) :
    isWideOverlayPlace localDecls ⟨idx, #[]⟩ = false := by
  unfold isWideOverlayPlace; simp [hdecl, h1, h2]
theorem memoryAllocDisjoint_cacheFrameLocalLayout {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit} {idx : Nat} (hlt : idx < tf.locals.size) {lay : Miri.Interpreter.LocalLayout}
    (hdisj : MemoryAllocDisjoint tf) :
    MemoryAllocDisjoint (cacheFrameLocalLayout tf idx hlt lay) := by
  apply MemoryAllocDisjoint.mono_layout hdisj
  intro k
  by_cases hk : k = idx
  · subst hk; refine ⟨some lay, ?_⟩; dsimp [cacheFrameLocalLayout]; simp [Array.getElem?_eq_getElem hlt]
  · refine ⟨(tf.locals[k]?).bind (·.layout), ?_⟩; dsimp [cacheFrameLocalLayout]; simp only [Array.getElem?_set, Ne.symm hk, ↓reduceIte]; cases tf.locals[k]? with | none => rfl | some x => cases x; rfl
theorem annealEvalPlace_unprojected_root {body : CapturedMir} {m : AnnealStepState} {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {dstIdx : Nat} {dstDecl : LocalDecl} (hframes : m.stack.frames = #[topFrame]) (hlt_d : dstIdx < topFrame.locals.size) (hdst_decl : get? body.localDecls dstIdx = some dstDecl)
    (hc_d : ∀ l, (topFrame.locals[dstIdx]'hlt_d).layout = some l → l = translateTy dstDecl.ty body.layouts) :
    annealEvalPlace body.localDecls body.layouts ⟨dstIdx, #[]⟩ m = .ok ⟨.local 0 dstIdx none topFrame.localsIdentity, translateTy dstDecl.ty body.layouts⟩
        { m with stack := ⟨#[cacheFrameLocalLayout topFrame dstIdx hlt_d (translateTy dstDecl.ty body.layouts)]⟩ } := by
  simpa using annealEvalPlace_unprojected_multiFrame (body := body) (restMfs := []) hframes hlt_d hdst_decl hc_d
private def ep2CacheDstSrc (tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit) {dstIdx srcIdx : Nat} (hlt_d : dstIdx < tf.locals.size) (hlt_s : srcIdx < tf.locals.size)
    (dstLay srcLay : Miri.Interpreter.LocalLayout) :
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  cacheFrameLocalLayout (cacheFrameLocalLayout tf dstIdx hlt_d dstLay) srcIdx (by rw [cacheFrameLocalLayout_size]; exact hlt_s) srcLay
private theorem ep2CacheDstSrc_location (tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit) {dstIdx srcIdx : Nat} (hlt_d : dstIdx < tf.locals.size) (hlt_s : srcIdx < tf.locals.size)
    (dstLay srcLay : Miri.Interpreter.LocalLayout) : (ep2CacheDstSrc tf hlt_d hlt_s dstLay srcLay).location = tf.location := rfl
private theorem ep2CacheDstSrc_dst_getElem? (tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit) {dstIdx srcIdx : Nat} {dstLay srcLay : Miri.Interpreter.LocalLayout}
    {vD : Miri.Interpreter.LocalValue AnnealProv} {cDst : Option Miri.Interpreter.LocalLayout} (hlt_d : dstIdx < tf.locals.size) (hlt_s : srcIdx < tf.locals.size)
    (hne : dstIdx ≠ srcIdx) (hmls_d : tf.locals[dstIdx]'hlt_d = ⟨vD, cDst⟩) :
    dstIdx < (ep2CacheDstSrc tf hlt_d hlt_s dstLay srcLay).locals.size ∧ (ep2CacheDstSrc tf hlt_d hlt_s dstLay srcLay).locals[dstIdx]? = some ⟨vD, some dstLay⟩ := by
  unfold ep2CacheDstSrc; refine ⟨by simp [cacheFrameLocalLayout, hlt_d], ?_⟩; dsimp only [cacheFrameLocalLayout]; rw [Array.getElem?_set_ne (by simp [hlt_s]) (Ne.symm hne), Array.getElem?_set_self hlt_d]; simp [hmls_d]
theorem evalStatement_overlay_assign_cast_copy {body : CapturedMir} {callees : List CapturedMir} {poppedFrame : Miri.TreeBorrows.FrameState} {fnPtrs : List FnPtrEntry} {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit} {stmt : Statement} {ck : CastKind} {srcIdx dstIdx : Local} {srcDecl dstDecl : LocalDecl} (hframes : m.stack.frames = #[topFrame])
    (hkind : stmt.kind = .assign ⟨dstIdx, .nil⟩ (.cast ck (.copy ⟨srcIdx, .nil⟩) dstDecl.ty)) (hov_ck : isOverlayCastKind (translateCastKind ck) = true) (hsrc_decl : get? body.localDecls srcIdx = some srcDecl)
    (hdst_decl : get? body.localDecls dstIdx = some dstDecl) (hno_wide_s : isWideOverlayPlace body.localDecls ⟨srcIdx, #[]⟩ = false) (hno_wide_d : isWideOverlayPlace body.localDecls ⟨dstIdx, #[]⟩ = false)
    (hlt_s : srcIdx < topFrame.locals.size) (hlt_d : dstIdx < topFrame.locals.size) (hc_d : ∀ l, (topFrame.locals[dstIdx]'hlt_d).layout = some l → l = translateTy dstDecl.ty body.layouts) :
    let tf_sd := ep2CacheDstSrc topFrame hlt_d hlt_s (translateTy dstDecl.ty body.layouts) (translateTy srcDecl.ty body.layouts)
    (∀ cSrc, topFrame.locals[srcIdx]? = some ⟨.dead, cSrc⟩ → (∀ l, cSrc = some l → l = translateTy srcDecl.ty body.layouts) → Miri.Interpreter.Step.evalStatement (annealStepHooksUnwindFnPtrClosure body callees poppedFrame fnPtrs) ()
        (translateStmt stmt) m =
      ({ stack := ⟨#[tf_sd]⟩, machine := m.machine }, .error (.undefinedBehavior "read of dead local"))) ∧
    (∀ immSrc cSrc, topFrame.locals[srcIdx]? = some ⟨.live (.immediate immSrc), cSrc⟩ → (∀ l, cSrc = some l → l = translateTy srcDecl.ty body.layouts) → Miri.Interpreter.Step.evalStatement
        (annealStepHooksUnwindFnPtrClosure body callees poppedFrame fnPtrs) () (translateStmt stmt) m =
      Miri.Interpreter.runRvalue ((annealRvalueHooksUnwindFnPtrClosure body fnPtrs).cast () ⟨.immediate immSrc, translateTy srcDecl.ty body.layouts⟩ (translateCastKind ck) (encodeTyId dstDecl.ty)
          ⟨.local 0 dstIdx none topFrame.localsIdentity, translateTy dstDecl.ty body.layouts⟩)
        { stack := ⟨#[tf_sd]⟩, machine := m.machine }) := by
  intro tf_sd; let tf_d := cacheFrameLocalLayout topFrame dstIdx hlt_d (translateTy dstDecl.ty body.layouts); have hlt_s' : srcIdx < tf_d.locals.size := by rw [cacheFrameLocalLayout_size]; exact hlt_s
  have heval_dst := annealEvalPlace_unprojected_root hframes hlt_d hdst_decl hc_d
  have hover_true : isUnwindFnPtrClosureAssign body.localDecls ⟨dstIdx, #[]⟩ (.Cast (translateCastKind ck) (.Copy ⟨srcIdx, #[]⟩) (encodeTyId dstDecl.ty)) = true := by unfold isUnwindFnPtrClosureAssign; simp [hov_ck]
  cases m with | mk st mach =>
  dsimp only at hframes heval_dst ⊢; refine ⟨?_, ?_⟩
  · intro cSrc hmls_s hc_s
    obtain ⟨cSrc', hmls_sd, hc_sd⟩ := cacheFrameLocalLayout_getElem?_preserve topFrame hdst_decl hsrc_decl hlt_d hmls_s hc_s
    have hop_dead := annealEvalOperand_copy_dead (m := { stack := ⟨#[tf_d]⟩, machine := mach }) (known := none)
      rfl hlt_s' hsrc_decl (Option.some.inj ((Array.getElem?_eq_getElem hlt_s').symm.trans hmls_sd)) hc_sd
    dsimp only at hop_dead; unfold annealStepHooksUnwindFnPtrClosure Miri.Interpreter.Step.evalStatement translateStmt; rw [hkind]
    dsimp only [translateStmtKind, translateRvalue, translateOperand, translatePlace, List.map, List.toArray, Miri.Interpreter.evalRvalueIntoPlace, annealRvalueHooksUnwindFnPtrClosure]
    simp only [hover_true, ↓reduceIte]; unfold Miri.Interpreter.runRvalue
    rw [annealEvalPlaceOverlay_unprojected_nonWide _ _ _ true hno_wide_d, EStateM.bind_eq_ok heval_dst, annealEvalOperandOverlay_copy_nonWide _ _ _ none hno_wide_s, EStateM.bind_eq_error hop_dead]; rfl
  · intro immSrc cSrc hmls_s hc_s
    obtain ⟨cSrc', hmls_si, hc_si⟩ := cacheFrameLocalLayout_getElem?_preserve topFrame hdst_decl hsrc_decl hlt_d hmls_s hc_s
    have hop_live := annealEvalOperand_copy_live (m := { stack := ⟨#[tf_d]⟩, machine := mach }) (known := none)
      rfl hlt_s' hsrc_decl (Option.some.inj ((Array.getElem?_eq_getElem hlt_s').symm.trans hmls_si)) hc_si
    dsimp only at hop_live; unfold annealStepHooksUnwindFnPtrClosure Miri.Interpreter.Step.evalStatement translateStmt; rw [hkind]
    dsimp only [translateStmtKind, translateRvalue, translateOperand, translatePlace, List.map, List.toArray, Miri.Interpreter.evalRvalueIntoPlace]; simp only [hover_true, ↓reduceIte]; unfold Miri.Interpreter.runRvalue
    rw [show (annealRvalueHooksUnwindFnPtrClosure body fnPtrs).evalPlace () ⟨dstIdx, #[]⟩ true = annealEvalPlace body.localDecls body.layouts ⟨dstIdx, #[]⟩ from annealEvalPlaceOverlay_unprojected_nonWide _ _ _ true hno_wide_d,
        EStateM.bind_eq_ok heval_dst, show (annealRvalueHooksUnwindFnPtrClosure body fnPtrs).evalOperandAt () (Miri.Interpreter.OperandPath.rvalue "operand") (.Copy ⟨srcIdx, #[]⟩) none =
          annealEvalOperand body.localDecls body.layouts (.Copy ⟨srcIdx, #[]⟩) none from
        annealEvalOperandOverlay_copy_nonWide _ _ _ none hno_wide_s, EStateM.bind_eq_ok hop_live]
    rfl
theorem stepRel_of_writeImmediateLM2_2 {PlaceTy : Type} (hooks : Miri.Interpreter.StepHooks AnnealProv Miri.Interpreter.LocalLayout Unit AnnealMachine Unit PlaceTy) {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {tf₀ topFrame₁ : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit} {locals₁ : List LocalSlot} {dstIdx : Local} {dstDecl : LocalDecl} {val : Value} {imm : Miri.Interpreter.Immediate AnnealProv}
    {id0 : Miri.Interpreter.LocalsIdentity} {bb : BasicBlockData} {stmt : Statement} (hphase : ∀ p, body.phase ≠ .other p) (hretCont : topFrame₁.returnContinuation = .stop false)
    (hretPlace : ∃ retLay, topFrame₁.returnPlace = .frameLocal 0 0 none retLay topFrame₁.localsIdentity) (hcal : s.memory.activeCallee = none) (hstack : s.memory.callStack = .nil)
    (hbor : s.memory.borrows = .nil) (hprot : s.memory.activeProtectors = .nil) (hcaller : s.memory.callerLocals = .nil) (hframes : m.stack.frames = #[tf₀])
    (hbody₀ : tf₀.body = translateBody body) (hloc₀ : tf₀.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩) (hbb : get? body.basicBlocks s.frame.blockIdx = some bb) (hstmt : get? bb.statements s.frame.stmtIdx = some stmt)
    (hframe₁ : FrameRel body m.machine { s.frame with locals := locals₁ } topFrame₁) (hdisj : MemoryAllocDisjoint topFrame₁) (hdecl : get? body.localDecls dstIdx = some dstDecl)
    (himm_dst : IsImmediateFrameLocal topFrame₁ dstIdx) (himmRel : ImmediateRel dstDecl.ty body.layouts val imm) (heval_a : evalStmt s stmt body.localDecls body.layouts =
      match get? locals₁ dstIdx with
      | .some .dead => MirStepNode.fail .ub
      | .some _ =>
        match set? locals₁ dstIdx (.init val) with
        | .some locals₂ => MirStepNode.step (advanceStmt s locals₂ s.memory)
        | .none => MirStepNode.fail .ub
      | .none => MirStepNode.fail .ub)
    (heval_m : Miri.Interpreter.Step.evalStatement hooks () (translateStmt stmt) m = Miri.Interpreter.runRvalue (annealWriteImmediateLM2_2 imm ⟨.local 0 dstIdx none id0, translateTy dstDecl.ty body.layouts⟩)
        { m with stack := ⟨#[topFrame₁]⟩ }) :
    StepRel body m (stepMirFn body s) (Miri.Interpreter.Step.step hooks () m) := by
  have hact : activeMirBody body s = body := by simp [activeMirBody, hcal]
  rw [stepMirFn_activeMirBody_eq body s (by rw [hact]; exact hphase)]; simp only [hact, hbb, hstmt]
  obtain ⟨slot_d, mls_d, hlt_af, hlt_mf, hslot_d, hmls_d, hmls_eq, hloc_d⟩ := hframe₁.lookup_local hdecl; have hget_d := frame_getLocal_of_getElem? topFrame₁ dstIdx mls_d hmls_d; have himm_d := himm_dst mls_d hmls_d
  dsimp only at hslot_d hlt_af; rw [heval_a, hslot_d]
  cases hloc_d with
  | dead _ _ =>
    have hm_err : Miri.Interpreter.Step.evalStatement hooks () (translateStmt stmt) m = ({ m with stack := ⟨#[topFrame₁]⟩ }, .error (.undefinedBehavior "write to dead local")) := by
      rw [heval_m]; unfold Miri.Interpreter.runRvalue; rw [annealWriteImmediateLM2_2_dead (topFrame := topFrame₁) rfl hget_d]
    rw [miri_step_at_statement_error _ hframes hbody₀ hloc₀ hbb hstmt hm_err]; exact .ub _ _
  | indirect _ mp _ _ _ _ => exact False.elim (himm_d mp rfl)
  | immediate _ _ cachedLayout hc hval =>
    have hnot_dead : (match some slot_d with
         | .some .dead => MirStepNode.fail .ub
         | .some _ =>
           match set? locals₁ dstIdx (.init val) with
           | .some locals₂ => MirStepNode.step (advanceStmt s locals₂ s.memory)
           | .none => MirStepNode.fail .ub
         | .none => MirStepNode.fail .ub) =
        MirStepNode.step (advanceStmt s (locals₁.set dstIdx (.init val)) s.memory) := by
      rcases hval with ⟨rfl, _⟩ | ⟨_, rfl, _⟩ <;> simp [set?_eq_some_set hlt_af]
    rw [hnot_dead]
    let topFrame₂ :=
      { topFrame₁ with
        locals := topFrame₁.locals.set dstIdx { topFrame₁.locals[dstIdx]'hlt_mf with value := .live (.immediate imm) } hlt_mf }
    have hm_ok : Miri.Interpreter.Step.evalStatement hooks () (translateStmt stmt) m = ({ m with stack := ⟨#[topFrame₂]⟩ }, .ok ()) := by
      rw [heval_m]; unfold Miri.Interpreter.runRvalue; rw [annealWriteImmediateLM2_2_live (topFrame := topFrame₁) rfl hlt_mf hget_d]
    rw [miri_step_at_statement_ok _ hframes hbody₀ hloc₀ hbb hstmt hm_ok rfl hframe₁.location_eq]; apply StepRel.step
    have hloc_new : LocalRel m.machine dstDecl body.layouts (.init val) { topFrame₁.locals[dstIdx]'hlt_mf with value := .live (.immediate imm) } := by
      rw [hmls_eq]; exact .immediate (.init val) imm cachedLayout hc (Or.inr ⟨val, rfl, himmRel⟩)
    have hfr₂ := hframe₁.update_local hdecl (.init val) (.live (.immediate imm)) hloc_new; obtain ⟨retLay, hretP⟩ := hretPlace
    exact StateRel.mk { topFrame₂ with location := .mir ⟨s.frame.blockIdx, s.frame.stmtIdx + 1⟩ }
      rfl hretCont ⟨retLay, hretP⟩ ⟨hfr₂.body_eq, rfl, hfr₂.af_locals_len, hfr₂.mf_locals_size, hfr₂.locals_rel⟩
      hcal hstack hbor hprot hcaller (by
        apply MemoryAllocDisjoint.mono_immediate hdisj
        intro k
        by_cases hk : k = dstIdx
        · subst hk; right; refine ⟨imm, (topFrame₁.locals[k]'hlt_mf).layout, ?_⟩; dsimp [topFrame₂]; simp
        · left; dsimp [topFrame₂]; simp [Ne.symm hk])
private theorem evalOperand_copy_nil (locals : List LocalSlot) (idx : Local) (borrows : List BorrowEntry) (globals : List CapturedAllocation) (layouts : LayoutTable) (callerLocals : List LocalSlot)
    (localDecls : List LocalDecl) (callStack : List SavedCallerFrame) :
    evalOperand locals (.copy ⟨idx, .nil⟩) borrows globals layouts callerLocals localDecls callStack =
      match get? locals idx with
      | some (.init v) => .ok v locals
      | _ => .ub := by
  unfold evalOperand; dsimp only
  cases get? locals idx with
  | none => rfl
  | some sl =>
    cases sl with
    | dead | uninit => rfl
    | init v => cases v <;> rfl
private theorem memory_inv_of_borrows_nil {mem : Memory} (dstIdx : Local) (hb : mem.borrows = .nil) (hp : mem.activeProtectors = .nil) :
    ({ nextAllocId := mem.nextAllocId, globals := mem.globals,
       borrows := invalidateConflictingBorrows mem.borrows dstIdx none (length mem.callStack), nextTag := mem.nextTag, callees := mem.callees, traitImpls := mem.traitImpls, callStack := mem.callStack, activeCallee := mem.activeCallee,
       activeProtectors := .nil, nextProtector := mem.nextProtector, callerLocals := mem.callerLocals, fnPtrs := mem.fnPtrs, exposedAllocIds := mem.exposedAllocIds } : Memory) = mem := by
  cases mem; dsimp at hb hp; subst hb hp; rfl
private theorem trusted_step_assign_rvalue_ok {body : CapturedMir} {s : MachineState} {bb : BasicBlockData} {stmt : Statement} {dstIdx : Local} {rv : Rvalue} {val : Value} {mem' : Memory} {slot_d : LocalSlot}
    (hphase : ∀ p, body.phase ≠ .other p) (hcal : s.memory.activeCallee = none) (hbb : get? body.basicBlocks s.frame.blockIdx = some bb) (hstmt : get? bb.statements s.frame.stmtIdx = some stmt)
    (hkind : stmt.kind = .assign ⟨dstIdx, .nil⟩ rv) (hrv : evalRvalue s.frame.locals rv s.memory body.localDecls body.layouts = .ok val s.frame.locals mem')
    (hlt_d : dstIdx < s.frame.locals.length) (hslot_d : get? s.frame.locals dstIdx = some slot_d) (hnot_dead : slot_d ≠ .dead) (hbor' : mem'.borrows = .nil) (hprot' : mem'.activeProtectors = .nil) :
    let s' := advanceStmt s (s.frame.locals.set dstIdx (.init val)) mem'
    stepMirFn body s = .step s' ∧ s'.frame.blockIdx = s.frame.blockIdx ∧ s'.frame.stmtIdx = s.frame.stmtIdx + 1 ∧ get? s'.frame.locals dstIdx = some (.init val) := by
  have hact : activeMirBody body s = body := by simp [activeMirBody, hcal]
  have ha : stepMirFn body s = MirStepNode.step (advanceStmt s (s.frame.locals.set dstIdx (.init val)) mem') := by
    rw [stepMirFn_activeMirBody_eq body s (by rw [hact]; exact hphase)]; simp only [hact, hbb, hstmt]; unfold evalStmt; rw [hkind]; dsimp only; rw [hrv]; dsimp only; rw [hslot_d]
    cases hs_d : slot_d with
    | dead => exact False.elim (hnot_dead hs_d)
    | uninit | init _ =>
        rw [set?_eq_some_set hlt_d]; dsimp only; rw [hprot']; dsimp only; rw [memory_inv_of_borrows_nil dstIdx hbor' hprot']
  refine ⟨ha, rfl, rfl, ?_⟩
  dsimp [advanceStmt]; rw [get?_eq_getElem?, List.getElem?_set_self hlt_d]
private theorem trusted_step_assign_rvalue_ub {body : CapturedMir} {s : MachineState} {bb : BasicBlockData} {stmt : Statement} {dstIdx : Local} {rv : Rvalue} (hphase : ∀ p, body.phase ≠ .other p) (hcal : s.memory.activeCallee = none)
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb) (hstmt : get? bb.statements s.frame.stmtIdx = some stmt) (hkind : stmt.kind = .assign ⟨dstIdx, .nil⟩ rv)
    (hrv : evalRvalue s.frame.locals rv s.memory body.localDecls body.layouts = .ub) :
    stepMirFn body s = .fail .ub := by
  have hact : activeMirBody body s = body := by simp [activeMirBody, hcal]
  rw [stepMirFn_activeMirBody_eq body s (by rw [hact]; exact hphase)]; simp only [hact, hbb, hstmt]; unfold evalStmt; rw [hkind]; dsimp only; rw [hrv]
private theorem miri_step_write_immediate_root {PlaceTy : Type} (hooks : Miri.Interpreter.StepHooks AnnealProv Miri.Interpreter.LocalLayout Unit AnnealMachine Unit PlaceTy)
    {body : CapturedMir} {m : AnnealStepState} {mach' : AnnealMachine} {topFrame tf_sd : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit} {bb : BasicBlockData} {stmt : Statement} {blockIdx stmtIdx dstIdx : Nat}
    {immDst imm : Miri.Interpreter.Immediate AnnealProv} {dstLay writeLay : Miri.Interpreter.LocalLayout} {id0 : Miri.Interpreter.LocalsIdentity} (hframes : m.stack.frames = #[topFrame]) (hbody : topFrame.body = translateBody body)
    (hloc : topFrame.location = .mir ⟨blockIdx, stmtIdx⟩) (hloc_sd : tf_sd.location = .mir ⟨blockIdx, stmtIdx⟩) (hbb : get? body.basicBlocks blockIdx = some bb) (hstmt : get? bb.statements stmtIdx = some stmt)
    (hlt_d : dstIdx < tf_sd.locals.size) (htf_d : tf_sd.locals[dstIdx]? = some ⟨.live (.immediate immDst), some dstLay⟩) (heval : Miri.Interpreter.Step.evalStatement hooks () (translateStmt stmt) m = Miri.Interpreter.runRvalue
        (annealWriteImmediateLM2_2 imm ⟨.local 0 dstIdx none id0, writeLay⟩)
        { stack := ⟨#[tf_sd]⟩, machine := mach' }) :
    ∃ tf', Miri.Interpreter.Step.step hooks () m = ({ stack := ⟨#[tf']⟩, machine := mach' }, .ok true) ∧ tf'.location = .mir ⟨blockIdx, stmtIdx + 1⟩ ∧ tf'.locals[dstIdx]? = some ⟨.live (.immediate imm), some dstLay⟩ := by
  have hget_d := frame_getLocal_of_getElem? tf_sd dstIdx _ htf_d
  have hlay_d : (tf_sd.locals[dstIdx]'hlt_d).layout = some dstLay := by have h := htf_d; rw [Array.getElem?_eq_getElem hlt_d] at h; exact congrArg (·.layout) (Option.some.inj h)
  let newLoc : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout := { tf_sd.locals[dstIdx]'hlt_d with value := .live (.immediate imm) }
  let tf_out := { tf_sd with locals := tf_sd.locals.set dstIdx newLoc hlt_d }
  have hm_ok : Miri.Interpreter.Step.evalStatement hooks () (translateStmt stmt) m = ({ stack := ⟨#[tf_out]⟩, machine := mach' }, .ok ()) := by
    rw [heval]; unfold Miri.Interpreter.runRvalue
    rw [annealWriteImmediateLM2_2_live (m := { stack := ⟨#[tf_sd]⟩, machine := mach' }) (topFrame := tf_sd)
      rfl hlt_d hget_d]
  let tf' := { tf_out with location := .mir ⟨blockIdx, stmtIdx + 1⟩ }
  refine ⟨tf', miri_step_at_statement_ok hooks (m' := { stack := ⟨#[tf_out]⟩, machine := mach' }) hframes hbody hloc hbb hstmt hm_ok rfl hloc_sd, rfl, ?_⟩
  dsimp only [tf', tf_out, newLoc]; rw [Array.getElem?_set_self hlt_d, hlay_d]
private theorem annealCheckFnPointerOverlay_state_eq {fnPtrs : List FnPtrEntry} {ptr : Miri.Memory.Pointer (Option AnnealProv)} {st st' : AnnealStepState} {u : Unit}
    (h : annealCheckFnPointerOverlay fnPtrs ptr st = .ok u st') : st' = st := by
  unfold annealCheckFnPointerOverlay at h; dsimp only [Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, get, getThe, MonadStateOf.get, EStateM.get, throw, throwThe, MonadExceptOf.throw, EStateM.throw] at h
  cases h1 : ptr.intoPointerOrAddr with
  | error _ => simp only [h1] at h; cases h
  | ok _ =>
    simp only [h1] at h
    cases h2 : annealResolvePtr st.machine ptr 0 with
    | error _ => simp only [h2] at h; cases h
    | ok res =>
      simp only [h2] at h
      by_cases hnz : (res.offset != Miri.ABI.Size.ZERO) = true
      · simp only [hnz, ↓reduceIte] at h; cases h
      · simp only [hnz, Bool.false_eq_true, ↓reduceIte] at h
        cases hfn : (match fnPtrs with | [] => isFnPtrAllocId res.allocId.value.toNat | _ :: _ => (lookupFnPtr fnPtrs res.allocId.value.toNat).isSome)
        · simp only [hfn, Bool.false_eq_true, ↓reduceIte] at h; cases h
        · simp only [hfn, ↓reduceIte] at h; cases h; rfl
private theorem fnPtrs_miri_isFn_eq (fnPtrs : List FnPtrEntry) (aid : Nat) : fnPtrs ≠ [] → (match fnPtrs with | [] => isFnPtrAllocId aid | _ :: _ => (lookupFnPtr fnPtrs aid).isSome) =
      (lookupFnPtr fnPtrs aid).isSome := by
  intro hne; cases fnPtrs with | nil => exact False.elim (hne rfl) | cons _ _ => rfl
private theorem annealCheckFnPointerOverlay_cases {fnPtrs : List FnPtrEntry} {st : AnnealStepState} {ptrVal : ProvenancePtr} {mAllocId : Miri.Memory.AllocId} {mTag : Miri.Memory.BorTag} {baseAddr : UInt64}
    (haid : mAllocId.value.toNat = ptrVal.allocId) (hbase : st.machine.lookupBaseAddr mAllocId = some baseAddr) (hnow1 : baseAddr ≤ baseAddr + UInt64.ofNat ptrVal.offsetBytes)
    (hnow2 : (baseAddr + UInt64.ofNat ptrVal.offsetBytes - baseAddr).toNat = ptrVal.offsetBytes) :
    let mptr : Miri.Memory.Pointer AnnealProv := ⟨Miri.ABI.Size.ofBytes (baseAddr + UInt64.ofNat ptrVal.offsetBytes), .concrete mAllocId mTag⟩
    (ptrVal.offsetBytes ≠ 0 → annealCheckFnPointerOverlay fnPtrs mptr.withOptionalProvenance st = .error (.undefinedBehavior "InvalidFunctionPointer") st) ∧
    (ptrVal.offsetBytes = 0 → fnPtrs ≠ [] → lookupFnPtr fnPtrs ptrVal.allocId = none → annealCheckFnPointerOverlay fnPtrs mptr.withOptionalProvenance st = .error (.undefinedBehavior "InvalidFunctionPointer") st) ∧
    (∀ entry, ptrVal.offsetBytes = 0 → fnPtrs ≠ [] → lookupFnPtr fnPtrs ptrVal.allocId = some entry → annealCheckFnPointerOverlay fnPtrs mptr.withOptionalProvenance st = .ok () st) := by
  intro mptr
  have hres : annealResolvePtr st.machine mptr.withOptionalProvenance 0 = .ok ⟨mAllocId, Miri.ABI.Size.ofBytes (baseAddr + UInt64.ofNat ptrVal.offsetBytes - baseAddr), mTag⟩ := by
    unfold annealResolvePtr; dsimp only [mptr, Miri.Memory.Pointer.withOptionalProvenance, Miri.ABI.Size.ofBytes]; rw [hbase]; dsimp only; exact ite_eq_left_iff.mpr fun h => absurd hnow1 h
  have hinto : mptr.withOptionalProvenance.intoPointerOrAddr = .ok (Miri.Memory.Pointer.new mptr.provenance mptr.offset) := rfl; refine ⟨?_, ?_, ?_⟩
  · intro hoff_ne
    have hne_sz : (Miri.ABI.Size.ofBytes (baseAddr + UInt64.ofNat ptrVal.offsetBytes - baseAddr) != Miri.ABI.Size.ZERO) = true := by
      rw [bne_iff_ne]; intro heq; have hbt := congrArg (fun sz : Miri.ABI.Size => sz.bytes.toNat) heq; dsimp [Miri.ABI.Size.ofBytes, Miri.ABI.Size.ZERO] at hbt; rw [hnow2] at hbt; exact hoff_ne hbt
    unfold annealCheckFnPointerOverlay; dsimp only [Bind.bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get]; rw [hinto]; dsimp only; rw [hres]; dsimp only; rw [hne_sz]; rfl
  · intro hoff0 hfn_ne hnone
    have heq_sz : (Miri.ABI.Size.ofBytes (baseAddr + UInt64.ofNat ptrVal.offsetBytes - baseAddr) != Miri.ABI.Size.ZERO) = false := by rw [bne_eq_false_iff_eq, hoff0]; simp [Miri.ABI.Size.ofBytes, Miri.ABI.Size.ZERO]
    unfold annealCheckFnPointerOverlay; dsimp only [Bind.bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get]; rw [hinto]; dsimp only; rw [hres]; dsimp only; rw [heq_sz, fnPtrs_miri_isFn_eq fnPtrs _ hfn_ne, haid, hnone]; rfl
  · intro entry hoff0 hfn_ne hsome
    have heq_sz : (Miri.ABI.Size.ofBytes (baseAddr + UInt64.ofNat ptrVal.offsetBytes - baseAddr) != Miri.ABI.Size.ZERO) = false := by rw [bne_eq_false_iff_eq, hoff0]; simp [Miri.ABI.Size.ofBytes, Miri.ABI.Size.ZERO]
    unfold annealCheckFnPointerOverlay; dsimp only [Bind.bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get]; rw [hinto]; dsimp only; rw [hres]; dsimp only; rw [heq_sz, fnPtrs_miri_isFn_eq fnPtrs _ hfn_ne, haid, hsome]; rfl
private theorem ep2_activeCastCoercionKind?_singleton {body : CapturedMir} {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit} {mach : AnnealMachine} {bb : BasicBlockData} {stmt : Statement} {b i : Nat}
    {place : Place} {ck : String} {op : Operand} {targetTy : Ty} {sp : String} (hloc : tf.location = .mir ⟨b, i⟩) (hbb : get? body.basicBlocks b = some bb) (hstmt : get? bb.statements i = some stmt)
    (hsk : stmt = { kind := .assign place (.cast (.pointerCoercion ck) op targetTy), span := sp }) :
    activeCastCoercionKind? body { stack := ⟨#[tf]⟩, machine := mach } = some ck := by
  unfold activeCastCoercionKind?; rw [stack_currentFrame?_singleton ⟨#[tf]⟩ tf rfl]; dsimp only; rw [hloc]; dsimp only; rw [hbb]; dsimp only; rw [hstmt]; subst hsk; rfl
private theorem ep2_castTypeInfoOverlay_closure_singleton {body : CapturedMir} {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit} {mach : AnnealMachine} {bb : BasicBlockData} {stmt : Statement} {b i : Nat}
    {place : Place} {ck : String} {op : Operand} {targetTy srcTy : Ty} {sp : String} {defPath : DefPath} {upvars : List RigidTy} (hloc : tf.location = .mir ⟨b, i⟩)
    (hbb : get? body.basicBlocks b = some bb) (hstmt : get? bb.statements i = some stmt) (hsk : stmt = { kind := .assign place (.cast (.pointerCoercion ck) op targetTy), span := sp })
    (hop : operandTy body.localDecls body.layouts op = some srcTy) (hsrc_ty : srcTy.kind = .closure defPath upvars) :
    castTypeInfoOverlay body { stack := ⟨#[tf]⟩, machine := mach } (encodeTyId srcTy) = .ok (.closure 0 #[] upvars.length) := by
  unfold castTypeInfoOverlay activeClosureCastTypeInfo?; rw [stack_currentFrame?_singleton ⟨#[tf]⟩ tf rfl]; dsimp only; rw [hloc]; dsimp only; rw [hbb]; dsimp only; rw [hstmt]; subst hsk; dsimp only
  rw [hop]; dsimp only; rw [hsrc_ty]; simp
private theorem ep2_activeClosureCastTypeInfo?_none {body : CapturedMir} {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {mach : AnnealMachine} {bb : BasicBlockData} {stmt : Statement} {b i : Nat} {tyId : Miri.MIR.TyId} (hloc : tf.location = .mir ⟨b, i⟩) (hbb : get? body.basicBlocks b = some bb) (hstmt : get? bb.statements i = some stmt)
    (hnot : (∃ place op targetTy, stmt.kind = .assign place (.cast .fnPtrToPtr op targetTy)) ∨ (∃ place ck op targetTy srcTy, stmt.kind = .assign place (.cast (.pointerCoercion ck) op targetTy) ∧
        operandTy body.localDecls body.layouts op = some srcTy ∧ ∀ dp uv, srcTy.kind ≠ .closure dp uv)) :
    activeClosureCastTypeInfo? body { stack := ⟨#[tf]⟩, machine := mach } tyId = none := by
  unfold activeClosureCastTypeInfo?; rw [stack_currentFrame?_singleton ⟨#[tf]⟩ tf rfl]; dsimp only; rw [hloc]; dsimp only; rw [hbb]; dsimp only; rw [hstmt]
  rcases stmt with ⟨fk, sp⟩; dsimp only at hnot
  rcases hnot with ⟨p, op, t, hk⟩ | ⟨p, ck, op, t, sTy, hk, hop, hnc⟩
  · subst hk; rfl
  · subst hk; dsimp only; rw [hop]; dsimp only
    cases hkS : sTy.kind with
    | closure dp uv => exact False.elim (hnc dp uv hkS)
    | _ => rfl
private def ep2LiftExcept {S A : Type} (r : Except Miri.Interpreter.StepError A) : Miri.Interpreter.RvalueM S A := match r with | .ok value => pure value | .error error => throw error
private theorem ep2_scalarInt_toPointer_dangling (sc : MirAst.ScalarInt) (msc : Miri.Memory.ScalarInt) (hrel : ScalarRel sc msc) (hsc8 : sc.sizeBytes = 8) :
    ∃ addr, (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) msc).toPointer annealTargetDataLayout = .ok (Miri.Memory.Pointer.withoutProvenance addr) :=
  ⟨UInt64.ofNat sc.bits, scalar_fromScalarInt_toPointer_eq hrel hsc8⟩
private theorem evalStatement_overlay_cast_fnPtr_common {body : CapturedMir} {callees : List CapturedMir} {poppedFrame : Miri.TreeBorrows.FrameState} {fnPtrs : List FnPtrEntry} {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit} {bb : BasicBlockData} {stmt : Statement} {ck : CastKind} {blockIdx stmtIdx : Nat} {srcIdx dstIdx : Local} {srcDecl dstDecl : LocalDecl}
    {ins : List RigidTy} {out : RigidTy} {saf : Safety} {srcAbi : CallConv} (hframes : m.stack.frames = #[topFrame]) (hloc : topFrame.location = .mir ⟨blockIdx, stmtIdx⟩)
    (hbb : get? body.basicBlocks blockIdx = some bb) (hstmt : get? bb.statements stmtIdx = some stmt) (hkind : stmt.kind = .assign ⟨dstIdx, .nil⟩ (.cast ck (.copy ⟨srcIdx, .nil⟩) dstDecl.ty))
    (hsrc_decl : get? body.localDecls srcIdx = some srcDecl) (hdst_decl : get? body.localDecls dstIdx = some dstDecl) (hsrc_ty : srcDecl.ty.kind = .fnPtr ins out saf srcAbi)
    (hno_wide_d : isWideOverlayPlace body.localDecls ⟨dstIdx, #[]⟩ = false) (hlt_s : srcIdx < topFrame.locals.size) (hlt_d : dstIdx < topFrame.locals.size)
    (hc_d : ∀ l, (topFrame.locals[dstIdx]'hlt_d).layout = some l → l = translateTy dstDecl.ty body.layouts) (hck : (ck = .fnPtrToPtr ∧ (∃ ptId, castTypeInfoOfEncodedTyIdWideSlice (encodeTyId dstDecl.ty) = .ok (.rawPointer ptId)) ∧
        (translateTy dstDecl.ty body.layouts).layout.size = Miri.ABI.Size.ofBytes 8) ∨
      (ck = .pointerCoercion "UnsafeFnPointer" ∧ encodeTyId dstDecl.ty = 42)) :
    let tf_sd := ep2CacheDstSrc topFrame hlt_d hlt_s (translateTy dstDecl.ty body.layouts) (translateTy srcDecl.ty body.layouts); let st_sd : AnnealStepState := { stack := ⟨#[tf_sd]⟩, machine := m.machine }
    let hooks := annealStepHooksUnwindFnPtrClosure body callees poppedFrame fnPtrs
    (∀ cSrc, topFrame.locals[srcIdx]'hlt_s = ⟨.dead, cSrc⟩ → (∀ l, cSrc = some l → l = translateTy srcDecl.ty body.layouts) → Miri.Interpreter.Step.evalStatement hooks () (translateStmt stmt) m =
        (st_sd, .error (.undefinedBehavior "read of dead local"))) ∧
    (∀ cSrc, topFrame.locals[srcIdx]'hlt_s = ⟨.live (.immediate .uninit), cSrc⟩ → (∀ l, cSrc = some l → l = translateTy srcDecl.ty body.layouts) → Miri.Interpreter.Step.evalStatement hooks () (translateStmt stmt) m =
        (st_sd, .error (.undefinedBehavior "read of uninitialized local"))) ∧
    (∀ sc msc cSrc, ScalarRel sc msc → sc.sizeBytes = 8 → topFrame.locals[srcIdx]'hlt_s = ⟨.live (.immediate (.scalar (.fromScalarInt msc))), cSrc⟩ → (∀ l, cSrc = some l → l = translateTy srcDecl.ty body.layouts) →
      Miri.Interpreter.Step.evalStatement hooks () (translateStmt stmt) m = (st_sd, .error (.undefinedBehavior "DanglingIntPointer"))) ∧
    (∀ (mptr : Miri.Memory.Pointer AnnealProv) cSrc,
      let msc := Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr
      topFrame.locals[srcIdx]'hlt_s = ⟨.live (.immediate (.scalar msc)), cSrc⟩ → (∀ l, cSrc = some l → l = translateTy srcDecl.ty body.layouts) →
      (∀ e, annealCheckFnPointerOverlay fnPtrs mptr.withOptionalProvenance st_sd = .error e st_sd → Miri.Interpreter.Step.evalStatement hooks () (translateStmt stmt) m = (st_sd, .error e)) ∧
      (annealCheckFnPointerOverlay fnPtrs mptr.withOptionalProvenance st_sd = .ok () st_sd → Miri.Interpreter.Step.evalStatement hooks () (translateStmt stmt) m = Miri.Interpreter.runRvalue (annealWriteImmediateLM2_2 (.scalar msc)
              ⟨.local 0 dstIdx none topFrame.localsIdentity, translateTy dstDecl.ty body.layouts⟩) st_sd)) := by
  intro tf_sd st_sd hooks; have hty42 : (translateTy srcDecl.ty body.layouts).ty = 42 := by unfold translateTy encodeTyId; cases hmk : srcDecl.ty with | mk k _ => rw [hmk] at hsrc_ty; dsimp at hsrc_ty; subst hsrc_ty; rfl
  have hsrc_sz8 : (translateTy srcDecl.ty body.layouts).layout.size = Miri.ABI.Size.ofBytes 8 := by unfold translateTy; cases hmk : srcDecl.ty with | mk k _ => rw [hmk] at hsrc_ty; dsimp at hsrc_ty; subst hsrc_ty; rfl
  have hsrc_uninh : (translateTy srcDecl.ty body.layouts).layout.isUninhabited = false := by unfold translateTy; cases hmk : srcDecl.ty with | mk k _ => rw [hmk] at hsrc_ty; dsimp at hsrc_ty; subst hsrc_ty; rfl
  have hno_wide_s : isWideOverlayPlace body.localDecls ⟨srcIdx, #[]⟩ = false := by
    apply isWideOverlayPlace_eq_false_of_decl hsrc_decl <;> (cases hmk : srcDecl.ty with | mk k _ => rw [hmk] at hsrc_ty; dsimp at hsrc_ty; subst hsrc_ty; rfl)
  have hov_ck : isOverlayCastKind (translateCastKind ck) = true := by rcases hck with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> rfl
  have hloc_sd : tf_sd.location = .mir ⟨blockIdx, stmtIdx⟩ := by dsimp only [tf_sd]; rw [ep2CacheDstSrc_location]; exact hloc
  have hop_ty : operandTy body.localDecls body.layouts (.copy ⟨srcIdx, .nil⟩) = some srcDecl.ty := by simp [operandTy, placeTy, hsrc_decl]
  have hnone_act : ∀ tyId, activeClosureCastTypeInfo? body { stack := ⟨#[tf_sd]⟩, machine := m.machine } tyId = none := by
    intro tyId; apply ep2_activeClosureCastTypeInfo?_none hloc_sd hbb hstmt
    rcases hck with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact Or.inl ⟨⟨dstIdx, .nil⟩, .copy ⟨srcIdx, .nil⟩, dstDecl.ty, hkind⟩
    · exact Or.inr ⟨⟨dstIdx, .nil⟩, "UnsafeFnPointer", .copy ⟨srcIdx, .nil⟩, dstDecl.ty, srcDecl.ty, hkind, hop_ty, fun dp uv hk => by rw [hsrc_ty] at hk; cases hk⟩
  have hinfo42 : castTypeInfoOverlay body { stack := ⟨#[tf_sd]⟩, machine := m.machine } 42 = .ok .fnPointer := by unfold castTypeInfoOverlay; rw [hnone_act 42]; rfl
  have hty_id_eq : encodeTyId dstDecl.ty = (translateTy dstDecl.ty body.layouts).ty := rfl
  have ⟨heval_dead, heval_live⟩ := evalStatement_overlay_assign_cast_copy (callees := callees) (poppedFrame := poppedFrame) (fnPtrs := fnPtrs) hframes hkind hov_ck hsrc_decl hdst_decl hno_wide_s hno_wide_d hlt_s hlt_d hc_d
  have hcast_eq : ∀ immS cSrc, topFrame.locals[srcIdx]'hlt_s = ⟨.live (.immediate immS), cSrc⟩ → (∀ l, cSrc = some l → l = translateTy srcDecl.ty body.layouts) → Miri.Interpreter.Step.evalStatement hooks () (translateStmt stmt) m =
      Miri.Interpreter.runRvalue (Miri.Interpreter.Cast.cast (annealCastHooksUnwindFnPtrClosure body fnPtrs) () 16 ⟨.immediate immS, translateTy srcDecl.ty body.layouts⟩ (translateCastKind ck) (encodeTyId dstDecl.ty)
          ⟨.local 0 dstIdx none topFrame.localsIdentity, translateTy dstDecl.ty body.layouts⟩) st_sd := by
    intro immS cSrc hmls_s hc_s; rw [heval_live immS cSrc (by rw [Array.getElem?_eq_getElem hlt_s, hmls_s]) hc_s]
    rcases hck with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> rfl
  have hsz_nz_eq : (Miri.ABI.Size.ofBytes 8 == Miri.ABI.Size.ZERO) = false := by decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro cSrc hmls_s hc_s; exact heval_dead cSrc (by rw [Array.getElem?_eq_getElem hlt_s, hmls_s]) hc_s
  · intro cSrc hmls_s hc_s
    rw [hcast_eq .uninit cSrc hmls_s hc_s]
    cases hmkS : srcDecl.ty with | mk kS lS =>
      rw [hmkS] at hsrc_ty; dsimp at hsrc_ty; subst hsrc_ty; have h42s : (translateTy { kind := .fnPtr ins out saf srcAbi, layoutIdx := lS } body.layouts).ty = 42 := rfl
      rcases hck with ⟨rfl, _⟩ | ⟨rfl, _⟩
      · unfold Miri.Interpreter.runRvalue Miri.Interpreter.Cast.cast annealCastHooksUnwindFnPtrClosure annealCastHooksLM4_1 annealCastHooks
        simp only [translateCastKind, st_sd, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, get, getThe, MonadStateOf.get, EStateM.get, hty_id_eq, beq_self_eq_true, ↓reduceIte, Bool.false_eq_true, h42s, hinfo42]
        with_unfolding_all rfl
      · rw [show translateCastKind (.pointerCoercion "UnsafeFnPointer") = .PointerCoercion .UnsafeFnPointer .Implicit from rfl]
        unfold Miri.Interpreter.runRvalue Miri.Interpreter.Cast.cast annealCastHooksUnwindFnPtrClosure annealCastHooksLM4_1 annealCastHooks
        simp only [st_sd, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, get, getThe, MonadStateOf.get, EStateM.get, hty_id_eq, beq_self_eq_true, ↓reduceIte, Bool.false_eq_true, h42s, hinfo42]; with_unfolding_all rfl
  · intro sc msc cSrc hrel hsc8 hmls_s hc_s
    obtain ⟨addr, hptr_ok⟩ := ep2_scalarInt_toPointer_dangling sc msc hrel hsc8
    have hdang : annealCheckFnPointerOverlay fnPtrs (Miri.Memory.Pointer.withoutProvenance addr) st_sd = .error (.undefinedBehavior "DanglingIntPointer") st_sd := rfl; rw [hcast_eq (.scalar (.fromScalarInt msc)) cSrc hmls_s hc_s]
    cases hmkS : srcDecl.ty with | mk kS lS =>
      rw [hmkS] at hsrc_ty; dsimp at hsrc_ty; subst hsrc_ty; have h42s : (translateTy { kind := .fnPtr ins out saf srcAbi, layoutIdx := lS } body.layouts).ty = 42 := rfl; let cHooks := annealCastHooksUnwindFnPtrClosure body fnPtrs
      let srcOp : Miri.Interpreter.OpTy AnnealProv := ⟨.immediate (.scalar (.fromScalarInt msc)), translateTy { kind := .fnPtr ins out saf srcAbi, layoutIdx := lS } body.layouts⟩
      let dstPl : Miri.Interpreter.RuntimePlace AnnealProv := ⟨.local 0 dstIdx none topFrame.localsIdentity, translateTy dstDecl.ty body.layouts⟩
      let hptrL := ep2LiftExcept (S := AnnealStepState) ((Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) msc).toPointer annealTargetDataLayout |>.mapError Miri.Interpreter.ScalarOps.scalarError)
      rcases hck with ⟨rfl, _⟩ | ⟨rfl, _⟩
      · refine Eq.trans (b := Miri.Interpreter.runRvalue (EStateM.bind hptrL fun p => EStateM.bind (annealCheckFnPointerOverlay fnPtrs p) fun _ => do
              let value ← cHooks.readImmediate () srcOp
              let result ← Miri.Interpreter.Cast.ptrToPtr cHooks () value (translateTy dstDecl.ty body.layouts)
              cHooks.writeImmediate () result.imm dstPl) st_sd) ?_ ?_
        · unfold Miri.Interpreter.runRvalue Miri.Interpreter.Cast.cast
          dsimp only [translateCastKind, st_sd, cHooks, srcOp, dstPl, hptrL, annealCastHooksUnwindFnPtrClosure, annealCastHooksLM4_1, annealCastHooks]
          simp only [Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, get, getThe, MonadStateOf.get, EStateM.get, hty_id_eq, beq_self_eq_true, ↓reduceIte, Bool.false_eq_true, h42s, hinfo42]; with_unfolding_all rfl
        · unfold Miri.Interpreter.runRvalue; dsimp only [hptrL, ep2LiftExcept, Except.mapError]; rw [hptr_ok]; simp only [EStateM.bind, Pure.pure, EStateM.pure, hdang]
      · refine Eq.trans (b := Miri.Interpreter.runRvalue (EStateM.bind hptrL fun p => EStateM.bind (annealCheckFnPointerOverlay fnPtrs p) fun _ => do
              let value ← cHooks.readImmediate () srcOp
              let .fnPointer ← cHooks.typeInfo () (encodeTyId dstDecl.ty)
                | throw (.invalidProgram "unsafe fn pointer target is not fn pointer")
              cHooks.writeImmediate () value.imm dstPl) st_sd) ?_ ?_
        · rw [show translateCastKind (.pointerCoercion "UnsafeFnPointer") = .PointerCoercion .UnsafeFnPointer .Implicit from rfl]
          unfold Miri.Interpreter.runRvalue Miri.Interpreter.Cast.cast; dsimp only [st_sd, cHooks, srcOp, dstPl, hptrL, annealCastHooksUnwindFnPtrClosure, annealCastHooksLM4_1, annealCastHooks]
          simp only [Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, get, getThe, MonadStateOf.get, EStateM.get, hty_id_eq, beq_self_eq_true, ↓reduceIte, Bool.false_eq_true, h42s, hinfo42]; with_unfolding_all rfl
        · unfold Miri.Interpreter.runRvalue; dsimp only [hptrL, ep2LiftExcept, Except.mapError]; rw [hptr_ok]; simp only [EStateM.bind, Pure.pure, EStateM.pure, hdang]
  · intro mptr cSrc msc hmls_s hc_s
    have hrun : ∀ (f : Unit → Miri.Interpreter.RvalueM AnnealStepState Unit), (Miri.Interpreter.runRvalue (annealCheckFnPointerOverlay fnPtrs mptr.withOptionalProvenance >>= f) st_sd) =
        match annealCheckFnPointerOverlay fnPtrs mptr.withOptionalProvenance st_sd with
        | .error e st' => (st', .error e)
        | .ok () st' => Miri.Interpreter.runRvalue (f ()) st' := by
      intro f; dsimp only [Miri.Interpreter.runRvalue, Bind.bind, EStateM.bind]
      cases annealCheckFnPointerOverlay fnPtrs mptr.withOptionalProvenance st_sd <;> rfl
    have htoP : msc.toPointer annealTargetDataLayout = .ok mptr.withOptionalProvenance := rfl
    rcases hck with ⟨rfl, ⟨ptId, hdst_info⟩, hdst_sz8⟩ | ⟨rfl, hty42_d⟩
    · have hpref : Miri.Interpreter.Step.evalStatement hooks () (translateStmt stmt) m = Miri.Interpreter.runRvalue (annealCheckFnPointerOverlay fnPtrs mptr.withOptionalProvenance >>= fun _ => do
              let result ← Miri.Interpreter.Cast.ptrToPtr (annealCastHooksUnwindFnPtrClosure body fnPtrs) () ⟨.scalar msc, translateTy srcDecl.ty body.layouts⟩ (translateTy dstDecl.ty body.layouts)
              annealWriteImmediateLM2_2 result.imm ⟨.local 0 dstIdx none topFrame.localsIdentity, translateTy dstDecl.ty body.layouts⟩) st_sd := by
        rw [hcast_eq (.scalar msc) cSrc hmls_s hc_s]; dsimp only [translateCastKind, st_sd]
        unfold Miri.Interpreter.runRvalue Miri.Interpreter.Cast.cast annealCastHooksUnwindFnPtrClosure annealCastHooksLM4_1 annealCastHooks annealReadImmediateOverlay
        with_unfolding_all
          simp only [Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, get, getThe, MonadStateOf.get, EStateM.get, hty_id_eq, beq_self_eq_true, ↓reduceIte, Bool.false_eq_true, hty42, hinfo42]; rfl
      have hinfo_dst_ex : ∃ ptId', castTypeInfoOverlay body { stack := ⟨#[tf_sd]⟩, machine := m.machine } (translateTy dstDecl.ty body.layouts).ty = .ok (.rawPointer ptId') := by
        have hd_ty : (translateTy dstDecl.ty body.layouts).ty = encodeTyId dstDecl.ty := rfl; rw [hd_ty]; unfold castTypeInfoOverlay; rw [hnone_act]; dsimp only
        by_cases h40 : (encodeTyId dstDecl.ty == 40) = true
        · exact ⟨40, by simp [h40]⟩
        · have hne41 : (encodeTyId dstDecl.ty == 41) = false := if h : encodeTyId dstDecl.ty = 41 then by rw [h] at hdst_info; cases hdst_info else beq_false_of_ne h
          have hne42 : (encodeTyId dstDecl.ty == 42) = false := if h : encodeTyId dstDecl.ty = 42 then by rw [h] at hdst_info; cases hdst_info else beq_false_of_ne h
          by_cases hDyn : (encodeTyId dstDecl.ty == wideRawDynPtrTyId) = true
          · exact ⟨dynPointeeTyId, by simp [h40, hne41, hne42, hDyn]⟩
          · exact ⟨ptId, by simp [h40, hne41, hne42, hDyn, hdst_info]⟩
      obtain ⟨ptId', hinfo_dst⟩ := hinfo_dst_ex; refine ⟨fun e herr => by rw [hpref, hrun, herr], fun hok => ?_⟩
      rw [hpref, hrun, hok]
      have hptrToPtr_ok : Miri.Interpreter.Cast.ptrToPtr (annealCastHooksUnwindFnPtrClosure body fnPtrs) () ⟨.scalar msc, translateTy srcDecl.ty body.layouts⟩ (translateTy dstDecl.ty body.layouts) st_sd =
          .ok ⟨.scalar msc, translateTy dstDecl.ty body.layouts⟩ st_sd := by
        dsimp only [st_sd]
        with_unfolding_all
          simp only [Miri.Interpreter.Cast.ptrToPtr, annealCastHooksUnwindFnPtrClosure, hty42, hinfo42, hsrc_sz8, hdst_sz8, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, get, getThe, MonadStateOf.get, EStateM.get]
          change (if false = true then _ else _ : Miri.Interpreter.RvalueM AnnealStepState _) _ = _
          simp only [Bool.false_eq_true, ↓reduceIte, EStateM.bind, EStateM.pure, EStateM.get, hinfo_dst, beq_self_eq_true]
      dsimp only [Miri.Interpreter.runRvalue, Bind.bind, EStateM.bind]; rw [hptrToPtr_ok]
    · have hpref : Miri.Interpreter.Step.evalStatement hooks () (translateStmt stmt) m = Miri.Interpreter.runRvalue (annealCheckFnPointerOverlay fnPtrs mptr.withOptionalProvenance >>= fun _ => do
              let info ← (annealCastHooksUnwindFnPtrClosure body fnPtrs).typeInfo () 42
              match info with
              | .fnPointer =>
                annealWriteImmediateLM2_2 (.scalar msc) ⟨.local 0 dstIdx none topFrame.localsIdentity, translateTy dstDecl.ty body.layouts⟩
              | _ => throw (.invalidProgram "unsafe fn pointer target is not fn pointer")) st_sd := by
        rw [hcast_eq (.scalar msc) cSrc hmls_s hc_s]; rw [show translateCastKind (.pointerCoercion "UnsafeFnPointer") = .PointerCoercion .UnsafeFnPointer .Implicit from rfl]
        cases hmkS : srcDecl.ty with | mk kS lS =>
          rw [hmkS] at hsrc_ty; dsimp at hsrc_ty; subst hsrc_ty; have h42s : (translateTy { kind := .fnPtr ins out saf srcAbi, layoutIdx := lS } body.layouts).ty = 42 := rfl
          unfold Miri.Interpreter.runRvalue Miri.Interpreter.Cast.cast annealCastHooksUnwindFnPtrClosure annealCastHooksLM4_1 annealCastHooks annealReadImmediateOverlay
          simp only [st_sd, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, get, getThe, MonadStateOf.get, EStateM.get, hty_id_eq, beq_self_eq_true, ↓reduceIte, Bool.false_eq_true, h42s, hinfo42]; rw [← hty_id_eq, hty42_d]
          with_unfolding_all rfl
      refine ⟨fun e herr => by rw [hpref, hrun, herr], fun hok => ?_⟩
      rw [hpref, hrun, hok]
      dsimp only [Miri.Interpreter.runRvalue, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, annealCastHooksUnwindFnPtrClosure, annealCastHooksLM4_1, annealCastHooks, get, getThe, MonadStateOf.get, EStateM.get, st_sd]
      rw [hinfo42]; rfl

/-! ## Section 5. `C6` (`CastKind.fnPtrToPtr`) & `C7` (`CastKind.subtype`) -/
/-- **`C6` Base-Hook Boundary**: `annealStepHooksLM4_1` rejects `FnPtrToPtr`
with `.unsupported` because `TyId 42` has no base `castTypeInfo`. -/
theorem step_cast_fnPtrToPtr_baseHooks_unsupported_boundary {body : CapturedMir} {callees : List CapturedMir} {poppedFrame : Miri.TreeBorrows.FrameState} {fnPtrs : List FnPtrEntry} {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit} {bb : BasicBlockData} {stmt : Statement} {srcIdx dstIdx : Local} {srcDecl dstDecl : LocalDecl}
    {immSrc immDst : Miri.Interpreter.Immediate AnnealProv} {cSrc cDst : Option Miri.Interpreter.LocalLayout} {blockIdx stmtIdx : Nat} (hframes : m.stack.frames = #[topFrame])
    (hbody : topFrame.body = translateBody body) (hloc : topFrame.location = .mir ⟨blockIdx, stmtIdx⟩) (hbb : get? body.basicBlocks blockIdx = some bb) (hstmt : get? bb.statements stmtIdx = some stmt)
    (hkind : stmt.kind = .assign ⟨dstIdx, .nil⟩ (.cast .fnPtrToPtr (.copy ⟨srcIdx, .nil⟩) dstDecl.ty)) (hsrc_decl : get? body.localDecls srcIdx = some srcDecl) (hdst_decl : get? body.localDecls dstIdx = some dstDecl)
    (hsrc_ty : ∃ ins out saf abi, srcDecl.ty.kind = .fnPtr ins out saf abi) (hlt_s : srcIdx < topFrame.locals.size) (hlt_d : dstIdx < topFrame.locals.size) (hmls_s : topFrame.locals[srcIdx]? = some ⟨.live (.immediate immSrc), cSrc⟩)
    (hmls_d : topFrame.locals[dstIdx]? = some ⟨.live (.immediate immDst), cDst⟩) (hc_s : ∀ l, cSrc = some l → l = translateTy srcDecl.ty body.layouts) (hc_d : ∀ l, cDst = some l → l = translateTy dstDecl.ty body.layouts) :
    (Miri.Interpreter.Step.step (annealStepHooksLM4_1 body callees poppedFrame fnPtrs) () m).2 = .error (.unsupported "cast typeInfo not wired in scalar fragment for TyId 42") := by
  obtain ⟨ins, out, saf, abi, hfn_k⟩ := hsrc_ty
  have hty42 : (translateTy srcDecl.ty body.layouts).ty = 42 := by unfold translateTy encodeTyId; cases hmk : srcDecl.ty with | mk k _ => rw [hmk] at hfn_k; dsimp at hfn_k; subst hfn_k; rfl
  obtain ⟨cSrc', hmls_s_d, hc_s_d⟩ := cacheFrameLocalLayout_getElem?_preserve topFrame hdst_decl hsrc_decl hlt_d hmls_s hc_s
  have hmls_d_eq : topFrame.locals[dstIdx]'hlt_d = ⟨.live (.immediate immDst), cDst⟩ := Option.some.inj ((Array.getElem?_eq_getElem hlt_d).symm.trans hmls_d)
  have heval_dst := annealEvalPlace_unprojected_root hframes hlt_d hdst_decl (by rw [hmls_d_eq]; exact hc_d); let tf_d := cacheFrameLocalLayout topFrame dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
  have hlt_s' : srcIdx < tf_d.locals.size := by rw [cacheFrameLocalLayout_size]; exact hlt_s
  have heval_src := annealEvalOperand_copy_live (m := { m with stack := ⟨#[tf_d]⟩ }) (known := none)
    rfl hlt_s' hsrc_decl (Option.some.inj ((Array.getElem?_eq_getElem hlt_s').symm.trans hmls_s_d)) hc_s_d
  dsimp only at heval_src; let tf_sd := cacheFrameLocalLayout tf_d srcIdx hlt_s' (translateTy srcDecl.ty body.layouts); have hty_id_eq : encodeTyId dstDecl.ty = (translateTy dstDecl.ty body.layouts).ty := rfl
  have hm_err : Miri.Interpreter.Step.evalStatement (annealStepHooksLM4_1 body callees poppedFrame fnPtrs) () (translateStmt stmt) m = ({ m with stack := ⟨#[tf_sd]⟩ },
       .error (.unsupported "cast typeInfo not wired in scalar fragment for TyId 42")) := by
    unfold Miri.Interpreter.Step.evalStatement translateStmt; rw [hkind]
    dsimp only [translateStmtKind, translateRvalue, translateCastKind, translateOperand, translatePlace, List.map, List.toArray, annealStepHooksLM4_1, annealStepHooks, annealRvalueHooksLM4_1, annealRvalueHooks,
      Miri.Interpreter.evalRvalueIntoPlace]
    unfold Miri.Interpreter.runRvalue; rw [EStateM.bind_eq_ok heval_dst, EStateM.bind_eq_ok heval_src]
    with_unfolding_all
      simp [Miri.Interpreter.Cast.cast, annealCastHooks, hty_id_eq, hty42, castTypeInfoOfEncodedTyId, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, throw, throwThe, MonadExceptOf.throw, tf_sd]; rfl
  rw [miri_step_at_statement_error _ hframes hbody hloc hbb hstmt hm_err]
/-- **`C6` Complete `FnPtrToPtr` Simulation**: covers end-to-end `Step.step` UB
equivalence on `.dead`, `.uninit`, dangling integer scalar
(`DanglingIntPointer`), nonzero-offset `fnPtr`, and non-fn-alloc pointers,
plus positive lockstep execution preserving `PtrRel`, PC advance, and
`m'.machine = m.machine`. -/
theorem step_cast_fnPtrToPtr_simulation {body : CapturedMir} {s : MachineState} {m : AnnealStepState} {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {srcIdx dstIdx : Local} {srcDecl dstDecl : LocalDecl} {ins : List RigidTy} {out : RigidTy} {saf : Safety} {srcAbi : CallConv} {mutDst : Mutability} {ptDst : RigidTy} {ptId : Miri.MIR.TyId} {bb : BasicBlockData} {stmt : Statement}
    (hframes : m.stack.frames = #[topFrame]) (hbody : topFrame.body = translateBody body) (hloc : topFrame.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩) (hphase : ∀ p, body.phase ≠ .other p)
    (hcal : s.memory.activeCallee = none) (hbor_nil : s.memory.borrows = .nil) (hprot_nil : s.memory.activeProtectors = .nil) (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some stmt) (hkind : stmt.kind = .assign ⟨dstIdx, .nil⟩ (.cast .fnPtrToPtr (.copy ⟨srcIdx, .nil⟩) dstDecl.ty)) (hsrc_decl : get? body.localDecls srcIdx = some srcDecl)
    (hdst_decl : get? body.localDecls dstIdx = some dstDecl) (hsrc_ty : srcDecl.ty.kind = .fnPtr ins out saf srcAbi) (hdst_ty : dstDecl.ty.kind = .rawPtr mutDst ptDst) (hdst_thin : isThinRawPtrTy dstDecl.ty = true ∧
      isWideSliceOrPointeeTy dstDecl.ty = false ∧ isWideDynRawPtrTy dstDecl.ty = false)
    (hdst_info : castTypeInfoOfEncodedTyIdWideSlice (encodeTyId dstDecl.ty) = .ok (.rawPointer ptId)) (hne_sd : dstIdx ≠ srcIdx) {slot_d : LocalSlot} {immDst : Miri.Interpreter.Immediate AnnealProv}
    {cDst : Option Miri.Interpreter.LocalLayout} (hlt_af_d : dstIdx < s.frame.locals.length) (hlt_mf_d : dstIdx < topFrame.locals.size) (hslot_d : get? s.frame.locals dstIdx = some slot_d)
    (hnot_dead_d : slot_d ≠ .dead) (hmls_d : topFrame.locals[dstIdx]'hlt_mf_d = ⟨.live (.immediate immDst), cDst⟩) (hc_d : ∀ l, cDst = some l → l = translateTy dstDecl.ty body.layouts) (hlt_mf_s : srcIdx < topFrame.locals.size) :
    let hooks := annealStepHooksUnwindFnPtrClosureForState body s
    (∀ cSrc, get? s.frame.locals srcIdx = some .dead → topFrame.locals[srcIdx]'hlt_mf_s = ⟨.dead, cSrc⟩ → (∀ l, cSrc = some l → l = translateTy srcDecl.ty body.layouts) →
      StepRel body m (stepMirFn body s) (Miri.Interpreter.Step.step hooks () m)) ∧
    (∀ cSrc, get? s.frame.locals srcIdx = some .uninit → topFrame.locals[srcIdx]'hlt_mf_s = ⟨.live (.immediate .uninit), cSrc⟩ → (∀ l, cSrc = some l → l = translateTy srcDecl.ty body.layouts) →
      StepRel body m (stepMirFn body s) (Miri.Interpreter.Step.step hooks () m)) ∧
    (∀ sc msc cSrc, ScalarRel sc msc → sc.sizeBytes = 8 → get? s.frame.locals srcIdx = some (.init (.scalar sc)) → topFrame.locals[srcIdx]'hlt_mf_s = ⟨.live (.immediate (.scalar (.fromScalarInt msc))), cSrc⟩ →
      (∀ l, cSrc = some l → l = translateTy srcDecl.ty body.layouts) → StepRel body m (stepMirFn body s) (Miri.Interpreter.Step.step hooks () m)) ∧
    (∀ (ptrVal : ProvenancePtr) (mAllocId : Miri.Memory.AllocId) (mTag : Miri.Memory.BorTag) (baseAddr : UInt64) (cSrc : Option Miri.Interpreter.LocalLayout), get? s.frame.locals srcIdx = some (.init (.ptr ptrVal 8)) →
      mAllocId.value.toNat = ptrVal.allocId → m.machine.lookupBaseAddr mAllocId = some baseAddr → baseAddr ≤ baseAddr + UInt64.ofNat ptrVal.offsetBytes →
      (baseAddr + UInt64.ofNat ptrVal.offsetBytes - baseAddr).toNat = ptrVal.offsetBytes →
      let mptr : Miri.Memory.Pointer AnnealProv := ⟨Miri.ABI.Size.ofBytes (baseAddr + UInt64.ofNat ptrVal.offsetBytes), .concrete mAllocId mTag⟩; let msc := Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr
      topFrame.locals[srcIdx]'hlt_mf_s = ⟨.live (.immediate (.scalar msc)), cSrc⟩ → (∀ l, cSrc = some l → l = translateTy srcDecl.ty body.layouts) →
      (ptrVal.offsetBytes ≠ 0 → StepRel body m (stepMirFn body s) (Miri.Interpreter.Step.step hooks () m)) ∧ (ptrVal.offsetBytes = 0 → s.memory.fnPtrs ≠ [] → lookupFnPtr s.memory.fnPtrs ptrVal.allocId = none →
        StepRel body m (stepMirFn body s) (Miri.Interpreter.Step.step hooks () m)) ∧
      (∀ entry, ptrVal.offsetBytes = 0 → s.memory.fnPtrs ≠ [] → lookupFnPtr s.memory.fnPtrs ptrVal.allocId = some entry → callConvEq srcAbi .rustIntrinsic = false → (match entry.fnSig with
         | none => true
         | some (.fnPtr _ _ _ sigAbi) => !callConvEq sigAbi .rustIntrinsic
         | some _ => false) = true →
        ∃ s' tf', stepMirFn body s = .step s' ∧ s'.frame.blockIdx = s.frame.blockIdx ∧ s'.frame.stmtIdx = s.frame.stmtIdx + 1 ∧ Miri.Interpreter.Step.step hooks () m = ({ stack := ⟨#[tf']⟩, machine := m.machine }, .ok true) ∧
          tf'.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx + 1⟩ ∧ get? s'.frame.locals dstIdx = some (.init (.ptr ptrVal 8)) ∧ tf'.locals[dstIdx]? =
            some ⟨.live (.immediate (.scalar msc)), some (translateTy dstDecl.ty body.layouts)⟩ ∧
          (∀ allocMap, PtrRel allocMap ptrVal mptr → PtrRel allocMap ptrVal mptr))) := by
  intro hooks; have hact : activeMirBody body s = body := by simp [activeMirBody, hcal]
  have hhooks_eq : hooks = annealStepHooksUnwindFnPtrClosure body s.memory.callees (annealPoppedFrameState s) s.memory.fnPtrs := by dsimp only [hooks]; unfold annealStepHooksUnwindFnPtrClosureForState; rw [hact]
  have hdst_sz8 : (translateTy dstDecl.ty body.layouts).layout.size = Miri.ABI.Size.ofBytes 8 := by
    rcases hdst_thin with ⟨_, hnw_s, hnw_d⟩; unfold translateTy
    cases hmk : dstDecl.ty with | mk k idx =>
      rw [hmk] at hdst_ty hnw_s hnw_d; dsimp at hdst_ty; subst hdst_ty; simp [isWideSliceOrPointeeTy, isWideDynRawPtrTy] at hnw_s hnw_d; simp [pointerLayoutData]
  have ⟨hm_dead, hm_uninit, hm_int, hm_ptr⟩ := evalStatement_overlay_cast_fnPtr_common (callees := s.memory.callees) (poppedFrame := annealPoppedFrameState s) (fnPtrs := s.memory.fnPtrs)
    hframes hloc hbb hstmt hkind hsrc_decl hdst_decl hsrc_ty (isWideOverlayPlace_eq_false_of_decl hdst_decl hdst_thin.2.1 hdst_thin.2.2)
    hlt_mf_s hlt_mf_d (by rw [hmls_d]; exact hc_d) (Or.inl ⟨rfl, ⟨ptId, hdst_info⟩, hdst_sz8⟩)
  have ⟨hlt_d_sd, htf_sd_d⟩ := ep2CacheDstSrc_dst_getElem? topFrame (dstLay := translateTy dstDecl.ty body.layouts) (srcLay := translateTy srcDecl.ty body.layouts) hlt_mf_d hlt_mf_s hne_sd hmls_d
  let tf_sd := ep2CacheDstSrc topFrame hlt_mf_d hlt_mf_s (translateTy dstDecl.ty body.layouts) (translateTy srcDecl.ty body.layouts)
  have hloc_sd : tf_sd.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩ := by dsimp only [tf_sd]; rw [ep2CacheDstSrc_location]; exact hloc
  rw [hhooks_eq]; refine ⟨?_, ?_, ?_, ?_⟩
  · intro cSrc hslot_s hmls_s hc_s
    have ha := trusted_step_assign_rvalue_ub hphase hcal hbb hstmt hkind (by unfold evalRvalue; dsimp only; unfold evalFnPtrToPtr; rw [evalOperand_copy_nil, hslot_s])
    rw [ha, miri_step_at_statement_error _ hframes hbody hloc hbb hstmt (hm_dead cSrc hmls_s hc_s)]; exact .ub _ _
  · intro cSrc hslot_s hmls_s hc_s
    have ha := trusted_step_assign_rvalue_ub hphase hcal hbb hstmt hkind (by unfold evalRvalue; dsimp only; unfold evalFnPtrToPtr; rw [evalOperand_copy_nil, hslot_s])
    rw [ha, miri_step_at_statement_error _ hframes hbody hloc hbb hstmt (hm_uninit cSrc hmls_s hc_s)]; exact .ub _ _
  · intro sc msc cSrc hrel hsc8 hslot_s hmls_s hc_s
    have ha := trusted_step_assign_rvalue_ub hphase hcal hbb hstmt hkind (by unfold evalRvalue; dsimp only; unfold evalFnPtrToPtr; rw [evalOperand_copy_nil, hslot_s])
    rw [ha, miri_step_at_statement_error _ hframes hbody hloc hbb hstmt (hm_int sc msc cSrc hrel hsc8 hmls_s hc_s)]; exact .ub _ _
  · intro ptrVal mAllocId mTag baseAddr cSrc hslot_s haid hbase hnow1 hnow2 mptr msc hmls_s hc_s
    have ⟨hchk_off, hchk_none, hchk_some⟩ := annealCheckFnPointerOverlay_cases (fnPtrs := s.memory.fnPtrs) (st := { stack := ⟨#[tf_sd]⟩, machine := m.machine }) (mTag := mTag) haid hbase hnow1 hnow2
    have ⟨hptr_err, hptr_ok⟩ := hm_ptr mptr cSrc hmls_s hc_s; refine ⟨?_, ?_, ?_⟩
    · intro hoff_ne
      have hbeq_off : Nat.beq ptrVal.offsetBytes 0 = false := if hb : Nat.beq ptrVal.offsetBytes 0 = true then False.elim (hoff_ne (Nat.eq_of_beq_eq_true hb)) else Bool.eq_false_iff.mpr hb
      have ha := trusted_step_assign_rvalue_ub hphase hcal hbb hstmt hkind (by unfold evalRvalue; dsimp only; unfold evalFnPtrToPtr; rw [evalOperand_copy_nil, hslot_s]; simp [hbeq_off])
      rw [ha, miri_step_at_statement_error _ hframes hbody hloc hbb hstmt (hptr_err _ (hchk_off hoff_ne))]; exact .ub _ _
    · intro hoff0 hfn_ne hnone
      have ha := trusted_step_assign_rvalue_ub hphase hcal hbb hstmt hkind (by
        unfold evalRvalue; dsimp only; unfold evalFnPtrToPtr; rw [evalOperand_copy_nil, hslot_s]; dsimp only; rw [hoff0, hbor_nil]; dsimp only [Nat.beq, lookupBorrow]
        cases hfp : s.memory.fnPtrs with
        | nil => exact False.elim (hfn_ne hfp)
        | cons _ _ => dsimp only; rw [← hfp, hnone]; simp)
      rw [ha, miri_step_at_statement_error _ hframes hbody hloc hbb hstmt (hptr_err _ (hchk_none hoff0 hfn_ne hnone))]; exact .ub _ _
    · intro entry hoff0 hfn_ne hsome hnot_intr hsig_ok
      obtain ⟨tf', hm_step, hloc', hdst_m⟩ := miri_step_write_immediate_root (annealStepHooksUnwindFnPtrClosure body s.memory.callees (annealPoppedFrameState s) s.memory.fnPtrs)
        hframes hbody hloc hloc_sd hbb hstmt hlt_d_sd htf_sd_d (hptr_ok (hchk_some entry hoff0 hfn_ne hsome))
      have hrv : evalRvalue s.frame.locals (.cast .fnPtrToPtr (.copy ⟨srcIdx, .nil⟩) dstDecl.ty) s.memory body.localDecls body.layouts = .ok (.ptr ptrVal 8) s.frame.locals s.memory := by
        have hop_ty : operandTy body.localDecls body.layouts (.copy ⟨srcIdx, .nil⟩) = some srcDecl.ty := by simp [operandTy, placeTy, hsrc_decl]
        unfold evalRvalue; dsimp only; unfold evalFnPtrToPtr; rw [evalOperand_copy_nil, hslot_s]; dsimp only; rw [hdst_thin.1, hop_ty, hoff0]; dsimp only [Nat.beq]; rw [hbor_nil]; dsimp only [lookupBorrow]
        cases hfp : s.memory.fnPtrs with
        | nil => exact False.elim (hfn_ne hfp)
        | cons _ _ =>
          dsimp only; rw [← hfp, hsome]; dsimp only
          cases hmk : srcDecl.ty with | mk k _ =>
            rw [hmk] at hsrc_ty; dsimp at hsrc_ty; subst hsrc_ty
            cases hfs : entry.fnSig with
            | none => simp [hnot_intr]
            | some fs =>
              rw [hfs] at hsig_ok
              cases fs <;> first | cases hsig_ok | (dsimp at hsig_ok; simp [hnot_intr, hsig_ok])
      obtain ⟨ha_step, hblk', hstmt', hdst_a⟩ := trusted_step_assign_rvalue_ok hphase hcal hbb hstmt hkind hrv hlt_af_d hslot_d hnot_dead_d hbor_nil hprot_nil
      exact ⟨_, tf', ha_step, hblk', hstmt', hm_step, hloc', hdst_a, hdst_m, fun _ h => h⟩
section C6WitnessesAndDivergence
private def witC6IntrTy : Ty := { kind := .fnPtr .nil (.tuple .nil) .safe .rustIntrinsic, layoutIdx := 0 }
private def witC6FnTy : Ty := { kind := .fnPtr .nil (.tuple .nil) .safe .rust, layoutIdx := 0 }
private def witC6FnDefTy : Ty := { kind := .fnDef "c6_target_fn" .nil, layoutIdx := 0 }
private def witC6Callee : CapturedMir := mkEp2Body "c6_target_fn" [ep2UnitTy] []
private def witC6IntrBody : CapturedMir := mkEp2Body "wit_c6_intr_div" [ep2RawU8PtrTy, witC6IntrTy] [.assign ⟨0, .nil⟩ (.cast .fnPtrToPtr (.copy ⟨1, .nil⟩) ep2RawU8PtrTy)]
private def witC6Aid : Miri.Memory.AllocId := ⟨65536, by decide⟩
private def witC6Base : UInt64 := annealStackBaseAddr witC6Aid
private def witC6PtrSc : Miri.Memory.Scalar AnnealProv := Miri.Memory.Scalar.fromPointer annealTargetDataLayout ⟨Miri.ABI.Size.ofBytes witC6Base, .concrete witC6Aid Miri.Memory.BorTag.one⟩
private def witC6IntrAnneal0 : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit, .init (.ptr ⟨65536, 0⟩ 8)] },
    memory := { emptyMemory with
      fnPtrs := [{ allocId := 65536, defPath := "intr_fn", typeArgs := .nil, fnSig := some witC6IntrTy.kind }] } }
private def witC6IntrMiri0 : AnnealStepState := mkEp2MiriState witC6IntrBody ep2RawU8PtrTy #[⟨.live (.immediate .uninit), some (translateTy ep2RawU8PtrTy)⟩, ⟨.live (.immediate (.scalar witC6PtrSc)), some (translateTy witC6IntrTy)⟩]
    (mkEp2AddrMachine witC6Aid witC6Base)
/-- **`C6` `rust-intrinsic` ABI Divergence**: Trusted rejects `rust-intrinsic`
ABI function pointers in `FnPtrToPtr` with `.ub`, while Miri succeeds. -/
theorem fnPtrToPtr_rustIntrinsic_abi_divergence : stepMirFn witC6IntrBody witC6IntrAnneal0 = .fail .ub ∧ (Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosureForState witC6IntrBody witC6IntrAnneal0)
      () witC6IntrMiri0).2 = .ok true := ⟨rfl, rfl⟩
private def witC6RtBody : CapturedMir := mkEp2Body "wit_c6_rt" [ep2RawU8PtrTy, witC6FnTy, ep2RawUnitPtrTy] [.assign ⟨1, .nil⟩ (.cast (.pointerCoercion "ReifyFnPointer") (.constant { ty := witC6FnDefTy, val := .zeroSized }) witC6FnTy),
     .assign ⟨2, .nil⟩ (.cast .fnPtrToPtr (.copy ⟨1, .nil⟩) ep2RawUnitPtrTy), .assign ⟨0, .nil⟩ (.cast .ptrToPtr (.copy ⟨2, .nil⟩) ep2RawU8PtrTy)]
private def witC6RtS0 : MachineState := { frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit, .uninit, .uninit] }, memory := { emptyMemory with callees := [witC6Callee] } }
private def witC6RtS1 : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 1, locals := [.uninit, .init (.ptr ⟨65536, 0⟩ 8), .uninit] },
    memory :=
      { emptyMemory with
        callees := [witC6Callee], fnPtrs := [{ allocId := 65536, defPath := "c6_target_fn", typeArgs := .nil, fnSig := some witC6FnTy.kind }] } }
private def witC6RtS2 : MachineState :=
  { witC6RtS1 with
    frame := { blockIdx := 0, stmtIdx := 2, locals := [.uninit, .init (.ptr ⟨65536, 0⟩ 8), .init (.ptr ⟨65536, 0⟩ 8)] } }
private def witC6RtS3 : MachineState :=
  { witC6RtS1 with
    frame := { blockIdx := 0, stmtIdx := 3, locals := [.init (.ptr ⟨65536, 0⟩ 8), .init (.ptr ⟨65536, 0⟩ 8), .init (.ptr ⟨65536, 0⟩ 8)] } }
private def witC6RtM0 : AnnealStepState := mkEp2MiriState witC6RtBody ep2RawU8PtrTy #[⟨.live (.immediate .uninit), some (translateTy ep2RawU8PtrTy)⟩, ⟨.live (.immediate .uninit), some (translateTy witC6FnTy)⟩,
      ⟨.live (.immediate .uninit), some (translateTy ep2RawUnitPtrTy)⟩]
private def witC6RtM1 : AnnealStepState := (Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosureForState witC6RtBody witC6RtS0) () witC6RtM0).1
private def witC6RtM2 : AnnealStepState := (Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosureForState witC6RtBody witC6RtS1) () witC6RtM1).1
private def witC6RtM3 : AnnealStepState := (Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosureForState witC6RtBody witC6RtS2) () witC6RtM2).1
/-- **Concrete `C6` Witness**: 3-step `ReifyFnPointer` -> `FnPtrToPtr` ->
`PtrToPtr` round-trip checking exact provenance preservation in local `_0`
on both Trusted and Miri. -/
theorem w_c6_fnPtrToPtr_roundtrip_ub_and_divergence : stepMirFn witC6RtBody witC6RtS0 = .step witC6RtS1 ∧ stepMirFn witC6RtBody witC6RtS1 = .step witC6RtS2 ∧ stepMirFn witC6RtBody witC6RtS2 = .step witC6RtS3 ∧
    get? witC6RtS3.frame.locals 0 = some (.init (.ptr ⟨65536, 0⟩ 8)) ∧ Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosureForState witC6RtBody witC6RtS0) () witC6RtM0 = (witC6RtM1, .ok true) ∧
    Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosureForState witC6RtBody witC6RtS1) () witC6RtM1 = (witC6RtM2, .ok true) ∧ Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosureForState witC6RtBody witC6RtS2)
      () witC6RtM2 = (witC6RtM3, .ok true) ∧
    miriLocalVal? witC6RtM3 0 = some (.live (.immediate (.scalar witC6PtrSc))) :=
  ⟨rfl, rfl, rfl, rfl, step_eq_fst_of_snd rfl, step_eq_fst_of_snd rfl, step_eq_fst_of_snd rfl, rfl⟩
end C6WitnessesAndDivergence
/-! ### `C7` (`CastKind.subtype`) Correspondence -/
/-- Definitional identity between `CastKind.subtype` and `CastKind.transmute`
in Trusted `evalRvalue`. -/
theorem trusted_evalRvalue_subtype_eq_transmute (locals : List LocalSlot) (op : Operand) (targetTy : Ty) (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalRvalue locals (.cast .subtype op targetTy) mem localDecls layouts = evalRvalue locals (.cast .transmute op targetTy) mem localDecls layouts := rfl
/-- Definitional identity between `Miri.MIR.CastKind.Subtype` and `.Transmute`
in vendored `Miri.Interpreter.Cast.cast`. -/
theorem miri_cast_subtype_eq_transmute {P S C V : Type} [Miri.Memory.PointerProvenance P] (h : Miri.Interpreter.CastHooks P S C V) (choice : C) (fuel : Nat) (source : Miri.Interpreter.OpTy P) (castTy : Miri.MIR.TyId) (dest : V) :
    Miri.Interpreter.Cast.cast h choice fuel source .Subtype castTy dest = Miri.Interpreter.Cast.cast h choice fuel source .Transmute castTy dest := rfl
section C7BaseBoundary
private def witC7BaseBadBoolBody : CapturedMir := mkEp2Body "wit_c7_base_gap" [ep2BoolTy, ep2U8Ty] [.assign ⟨0, .nil⟩ (.cast .subtype (.copy ⟨1, .nil⟩) ep2BoolTy)]
private def witC7BaseBadBoolAnneal : MachineState := { frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit, .init (.scalar ⟨2, 1⟩)] }, memory := emptyMemory }
private def witC7BaseBadBoolMiri : AnnealStepState := mkEp2MiriState witC7BaseBadBoolBody ep2BoolTy #[⟨.live (.immediate .uninit), some (translateTy ep2BoolTy)⟩,
      ⟨.live (.immediate (.scalar (miriScalarUInt 2 1))), some (translateTy ep2U8Ty)⟩]
/-- **`C7` Base-Hook vs. Overlay Boundary**. -/
theorem step_cast_subtype_baseHooks_unsupported_vs_overlay_ub : (Miri.Interpreter.Step.step (annealStepHooksLM4_1 witC7BaseBadBoolBody) () witC7BaseBadBoolMiri).2 = .error (.unsupported "copyAllowTransmute in cast") ∧
    stepMirFn witC7BaseBadBoolBody witC7BaseBadBoolAnneal = .fail .ub ∧ (Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosure witC7BaseBadBoolBody) () witC7BaseBadBoolMiri).2 =
      .error (.undefinedBehavior "transmute produced invalid value for target layout") :=
  ⟨rfl, rfl, rfl⟩
end C7BaseBoundary
private theorem encodeLittleEndianBytes_len_ep2 : ∀ x n p, length (encodeLittleEndianBytes x n p) = n
  | _, 0, _ => rfl
  | x, n + 1, p => congrArg (· + 1) (encodeLittleEndianBytes_len_ep2 (Nat.div x 256) n p)
private theorem abstractBytesHaveProv_encode_none : ∀ x n, abstractBytesHaveProv (encodeLittleEndianBytes x n none) = false
  | _, 0 => rfl
  | x, n + 1 => abstractBytesHaveProv_encode_none (Nat.div x 256) n
private theorem abstractBytesAllProvAux_encode_some (a t : Nat) : ∀ k y, abstractBytesAllProvAux a t (encodeLittleEndianBytes y k (some (a, t))) = true
  | 0, _ => rfl
  | k + 1, y => by
    unfold encodeLittleEndianBytes abstractBytesAllProvAux; simp only [Nat.beq_refl, Bool.true_and]; exact abstractBytesAllProvAux_encode_some a t k (y / 256)
private theorem abstractBytesUniformProv_encode_some (a t x n : Nat) : abstractBytesUniformProv (encodeLittleEndianBytes x (n + 1) (some (a, t))) = true := abstractBytesAllProvAux_encode_some a t n (x / 256)
private theorem decodeLittleEndianBytes_encode_ep2 : ∀ w x p, decodeLittleEndianBytes (encodeLittleEndianBytes x w p) = some (x % scalarModulus w, if w == 0 then none else p)
  | 0, x, _ => by rw [scalarModulus_eq_two_pow]; exact congrArg (fun v => some (v, none)) (Nat.mod_one x).symm
  | w + 1, x, p => by
    unfold encodeLittleEndianBytes decodeLittleEndianBytes
    change (match decodeLittleEndianBytes (encodeLittleEndianBytes (x / 256) w p) with
      | some (highBits, restProv) =>
        some ((UInt8.ofNat x).toBitVec.toNat + 256 * highBits, mergeByteProvenance p restProv)
      | none => none) = _
    rw [decodeLittleEndianBytes_encode_ep2 w (x / 256) p]; have hmp : mergeByteProvenance p (if w == 0 then none else p) = p := by cases w <;> cases p <;> rfl
    dsimp only; rw [hmp]; simp only [scalarModulus_eq_two_pow, Nat.succ_ne_zero, beq_iff_eq, ↓reduceIte]; have hu8 : (UInt8.ofNat x).toBitVec.toNat = x % 256 := by simp [UInt8.ofNat]
    rw [hu8]; congr 1; congr 1; let M := 2 ^ (8 * w); have hpow : 2 ^ (8 * (w + 1)) = 256 * M := by dsimp only [M]; rw [show 8 * (w + 1) = 8 + 8 * w by omega, Nat.pow_add]
    rw [hpow]; have hb : x % 256 < 256 := Nat.mod_lt x (by decide); have hr : (x / 256) % M < M := Nat.mod_lt _ (Nat.two_pow_pos _)
    have hlt : x % 256 + 256 * ((x / 256) % M) < 256 * M := by have := Nat.mul_le_mul_left 256 (Nat.succ_le_of_lt hr); omega
    have hx : x = (x % 256 + 256 * ((x / 256) % M)) + ((x / 256) / M) * (256 * M) := by
      have h1 := (Nat.mod_add_div x 256).symm; have h2 := (Nat.mod_add_div (x / 256) M).symm; rw [h2, Nat.left_distrib, ← Nat.add_assoc] at h1
      have hmul : 256 * (M * ((x / 256) / M)) = ((x / 256) / M) * (256 * M) := by rw [Nat.mul_comm _ (256 * M), Nat.mul_assoc]
      rwa [hmul] at h1
    conv => rhs; rw [hx]
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt]
private theorem decodeLittleEndianBytes_encode_valid_ep2 {sz x : Nat} (_hv : ValidScalarBytes sz) (hx : x < scalarModulus sz) : decodeLittleEndianBytes (encodeLittleEndianBytes x sz none) = some (x, none) := by
  rw [decodeLittleEndianBytes_encode_ep2, Nat.mod_eq_of_lt hx]; split <;> rfl
private theorem resolveTyWithLocalDecls_kind_ep2 (decls : List LocalDecl) (lays : LayoutTable) (ty : Ty) : (resolveTyWithLocalDecls decls lays ty).kind = ty.kind := by
  unfold resolveTyWithLocalDecls
  cases isUnresolvedLayoutIdx lays ty.layoutIdx
  · rfl
  · cases findDeclOrContainerElemTyWithKind? decls lays ty.kind with
    | some _ => rfl
    | none =>
      cases Nat.beq ty.layoutIdx 0 <;> cases decls <;> try rfl
      cases isPrimitiveScalarKind ty.kind <;> rfl
private theorem lookup_emptyLayoutTable_ep2 (idx : Nat) : LayoutTable.lookup emptyLayoutTable idx = none := by unfold LayoutTable.lookup emptyLayoutTable; cases idx <;> rfl
private theorem tyByteSize_emptyLayoutTable_prim_ep2 (decls : List LocalDecl) (ty : Ty) (sz : Nat) (hprim : (∃ ut, ty.kind = .uint ut ∧ sz = ut.byteWidth 64) ∨ (∃ it, ty.kind = .int it ∧ sz = it.byteWidth 64) ∨
      (ty.kind = .bool ∧ sz = 1) ∨ (ty.kind = .char ∧ sz = 4)) :
    tyByteSize decls emptyLayoutTable ty = some sz := by
  unfold tyByteSize tyByteSizeAndAlignAux; dsimp only; have hk := resolveTyWithLocalDecls_kind_ep2 decls emptyLayoutTable ty
  generalize resolveTyWithLocalDecls decls emptyLayoutTable ty = rTy at hk ⊢
  rcases rTy with ⟨rk, rl⟩; dsimp only at hk; rw [hk]
  have hlk := lookup_emptyLayoutTable_ep2 rl
  rcases hprim with ⟨ut, h, hsz⟩ | ⟨it, h, hsz⟩ | ⟨h, hsz⟩ | ⟨h, hsz⟩
  · subst hsz; rw [h]; cases ut <;> simp [rigidTyByteSize, rigidTyKindByteSize, intCastTargetBytes, layoutPointerBytes, emptyLayoutTable, UintTy.byteWidth, UintTy.bitWidth, hlk]
  · subst hsz; rw [h]; cases it <;> simp [rigidTyByteSize, rigidTyKindByteSize, intCastTargetBytes, layoutPointerBytes, emptyLayoutTable, IntTy.byteWidth, IntTy.bitWidth, hlk]
  · subst hsz; rw [h]
  · subst hsz; rw [h]
private theorem prim_ty_layout_info {decls : List LocalDecl} {ty : Ty} {sz : Nat} (hprim : (∃ ut, ty = { kind := .uint ut, layoutIdx := 0 } ∧ sz = ut.byteWidth 64) ∨
      (∃ it, ty = { kind := .int it, layoutIdx := 0 } ∧ sz = it.byteWidth 64) ∨ (ty = { kind := .bool, layoutIdx := 0 } ∧ sz = 1) ∨ (ty = { kind := .char, layoutIdx := 0 } ∧ sz = 4)) :
    (translateTy ty emptyLayoutTable).layout.isSized = true ∧ (translateTy ty emptyLayoutTable).layout.size = translateSizeBytes sz ∧ (translateTy ty emptyLayoutTable).layout.size ≠ Miri.ABI.Size.ZERO ∧
    (translateTy ty emptyLayoutTable).layout.isUninhabited = false ∧ (translateTy ty emptyLayoutTable).layout.isZst = false ∧ tyByteSize decls emptyLayoutTable (resolveTyWithLocalDecls decls emptyLayoutTable ty) = some sz := by
  have hts : tyByteSize decls emptyLayoutTable (resolveTyWithLocalDecls decls emptyLayoutTable ty) = some sz := by
    apply tyByteSize_emptyLayoutTable_prim_ep2
    rw [resolveTyWithLocalDecls_kind_ep2]
    rcases hprim with ⟨ut, h, hsz⟩ | ⟨it, h, hsz⟩ | ⟨h, hsz⟩ | ⟨h, hsz⟩
    · exact Or.inl ⟨ut, by rw [h], hsz⟩
    · exact Or.inr (Or.inl ⟨it, by rw [h], hsz⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨by rw [h], hsz⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨by rw [h], hsz⟩))
  rcases hprim with ⟨ut, h, hsz⟩ | ⟨it, h, hsz⟩ | ⟨h, hsz⟩ | ⟨h, hsz⟩
  · rw [h] at hts ⊢; cases ut <;> (simp [UintTy.byteWidth] at hsz; rw [hsz] at hts ⊢; exact ⟨rfl, rfl, by decide, rfl, rfl, hts⟩)
  · rw [h] at hts ⊢; cases it <;> (simp [IntTy.byteWidth] at hsz; rw [hsz] at hts ⊢; exact ⟨rfl, rfl, by decide, rfl, rfl, hts⟩)
  · rw [h] at hts ⊢; rw [hsz] at hts ⊢; exact ⟨rfl, rfl, by decide, rfl, rfl, hts⟩
  · rw [h] at hts ⊢; rw [hsz] at hts ⊢; exact ⟨rfl, rfl, by decide, rfl, rfl, hts⟩
private theorem decodeValueFromBytes_encode_int_ep2 (layouts : LayoutTable) (ty : Ty) (sc : MirAst.ScalarInt) (hint : intCastTargetBytes ty.kind = some sc.sizeBytes)
    (hv : ValidScalarBytes sc.sizeBytes) (hx : sc.bits < scalarModulus sc.sizeBytes) :
    decodeValueFromBytes defaultCodecFuel layouts ty (encodeLittleEndianBytes sc.bits sc.sizeBytes none) = some (.scalar sc) := by
  have hlen := encodeLittleEndianBytes_len_ep2 sc.bits sc.sizeBytes none; have hnz : Nat.beq sc.sizeBytes 0 = false := by rcases hv with h | h | h | h | h <;> rw [h] <;> rfl
  have hdec := decodeLittleEndianBytes_encode_valid_ep2 hv hx; have hsc_mk : ({ bits := sc.bits, sizeBytes := sc.sizeBytes } : MirAst.ScalarInt) = sc := by cases sc; rfl
  rcases ty with ⟨dk, dl⟩
  show decodeValueFromBytes (15 + 1) layouts ⟨dk, dl⟩ _ = _
  cases dk <;> first | cases hint | (
    unfold decodeValueFromBytes; dsimp only; rw [hint, hlen]; dsimp only; rw [Nat.beq_refl]; dsimp only; unfold decodeScalarBytes; dsimp only; rw [hlen, hnz, hdec, hsc_mk])
/-- **`C7` Scalar & Invalid-Bit-Pattern UB Simulation**: covers all 14 integer
types, `bool`, and `char` across `.dead`/`.uninit` UB, invalid bit
patterns, and valid lockstep `StepRel` execution. -/
theorem step_cast_subtype_scalar_and_ub_simulation {body : CapturedMir} {s : MachineState} {m : AnnealStepState} (hstate : StateRel body s m) (hphase : ∀ p, body.phase ≠ .other p) (hlay_empty : body.layouts = emptyLayoutTable)
    {bb : BasicBlockData} {stmt : Statement} {srcIdx dstIdx : Local} {srcDecl dstDecl : LocalDecl} {sz : Nat} (hbb : get? body.basicBlocks s.frame.blockIdx = some bb) (hstmt_ok : get? bb.statements s.frame.stmtIdx = some stmt)
    (hkind : stmt.kind = .assign ⟨dstIdx, .nil⟩ (.cast .subtype (.copy ⟨srcIdx, .nil⟩) dstDecl.ty)) (hsrc_decl : get? body.localDecls srcIdx = some srcDecl) (hdst_decl : get? body.localDecls dstIdx = some dstDecl) (hsrc_prim :
      (∃ ut, srcDecl.ty = { kind := .uint ut, layoutIdx := 0 } ∧ sz = ut.byteWidth 64) ∨ (∃ it, srcDecl.ty = { kind := .int it, layoutIdx := 0 } ∧ sz = it.byteWidth 64) ∨ (srcDecl.ty = { kind := .bool, layoutIdx := 0 } ∧ sz = 1) ∨
      (srcDecl.ty = { kind := .char, layoutIdx := 0 } ∧ sz = 4))
    (hdst_prim : (∃ ut, dstDecl.ty = { kind := .uint ut, layoutIdx := 0 } ∧ sz = ut.byteWidth 64) ∨ (∃ it, dstDecl.ty = { kind := .int it, layoutIdx := 0 } ∧ sz = it.byteWidth 64) ∨
      (dstDecl.ty = { kind := .bool, layoutIdx := 0 } ∧ sz = 1) ∨ (dstDecl.ty = { kind := .char, layoutIdx := 0 } ∧ sz = 4))
    (hsrc_imm : ∀ tf, m.stack.frames = #[tf] → IsImmediateFrameLocal tf srcIdx) (hdst_imm : ∀ tf, m.stack.frames = #[tf] → IsImmediateFrameLocal tf dstIdx) :
    StepRel body m (stepMirFn body s) (Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosure body) () m) := by
  rcases hstate with ⟨topFrame, hframes, hrc, hrp, hframe, hcal, hst, hbor, hprot, hcaller, hdisj⟩
  obtain ⟨slot_s, mls_s, _, hlt_mf_s, hslot_s, hmls_s, _, hloc_s⟩ := hframe.lookup_local hsrc_decl; obtain ⟨_, mls_d, _, hlt_mf_d, _, hmls_d, hmls_eq_d, hloc_d⟩ := hframe.lookup_local hdst_decl
  have himm_s := hsrc_imm topFrame hframes mls_s hmls_s; have himm_d := hdst_imm topFrame hframes mls_d hmls_d; have hact : activeMirBody body s = body := by simp [activeMirBody, hcal]
  have ha_step_eq : stepMirFn body s = evalStmt s stmt body.localDecls body.layouts := by rw [stepMirFn_activeMirBody_eq body s (by rw [hact]; exact hphase)]; simp [hact, hbb, hstmt_ok]
  have hno_wide_d : isWideOverlayPlace body.localDecls ⟨dstIdx, #[]⟩ = false := by
    rcases hdst_prim with ⟨_, hd, _⟩ | ⟨_, hd, _⟩ | ⟨hd, _⟩ | ⟨hd, _⟩ <;>
      (apply isWideOverlayPlace_eq_false_of_decl hdst_decl <;> (rw [hd]; rfl))
  have hno_wide_s : isWideOverlayPlace body.localDecls ⟨srcIdx, #[]⟩ = false := by
    rcases hsrc_prim with ⟨_, hs, _⟩ | ⟨_, hs, _⟩ | ⟨hs, _⟩ | ⟨hs, _⟩ <;>
      (apply isWideOverlayPlace_eq_false_of_decl hsrc_decl <;> (rw [hs]; rfl))
  have hsrc_valid_sz : ValidScalarBytes sz := by
    unfold ValidScalarBytes
    rcases hsrc_prim with ⟨ut, _, hsz⟩ | ⟨it, _, hsz⟩ | ⟨_, hsz⟩ | ⟨_, hsz⟩
    · subst hsz; cases ut <;> decide
    · subst hsz; cases it <;> decide
    · subst hsz; left; rfl
    · subst hsz; right; right; left; rfl
  have ⟨hs_szd, hs_sz, hs_nz, _, _, hs_bsz⟩ := prim_ty_layout_info (decls := body.localDecls) hsrc_prim
  have ⟨hd_szd, hd_sz, _, hd_uninh, hd_zst, hd_bsz⟩ := prim_ty_layout_info (decls := body.localDecls) hdst_prim; rw [← hlay_empty] at hs_szd hs_sz hs_nz hd_szd hd_sz hd_uninh hd_zst
  have ⟨heval_dead, heval_live⟩ := evalStatement_overlay_assign_cast_copy (callees := .nil) (poppedFrame := {}) (fnPtrs := .nil) hframes hkind rfl hsrc_decl hdst_decl hno_wide_s hno_wide_d hlt_mf_s hlt_mf_d
    (by rw [hmls_eq_d]; exact hloc_d.layout_eq)
  let tf_sd := ep2CacheDstSrc topFrame hlt_mf_d hlt_mf_s (translateTy dstDecl.ty body.layouts) (translateTy srcDecl.ty body.layouts); let st_sd : AnnealStepState := { stack := ⟨#[tf_sd]⟩, machine := m.machine }
  cases hloc_s with
  | indirect _ mp _ _ _ _ => exact False.elim (himm_s mp rfl)
  | dead cSrc hc_s =>
    have ha_ub : evalStmt s stmt body.localDecls body.layouts = MirStepNode.fail .ub := by unfold evalStmt; rw [hkind]; dsimp only; unfold evalRvalue evalByteCast evalOperand; simp [hslot_s]
    rw [ha_step_eq, ha_ub, miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq hbb hstmt_ok (heval_dead cSrc hmls_s hc_s)]; exact .ub _ _
  | immediate _ immSrc cSrc hc_s hval =>
    have hcast_eq : Miri.Interpreter.Step.evalStatement (annealStepHooksUnwindFnPtrClosure body) () (translateStmt stmt) m = Miri.Interpreter.runRvalue (annealCopyAllowTransmuteOverlay
            ⟨.immediate immSrc, translateTy srcDecl.ty body.layouts⟩ ⟨.local 0 dstIdx none topFrame.localsIdentity, translateTy dstDecl.ty body.layouts⟩)
          st_sd := by
      rw [heval_live immSrc cSrc hmls_s hc_s]; have hty_id_eq : encodeTyId dstDecl.ty = (translateTy dstDecl.ty body.layouts).ty := rfl
      have hsz_eq_sd : (translateTy srcDecl.ty body.layouts).layout.size = (translateTy dstDecl.ty body.layouts).layout.size := hs_sz.trans hd_sz.symm; unfold Miri.Interpreter.runRvalue
      with_unfolding_all
        simp [annealRvalueHooksUnwindFnPtrClosure, translateCastKind, isOverlayCastKind, Miri.Interpreter.Cast.cast, annealCastHooksUnwindFnPtrClosure,
          annealCastHooksLM4_1, annealCastHooks, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, hty_id_eq, hs_szd, hd_szd, hsz_eq_sd, st_sd, tf_sd]
    rcases hval with ⟨rfl, rfl⟩ | ⟨_, rfl, himmRel⟩
    · have ha_ub : evalStmt s stmt body.localDecls body.layouts = MirStepNode.fail .ub := by
        unfold evalStmt; rw [hkind]; dsimp only; unfold evalRvalue evalByteCast evalOperand; simp [hslot_s]
      have hm_err : Miri.Interpreter.Step.evalStatement (annealStepHooksUnwindFnPtrClosure body) () (translateStmt stmt) m = (st_sd, .error (.undefinedBehavior "read of uninitialized local")) := by
        rw [hcast_eq]; unfold Miri.Interpreter.runRvalue annealCopyAllowTransmuteOverlay annealReadImmediateOverlay; simp [beq_false_of_ne hs_nz, Bind.bind, EStateM.bind, throw, throwThe, MonadExceptOf.throw, EStateM.throw]
      rw [ha_step_eq, ha_ub, miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq hbb hstmt_ok hm_err]; exact .ub _ _
    · cases himmRel with
      | unit hz => exact False.elim (hs_nz hz)
      | scalarPair _ _ _ _ _ _ hagg _ =>
          rcases hsrc_prim with ⟨_, hs, _⟩ | ⟨_, hs, _⟩ | ⟨hs, _⟩ | ⟨hs, _⟩ <;>
            (rcases hagg with ⟨_, ht⟩ | ⟨_, _, ht⟩ <;> (rw [hs] at ht; cases ht))
      | scalar sc msc hsc_rel hsz_eq hbool_src hchar_src =>
        have hsc_sz : sc.sizeBytes = sz := (validScalarBytes_size_inj hsrc_valid_sz hsc_rel.validBytes (hs_sz.symm.trans hsz_eq)).symm; subst hsc_sz; let rSrcTy := resolveTyWithLocalDecls body.localDecls emptyLayoutTable srcDecl.ty
        let rTargetTy := resolveTyWithLocalDecls body.localDecls emptyLayoutTable dstDecl.ty; let bs := encodeLittleEndianBytes sc.bits sc.sizeBytes none
        have hbs_len : length bs = sc.sizeBytes := encodeLittleEndianBytes_len_ep2 sc.bits sc.sizeBytes none; have hbs_noprov : abstractBytesHaveProv bs = false := abstractBytesHaveProv_encode_none sc.bits sc.sizeBytes
        have henc_src : encodeByteCastSourceBytes emptyLayoutTable rSrcTy (.scalar sc) = some bs := by
          have hkS : rSrcTy.kind = srcDecl.ty.kind := resolveTyWithLocalDecls_kind_ep2 _ _ _
          rcases rSrcTy with ⟨sk, sl⟩; dsimp only at hkS
          have hunion0 : isUnionLayout emptyLayoutTable ⟨sk, sl⟩ = false := by unfold isUnionLayout; rw [lookup_emptyLayoutTable_ep2]; cases sk <;> rfl
          dsimp only [bs]
          rcases hsrc_prim with ⟨ut, hs, hsz_ut⟩ | ⟨it, hs, hsz_it⟩ | ⟨hs, hsz_b⟩ | ⟨hs, hsz_c⟩
          · rw [hs] at hkS; dsimp at hkS; subst hkS
            cases ut <;> (
              simp [UintTy.byteWidth, UintTy.bitWidth] at hsz_ut
              unfold encodeByteCastSourceBytes encodeTypedValueToBytes; rw [hunion0]; unfold normalizeCodecTy encodeValueToBytes defaultCodecFuel intCastTargetBytes encodeScalarBytes; simp [hsz_ut])
          · rw [hs] at hkS; dsimp at hkS; subst hkS
            cases it <;> (
              simp [IntTy.byteWidth, IntTy.bitWidth] at hsz_it
              unfold encodeByteCastSourceBytes encodeTypedValueToBytes; rw [hunion0]; unfold normalizeCodecTy encodeValueToBytes defaultCodecFuel intCastTargetBytes encodeScalarBytes; simp [hsz_it])
          · obtain ⟨_, hb01⟩ := hbool_src (by rw [hs]); rw [hs] at hkS; dsimp at hkS; subst hkS
            unfold encodeByteCastSourceBytes encodeTypedValueToBytes; rw [hunion0]; unfold normalizeCodecTy encodeValueToBytes defaultCodecFuel encodeScalarBytes
            rcases hb01 with h | h <;> simp [hsz_b, h]
          · obtain ⟨_, hc_ok⟩ := hchar_src (by rw [hs]); rw [hs] at hkS; dsimp at hkS; subst hkS
            unfold encodeByteCastSourceBytes encodeTypedValueToBytes; rw [hunion0]; unfold normalizeCodecTy encodeValueToBytes defaultCodecFuel encodeScalarBytes; simp [hsz_c, hc_ok]
        have hmsc_bits : msc.data.toNat = sc.bits := by rw [hsc_rel.data_eq, bitVec_ofNat_toNat_of_valid hsc_rel.validBytes hsc_rel.canonical]
        have hmsc_sz : msc.size = translateSizeBytes sc.sizeBytes := hsc_rel.size_eq
        have hvr_self : ({ start := BitVec.ofNat 128 0, «end» := BitVec.ofNat 128 (scalarModulus sc.sizeBytes - 1) } : Miri.ABI.WrappingRange).contains msc.data = true := by
          unfold Miri.ABI.WrappingRange.contains; have hle_max : sc.bits ≤ scalarModulus sc.sizeBytes - 1 := by have := hsc_rel.canonical; omega
          have hmod_le := validScalarBytes_modulus_le_u128 hsc_rel.validBytes
          have hend_toNat : (BitVec.ofNat 128 (scalarModulus sc.sizeBytes - 1)).toNat = scalarModulus sc.sizeBytes - 1 := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
          simp [hmsc_bits, hend_toNat, hle_max]
        have htoSI : ((Miri.Memory.Scalar.fromScalarInt msc : Miri.Memory.Scalar AnnealProv)).toScalarInt = .ok msc := rfl
        have hcheck_agree : ∃ valid : Bool, decodeTypedValueFromBytes defaultCodecFuel emptyLayoutTable rTargetTy bs = (if valid then some (.scalar sc) else none) ∧
              annealValidateTransmutedScalar (translateTy dstDecl.ty body.layouts) (.fromScalarInt msc) = valid ∧ (valid = true → ImmediateRel dstDecl.ty body.layouts (.scalar sc) (.scalar (.fromScalarInt msc))) := by
          have hkD : rTargetTy.kind = dstDecl.ty.kind := resolveTyWithLocalDecls_kind_ep2 _ _ _; rw [hlay_empty] at hd_sz ⊢
          rcases hdst_prim with ⟨ut, hd, hsz_ut⟩ | ⟨it, hd, hsz_it⟩ | ⟨hd, hsz_b⟩ | ⟨hd, hsz_c⟩
          · refine ⟨true, ?_, ?_, fun _ => .scalar sc msc hsc_rel hd_sz (fun hb => by rw [hd] at hb; cases hb) (fun hc => by rw [hd] at hc; cases hc)⟩
            · have hint_d : intCastTargetBytes rTargetTy.kind = some sc.sizeBytes := by
                rw [hkD, hd]; cases ut <;> (simp [UintTy.byteWidth, UintTy.bitWidth, intCastTargetBytes] at hsz_ut ⊢; exact hsz_ut.symm)
              have hdec_i := decodeValueFromBytes_encode_int_ep2 emptyLayoutTable rTargetTy sc hint_d hsc_rel.validBytes hsc_rel.canonical
              rcases rTargetTy with ⟨dk, dl⟩; rw [hd] at hkD; dsimp at hkD; subst hkD
              unfold decodeTypedValueFromBytes; dsimp [defaultCodecFuel, normalizeCodecTy]; rw [hbs_noprov]; exact hdec_i
            · have hv_ty : annealValidateScalarForTyId (translateTy dstDecl.ty emptyLayoutTable).ty (.fromScalarInt msc) = true := by
                cases ut <;> (rw [hd]; rfl)
              unfold annealValidateTransmutedScalar; rw [hv_ty]; simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
              cases ut <;> (
                rw [hd] at *; simp [UintTy.byteWidth, UintTy.bitWidth] at hsz_ut
                have hvr_eq := hvr_self; rw [hsz_ut] at hvr_eq; dsimp [translateTy, UintTy.byteWidth, UintTy.bitWidth, scalarLayoutData]; rw [htoSI]; dsimp only
                rw [hmsc_sz, hsz_ut]; simpa [scalarModulus, translateSizeBytes] using hvr_eq)
          · refine ⟨true, ?_, ?_, fun _ => .scalar sc msc hsc_rel hd_sz (fun hb => by rw [hd] at hb; cases hb) (fun hc => by rw [hd] at hc; cases hc)⟩
            · have hint_d : intCastTargetBytes rTargetTy.kind = some sc.sizeBytes := by
                rw [hkD, hd]; cases it <;> (simp [IntTy.byteWidth, IntTy.bitWidth, intCastTargetBytes] at hsz_it ⊢; exact hsz_it.symm)
              have hdec_i := decodeValueFromBytes_encode_int_ep2 emptyLayoutTable rTargetTy sc hint_d hsc_rel.validBytes hsc_rel.canonical
              rcases rTargetTy with ⟨dk, dl⟩; rw [hd] at hkD; dsimp at hkD; subst hkD
              unfold decodeTypedValueFromBytes; dsimp [defaultCodecFuel, normalizeCodecTy]; rw [hbs_noprov]; exact hdec_i
            · have hv_ty : annealValidateScalarForTyId (translateTy dstDecl.ty emptyLayoutTable).ty (.fromScalarInt msc) = true := by
                cases it <;> (rw [hd]; rfl)
              unfold annealValidateTransmutedScalar; rw [hv_ty]; simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
              cases it <;> (
                rw [hd] at *; simp [IntTy.byteWidth, IntTy.bitWidth] at hsz_it
                have hvr_eq := hvr_self; rw [hsz_it] at hvr_eq; dsimp [translateTy, IntTy.byteWidth, IntTy.bitWidth, scalarLayoutData]; rw [htoSI]; dsimp only
                rw [hmsc_sz, hsz_it]; simpa [scalarModulus, translateSizeBytes] using hvr_eq)
          · refine ⟨decide (sc.bits < 2), ?_, ?_, fun hv => .scalar sc msc hsc_rel hd_sz (fun _ => ⟨hsz_b, by have := of_decide_eq_true hv; omega⟩) (fun hc => by rw [hd] at hc; cases hc)⟩
            · rcases rTargetTy with ⟨dk, dl⟩; rw [hd] at hkD; dsimp at hkD; subst hkD
              have hcanon1 : sc.bits < 256 := by have := hsc_rel.canonical; rw [hsz_b] at this; exact this
              have hu8 : (UInt8.ofNat sc.bits).toBitVec.toNat = sc.bits := by simp [UInt8.ofNat, Nat.mod_eq_of_lt hcanon1]
              unfold decodeTypedValueFromBytes; dsimp [defaultCodecFuel, normalizeCodecTy, bs]; rw [hsz_b]; dsimp [encodeLittleEndianBytes, abstractBytesHaveProv, decodeValueFromBytes]; rw [hu8]
              by_cases hb2 : sc.bits < 2
              · rcases (show sc.bits = 0 ∨ sc.bits = 1 by omega) with h0 | h1
                · simp only [h0, Nat.beq_refl]; cases sc with | mk b sB => dsimp at h0 hsz_b; subst h0 hsz_b; rfl
                · simp only [h1, Nat.beq]; cases sc with | mk b sB => dsimp at h1 hsz_b; subst h1 hsz_b; rfl
              · have hne0 : Nat.beq sc.bits 0 = false := if hb0 : Nat.beq sc.bits 0 = true then by have := Nat.eq_of_beq_eq_true hb0; omega else Bool.eq_false_iff.mpr hb0
                have hne1 : Nat.beq sc.bits 1 = false := if hb1 : Nat.beq sc.bits 1 = true then by have := Nat.eq_of_beq_eq_true hb1; omega else Bool.eq_false_iff.mpr hb1
                simp [hb2, hne0, hne1]
            · have hsz_msc : (msc.size == Miri.ABI.Size.ofBytes 1) = true := by rw [hmsc_sz, hsz_b]; rfl
              have hsz_t1 : (msc.size == translateSizeBytes 1) = true := by rw [hmsc_sz, hsz_b]; rfl
              rw [hd]; unfold annealValidateTransmutedScalar annealValidateScalarForTyId; dsimp [translateTy, encodeTyId, scalarLayoutData]; rw [htoSI]; dsimp only; simp only [hsz_msc, hsz_t1, hmsc_bits, Bool.true_and]
              by_cases hb2 : sc.bits < 2
              · rcases (show sc.bits = 0 ∨ sc.bits = 1 by omega) with h0 | h1
                · rw [show msc.data = 0 by rw [hsc_rel.data_eq, h0]; rfl, h0]; simp [Miri.ABI.WrappingRange.contains]
                · rw [show msc.data = 1 by rw [hsc_rel.data_eq, h1]; rfl, h1]; simp [Miri.ABI.WrappingRange.contains]
              · simp [hb2, beq_false_of_ne (by omega : sc.bits ≠ 0), beq_false_of_ne (by omega : sc.bits ≠ 1)]
          · refine ⟨isValidCharCode sc.bits, ?_, ?_, fun hv => .scalar sc msc hsc_rel hd_sz (fun hb => by rw [hd] at hb; cases hb) (fun _ => ⟨hsz_c, hv⟩)⟩
            · rcases rTargetTy with ⟨dk, dl⟩; rw [hd] at hkD; dsimp at hkD; subst hkD
              have hdec4 := decodeLittleEndianBytes_encode_valid_ep2 hsc_rel.validBytes hsc_rel.canonical; unfold decodeTypedValueFromBytes; dsimp [defaultCodecFuel, normalizeCodecTy]
              rw [hbs_noprov]; unfold decodeValueFromBytes; dsimp only; rw [hbs_len, hsz_c]; dsimp only [Nat.beq]; unfold decodeScalarBytes; rw [hbs_len, hsz_c]; dsimp only [Nat.beq]; rw [← hsz_c, hdec4]; dsimp only
              have hsc_mk : ({ bits := sc.bits, sizeBytes := sc.sizeBytes } : MirAst.ScalarInt) = sc := by cases sc; rfl
              rw [hsc_mk]; cases isValidCharCode sc.bits <;> rfl
            · have hsz_msc : (msc.size == Miri.ABI.Size.ofBytes 4) = true := by rw [hmsc_sz, hsz_c]; rfl
              have hsz_t4 : (msc.size == translateSizeBytes 4) = true := by rw [hmsc_sz, hsz_c]; rfl
              rw [hd]; unfold annealValidateTransmutedScalar annealValidateScalarForTyId; dsimp [translateTy, encodeTyId, scalarLayoutData]; rw [htoSI]; dsimp only; simp only [hsz_msc, hsz_t4, hmsc_bits, Bool.true_and]
              cases hvc : isValidCharCode sc.bits
              · rfl
              · unfold Miri.ABI.WrappingRange.contains; dsimp only; rw [hmsc_bits]
                have hle_max : sc.bits ≤ 1114111 := Classical.byContradiction fun hgt => by
                  unfold isValidCharCode at hvc; have h1 : Nat.ble 55296 sc.bits = true := Nat.ble_eq.mpr (by omega); have h2 : Nat.ble sc.bits 1114111 = false := Bool.eq_false_iff.mpr (fun hb => hgt (Nat.ble_eq.mp hb))
                  simp [h1, h2] at hvc
                simp [show (0#128).toNat = 0 from rfl, show (1114111#128).toNat = 1114111 from rfl, hle_max]
        obtain ⟨valid, hdec_bs, hval_m, himm_valid⟩ := hcheck_agree; have hop_ty : operandTy body.localDecls emptyLayoutTable (.copy ⟨srcIdx, .nil⟩) = some srcDecl.ty := by simp [operandTy, placeTy, hsrc_decl]
        dsimp only [rSrcTy, rTargetTy] at henc_src hdec_bs
        cases hvalid_c : valid
        · rw [hvalid_c] at hdec_bs hval_m
          have ha_ub : evalStmt s stmt body.localDecls body.layouts = MirStepNode.fail .ub := by
            unfold evalStmt; rw [hkind, hlay_empty]; dsimp only; unfold evalRvalue; dsimp only; unfold evalByteCast; rw [evalOperand_copy_nil, hslot_s]; dsimp only; rw [hd_bsz, hop_ty]; dsimp only
            rw [hs_bsz]; dsimp only; rw [Nat.beq_refl]; dsimp only; rw [henc_src]; dsimp only; rw [hbs_len, Nat.beq_refl]; dsimp only; rw [hdec_bs]; rfl
          have hm_err : Miri.Interpreter.Step.evalStatement (annealStepHooksUnwindFnPtrClosure body) () (translateStmt stmt) m = (st_sd, .error (.undefinedBehavior "transmute produced invalid value for target layout")) := by
            rw [hcast_eq]; unfold Miri.Interpreter.runRvalue annealCopyAllowTransmuteOverlay annealReadImmediateOverlay
            simp [hd_uninh, hd_zst, hval_m, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, throw, throwThe, MonadExceptOf.throw, EStateM.throw]
          rw [ha_step_eq, ha_ub, miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq hbb hstmt_ok hm_err]; exact .ub _ _
        · have himm_ok := himm_valid hvalid_c
          rw [hvalid_c] at hdec_bs hval_m; have hlt_s' : srcIdx < (cacheFrameLocalLayout topFrame dstIdx hlt_mf_d (translateTy dstDecl.ty body.layouts)).locals.size := by rw [cacheFrameLocalLayout_size]; exact hlt_mf_s
          have hfr_sd : FrameRel body m.machine { s.frame with locals := s.frame.locals } tf_sd := (hframe.cache_local_layout hdst_decl hlt_mf_d).cache_local_layout hsrc_decl hlt_s'
          have hdisj_sd : MemoryAllocDisjoint tf_sd := memoryAllocDisjoint_cacheFrameLocalLayout hlt_s' (memoryAllocDisjoint_cacheFrameLocalLayout hlt_mf_d hdisj)
          have hval_map : (tf_sd.locals[dstIdx]?).map (·.value) = (topFrame.locals[dstIdx]?).map (·.value) := by
            have hv1 : ∀ (tfx : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit) (idx : Nat) (hlt : idx < tfx.locals.size) (lay : Miri.Interpreter.LocalLayout) (k : Nat),
                ((cacheFrameLocalLayout tfx idx hlt lay).locals[k]?).map (·.value) = (tfx.locals[k]?).map (·.value) := by
              intro tfx idx hlt lay k; dsimp [cacheFrameLocalLayout]
              by_cases hik : idx = k
              · subst hik; rw [Array.getElem?_set_self hlt, getElem?_pos tfx.locals idx hlt]; rfl
              · rw [Array.getElem?_set_ne hlt hik]
            exact (hv1 _ srcIdx hlt_s' _ dstIdx).trans (hv1 topFrame dstIdx hlt_mf_d _ dstIdx)
          have himm_dst_sd : IsImmediateFrameLocal tf_sd dstIdx := by intro mls_x hx mp_x hmp_x; have hmv := hval_map; rw [hx, hmls_d] at hmv; dsimp at hmv; exact himm_d mp_x ((Option.some.inj hmv).symm.trans hmp_x)
          apply stepRel_of_writeImmediateLM2_2 (annealStepHooksUnwindFnPtrClosure body) (tf₀ := topFrame) (topFrame₁ := tf_sd) (locals₁ := s.frame.locals) (id0 := topFrame.localsIdentity)
            hphase hrc (by obtain ⟨rl, hp⟩ := hrp; exact ⟨rl, hp⟩)
            hcal hst hbor hprot hcaller hframes hframe.body_eq hframe.location_eq
            hbb hstmt_ok hfr_sd hdisj_sd hdst_decl himm_dst_sd himm_ok
          · unfold evalStmt; rw [hkind, hlay_empty]; dsimp only; unfold evalRvalue; dsimp only; unfold evalByteCast
            rw [evalOperand_copy_nil, hslot_s]; dsimp only; rw [hd_bsz, hop_ty]; dsimp only; rw [hs_bsz]; dsimp only; rw [Nat.beq_refl]; dsimp only; rw [henc_src]; dsimp only
            rw [hbs_len, Nat.beq_refl]; dsimp only; rw [hdec_bs]; simp only [↓reduceIte]
            cases get? s.frame.locals dstIdx with
            | none => rfl
            | some sl =>
              cases sl with
              | dead => rfl
              | uninit | init _ =>
                cases set? s.frame.locals dstIdx (.init (.scalar sc)) with
                | none => rfl
                | some locals₂ => rw [hprot]; dsimp only; rw [memory_inv_of_borrows_nil dstIdx hbor hprot]
          · rw [hcast_eq]; cases m; unfold Miri.Interpreter.runRvalue annealCopyAllowTransmuteOverlay annealReadImmediateOverlay; simp [hd_uninh, hd_zst, hval_m, st_sd, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]
private theorem encodeRawPtrTyId_ge (pt : RigidTy) : encodeRawPtrTyId pt = 40 ∨ 60 ≤ encodeRawPtrTyId pt := by
  cases pt with
  | int w => cases w <;> exact Or.inr (by dsimp [encodeRawPtrTyId]; decide)
  | uint w => cases w <;> exact Or.inr (by dsimp [encodeRawPtrTyId]; decide)
  | float w => cases w <;> exact Or.inr (by dsimp [encodeRawPtrTyId]; decide)
  | tuple ts => cases ts with | nil => exact Or.inr (by decide) | cons _ _ => exact Or.inl rfl
  | bool | char | never | fnDef _ _ | rawPtr _ _ | ref _ _ | fnPtr _ _ _ _ =>
      exact Or.inr (by dsimp [encodeRawPtrTyId]; decide)
  | _ => exact Or.inl rfl
private def ep2IsWidePointee : RigidTy → Bool
  | .slice _ | .str | .dynamic _ => true
  | _ => false
private theorem decodePtrBytesNoForge_thin (isRef : Bool) (pt : RigidTy) (hpt : ep2IsWidePointee pt = false) (bytes : List AbstractByte) : decodePtrBytesNoForge isRef pt 8 bytes =
      match Nat.beq (length bytes) 8, decodeScalarBytes bytes false with
      | true, .some (sv, prov) =>
        match abstractBytesUniformProv bytes, prov with
        | true, .some (allocId, _) => .some (.ptr { allocId := allocId, offsetBytes := sv.bits } 8)
        | _, _ => match isRef with | true => .none | false => .some (.scalar ⟨sv.bits, 8⟩)
      | _, _ => .none := by
  cases pt <;> first | (dsimp [ep2IsWidePointee] at hpt; cases hpt; done) | rfl
/-- **`C7` Universal Thin-Pointer `CastKind.subtype` Simulation**: covers
`.dead`/`.uninit` UB equivalence and positive lockstep pointer subtyping
across arbitrary thin raw-pointer types, preserving `PtrRel`, PC advance,
and `m'.machine = m.machine`. -/
theorem step_cast_subtype_thinPtr_simulation {body : CapturedMir} {s : MachineState} {m : AnnealStepState} {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {srcIdx dstIdx : Local} {srcDecl dstDecl : LocalDecl} {mutS mutD : Mutability} {ptS ptD : RigidTy} {bb : BasicBlockData} {stmt : Statement} (hframes : m.stack.frames = #[topFrame]) (hbody : topFrame.body = translateBody body)
    (hloc : topFrame.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩) (hphase : ∀ p, body.phase ≠ .other p) (hlay_empty : body.layouts = emptyLayoutTable) (hcal : s.memory.activeCallee = none) (hbor_nil : s.memory.borrows = .nil)
    (hprot_nil : s.memory.activeProtectors = .nil) (hbb : get? body.basicBlocks s.frame.blockIdx = some bb) (hstmt : get? bb.statements s.frame.stmtIdx = some stmt)
    (hkind : stmt.kind = .assign ⟨dstIdx, .nil⟩ (.cast .subtype (.copy ⟨srcIdx, .nil⟩) dstDecl.ty)) (hsrc_decl : get? body.localDecls srcIdx = some srcDecl) (hdst_decl : get? body.localDecls dstIdx = some dstDecl)
    (hsrc_ty : srcDecl.ty = { kind := .rawPtr mutS ptS, layoutIdx := 0 }) (hdst_ty : dstDecl.ty = { kind := .rawPtr mutD ptD, layoutIdx := 0 })
    (hsrc_thin : isWideSliceOrPointeeTy srcDecl.ty = false ∧ isWideDynRawPtrTy srcDecl.ty = false) (hdst_thin : isWideSliceOrPointeeTy dstDecl.ty = false ∧ isWideDynRawPtrTy dstDecl.ty = false)
    (hne_sd : dstIdx ≠ srcIdx) {slot_d : LocalSlot} {immDst : Miri.Interpreter.Immediate AnnealProv} {cDst : Option Miri.Interpreter.LocalLayout} (hlt_af_d : dstIdx < s.frame.locals.length)
    (hlt_mf_d : dstIdx < topFrame.locals.size) (hslot_d : get? s.frame.locals dstIdx = some slot_d) (hnot_dead_d : slot_d ≠ .dead) (hmls_d : topFrame.locals[dstIdx]'hlt_mf_d = ⟨.live (.immediate immDst), cDst⟩)
    (hc_d : ∀ l, cDst = some l → l = translateTy dstDecl.ty body.layouts) (hlt_mf_s : srcIdx < topFrame.locals.size) :
    let hooks := annealStepHooksUnwindFnPtrClosure body
    (∀ cSrc, get? s.frame.locals srcIdx = some .dead → topFrame.locals[srcIdx]'hlt_mf_s = ⟨.dead, cSrc⟩ → (∀ l, cSrc = some l → l = translateTy srcDecl.ty body.layouts) →
      StepRel body m (stepMirFn body s) (Miri.Interpreter.Step.step hooks () m)) ∧
    (∀ cSrc, get? s.frame.locals srcIdx = some .uninit → topFrame.locals[srcIdx]'hlt_mf_s = ⟨.live (.immediate .uninit), cSrc⟩ → (∀ l, cSrc = some l → l = translateTy srcDecl.ty body.layouts) →
      StepRel body m (stepMirFn body s) (Miri.Interpreter.Step.step hooks () m)) ∧
    (∀ (ptrVal : ProvenancePtr) (mptr : Miri.Memory.Pointer AnnealProv) (cSrc : Option Miri.Interpreter.LocalLayout), ptrVal.offsetBytes < scalarModulus 8 → get? s.frame.locals srcIdx = some (.init (.ptr ptrVal 8)) →
      let msc := Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr
      topFrame.locals[srcIdx]'hlt_mf_s = ⟨.live (.immediate (.scalar msc)), cSrc⟩ → (∀ l, cSrc = some l → l = translateTy srcDecl.ty body.layouts) → ∃ s' tf', stepMirFn body s = .step s' ∧ s'.frame.blockIdx = s.frame.blockIdx ∧
        s'.frame.stmtIdx = s.frame.stmtIdx + 1 ∧ Miri.Interpreter.Step.step hooks () m = ({ stack := ⟨#[tf']⟩, machine := m.machine }, .ok true) ∧ tf'.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx + 1⟩ ∧
        get? s'.frame.locals dstIdx = some (.init (.ptr ptrVal 8)) ∧ tf'.locals[dstIdx]? = some ⟨.live (.immediate (.scalar msc)), some (translateTy dstDecl.ty body.layouts)⟩ ∧
        (∀ allocMap, PtrRel allocMap ptrVal mptr → PtrRel allocMap ptrVal mptr)) := by
  intro hooks; have hptS_nw : ep2IsWidePointee ptS = false := by have ⟨h1, h2⟩ := hsrc_thin; rw [hsrc_ty] at h1 h2; cases ptS <;> first | rfl | (simp [isWideSliceOrPointeeTy, isWideDynRawPtrTy] at h1 h2)
  have hptD_nw : ep2IsWidePointee ptD = false := by have ⟨h1, h2⟩ := hdst_thin; rw [hdst_ty] at h1 h2; cases ptD <;> first | rfl | (simp [isWideSliceOrPointeeTy, isWideDynRawPtrTy] at h1 h2)
  have hsrc_lay : translateTy srcDecl.ty body.layouts = { ty := encodeRawPtrTyId ptS, layout := pointerLayoutData false } := by rw [hsrc_ty]; rfl
  have hdst_lay : translateTy dstDecl.ty body.layouts = { ty := encodeRawPtrTyId ptD, layout := pointerLayoutData false } := by rw [hdst_ty]; rfl
  have ⟨heval_dead, heval_live⟩ := evalStatement_overlay_assign_cast_copy (callees := .nil) (poppedFrame := {}) (fnPtrs := .nil) hframes hkind rfl hsrc_decl hdst_decl
    (isWideOverlayPlace_eq_false_of_decl hsrc_decl hsrc_thin.1 hsrc_thin.2) (isWideOverlayPlace_eq_false_of_decl hdst_decl hdst_thin.1 hdst_thin.2)
    hlt_mf_s hlt_mf_d (by rw [hmls_d]; exact hc_d)
  have ⟨hlt_d_sd, htf_sd_d⟩ := ep2CacheDstSrc_dst_getElem? topFrame (dstLay := translateTy dstDecl.ty body.layouts) (srcLay := translateTy srcDecl.ty body.layouts) hlt_mf_d hlt_mf_s hne_sd hmls_d
  let tf_sd := ep2CacheDstSrc topFrame hlt_mf_d hlt_mf_s (translateTy dstDecl.ty body.layouts) (translateTy srcDecl.ty body.layouts); let st_sd : AnnealStepState := { stack := ⟨#[tf_sd]⟩, machine := m.machine }
  have hloc_sd : tf_sd.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩ := by dsimp only [tf_sd]; rw [ep2CacheDstSrc_location]; exact hloc
  have hcast_eq : ∀ immS cSrc, topFrame.locals[srcIdx]'hlt_mf_s = ⟨.live (.immediate immS), cSrc⟩ → (∀ l, cSrc = some l → l = translateTy srcDecl.ty body.layouts) → Miri.Interpreter.Step.evalStatement hooks () (translateStmt stmt) m =
      Miri.Interpreter.runRvalue (annealCopyAllowTransmuteOverlay ⟨.immediate immS, translateTy srcDecl.ty body.layouts⟩ ⟨.local 0 dstIdx none topFrame.localsIdentity, translateTy dstDecl.ty body.layouts⟩) st_sd := by
    intro immS cSrc hmls_s hc_s; rw [heval_live immS cSrc (by rw [Array.getElem?_eq_getElem hlt_mf_s, hmls_s]) hc_s]; have hty_id_eq : encodeTyId dstDecl.ty = (translateTy dstDecl.ty body.layouts).ty := rfl
    have hszd_s : (translateTy srcDecl.ty body.layouts).layout.isSized = true := by rw [hsrc_lay]; rfl
    have hszd_d : (translateTy dstDecl.ty body.layouts).layout.isSized = true := by rw [hdst_lay]; rfl
    have hsz_eq : (translateTy srcDecl.ty body.layouts).layout.size = (translateTy dstDecl.ty body.layouts).layout.size := by rw [hsrc_lay, hdst_lay]
    unfold Miri.Interpreter.runRvalue
    with_unfolding_all
      simp [annealRvalueHooksUnwindFnPtrClosure, translateCastKind, isOverlayCastKind, Miri.Interpreter.Cast.cast, annealCastHooksUnwindFnPtrClosure, annealCastHooksLM4_1, annealCastHooks,
        Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, hty_id_eq, hszd_s, hszd_d, hsz_eq, st_sd]
      rfl
  refine ⟨?_, ?_, ?_⟩
  · intro cSrc hslot_s hmls_s hc_s
    have ha := trusted_step_assign_rvalue_ub hphase hcal hbb hstmt hkind (by unfold evalRvalue; dsimp only; unfold evalByteCast; rw [evalOperand_copy_nil, hslot_s])
    rw [ha, miri_step_at_statement_error _ hframes hbody hloc hbb hstmt (heval_dead cSrc (by rw [Array.getElem?_eq_getElem hlt_mf_s, hmls_s]) hc_s)]; exact .ub _ _
  · intro cSrc hslot_s hmls_s hc_s
    have ha := trusted_step_assign_rvalue_ub hphase hcal hbb hstmt hkind (by unfold evalRvalue; dsimp only; unfold evalByteCast; rw [evalOperand_copy_nil, hslot_s])
    have hnz_s : (translateTy srcDecl.ty body.layouts).layout.size ≠ Miri.ABI.Size.ZERO := by rw [hsrc_lay]; exact show (pointerLayoutData false).size ≠ Miri.ABI.Size.ZERO by decide
    have hm_err : Miri.Interpreter.Step.evalStatement hooks () (translateStmt stmt) m = (st_sd, .error (.undefinedBehavior "read of uninitialized local")) := by
      rw [hcast_eq .uninit cSrc hmls_s hc_s]; unfold Miri.Interpreter.runRvalue annealCopyAllowTransmuteOverlay annealReadImmediateOverlay
      simp [beq_false_of_ne hnz_s, Bind.bind, EStateM.bind, throw, throwThe, MonadExceptOf.throw, EStateM.throw]
    rw [ha, miri_step_at_statement_error _ hframes hbody hloc hbb hstmt hm_err]; exact .ub _ _
  · intro ptrVal mptr cSrc hoff_lt hslot_s msc hmls_s hc_s
    have hval_raw : annealValidateTransmutedScalar (translateTy dstDecl.ty body.layouts) msc = true := by
      have hge_ne : encodeRawPtrTyId ptD ≠ 1 ∧ encodeRawPtrTyId ptD ≠ 2 ∧ encodeRawPtrTyId ptD ≠ 41 ∧ encodeRawPtrTyId ptD ≠ 42 ∧ encodeRawPtrTyId ptD ≠ 50 := by
        rcases encodeRawPtrTyId_ge ptD with h | h <;> dsimp only [Miri.MIR.TyId] at h ⊢ <;> omega
      have hty_v : annealValidateScalarForTyId (encodeRawPtrTyId ptD) msc = true := by
        unfold annealValidateScalarForTyId
        split <;> first | exact False.elim (hge_ne.1 (by assumption)) |
          exact False.elim (hge_ne.2.1 (by assumption)) |
          exact False.elim (hge_ne.2.2.1 (by assumption)) |
          exact False.elim (hge_ne.2.2.2.1 (by assumption)) |
          exact False.elim (hge_ne.2.2.2.2 (by assumption)) | rfl
      rw [hdst_lay]; unfold annealValidateTransmutedScalar; dsimp only; rw [hty_v]; simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, pointerLayoutData]
      have htoP : msc.toPointer annealTargetDataLayout = .ok mptr.withOptionalProvenance := rfl; rw [htoP]; dsimp only
      simp only [beq_false_of_ne hge_ne.2.2.1, beq_false_of_ne hge_ne.2.2.2.1, Bool.or_false, Bool.false_and, Bool.not_false, Bool.true_and, Miri.ABI.WrappingRange.contains]
      have hlt64 : mptr.offset.bytes.toNat < 2 ^ 64 := mptr.offset.bytes.toBitVec.isLt; have h0 : (BitVec.ofNat 128 0).toNat = 0 := rfl; have hmax : (BitVec.ofNat 128 (2 ^ 64 - 1)).toNat = 2 ^ 64 - 1 := by decide
      simp [Miri.Memory.Pointer.withOptionalProvenance, h0, hmax]; omega
    have huninh_d : (translateTy dstDecl.ty body.layouts).layout.isUninhabited = false := by rw [hdst_lay]; rfl
    have hzst_d : (translateTy dstDecl.ty body.layouts).layout.isZst = false := by rw [hdst_lay]; rfl
    have hm_eval : Miri.Interpreter.Step.evalStatement hooks () (translateStmt stmt) m = Miri.Interpreter.runRvalue (annealWriteImmediateLM2_2 (.scalar msc)
            ⟨.local 0 dstIdx none topFrame.localsIdentity, translateTy dstDecl.ty body.layouts⟩) st_sd := by
      rw [hcast_eq (.scalar msc) cSrc hmls_s hc_s]; unfold Miri.Interpreter.runRvalue annealCopyAllowTransmuteOverlay annealReadImmediateOverlay; simp [huninh_d, hzst_d, hval_raw, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]
    obtain ⟨tf', hm_step, hloc', hdst_m⟩ := miri_step_write_immediate_root hooks hframes hbody hloc hloc_sd hbb hstmt hlt_d_sd htf_sd_d hm_eval
    have hsz8 : ∀ (rTy : Ty) (mt : Mutability) (pt : RigidTy), rTy.kind = .rawPtr mt pt → ep2IsWidePointee pt = false → tyByteSize body.localDecls emptyLayoutTable rTy = some 8 := by
      intro rTy mt pt hk hnw; unfold tyByteSize tyByteSizeAndAlignAux; dsimp only; have hk' := resolveTyWithLocalDecls_kind_ep2 body.localDecls emptyLayoutTable rTy
      generalize resolveTyWithLocalDecls body.localDecls emptyLayoutTable rTy = t at hk' ⊢
      rcases t with ⟨tk, tl⟩; dsimp only at hk'; rw [hk', hk]
      have _hlk := lookup_emptyLayoutTable_ep2 tl
      cases pt <;> first | (dsimp [ep2IsWidePointee] at hnw; cases hnw; done) | simp
    have hrv : evalRvalue s.frame.locals (.cast .subtype (.copy ⟨srcIdx, .nil⟩) dstDecl.ty) s.memory body.localDecls body.layouts = .ok (.ptr ptrVal 8) s.frame.locals s.memory := by
      rw [hlay_empty]; unfold evalRvalue; dsimp only; unfold evalByteCast; rw [evalOperand_copy_nil, hslot_s]; dsimp only
      have hop_ty : operandTy body.localDecls emptyLayoutTable (.copy ⟨srcIdx, .nil⟩) = some srcDecl.ty := by simp [operandTy, placeTy, hsrc_decl]
      have hkS := resolveTyWithLocalDecls_kind_ep2 body.localDecls emptyLayoutTable srcDecl.ty; have hkD := resolveTyWithLocalDecls_kind_ep2 body.localDecls emptyLayoutTable dstDecl.ty
      have hs8 : tyByteSize body.localDecls emptyLayoutTable (resolveTyWithLocalDecls body.localDecls emptyLayoutTable srcDecl.ty) = some 8 := hsz8 _ mutS ptS (hkS.trans (by rw [hsrc_ty])) hptS_nw
      have hd8 : tyByteSize body.localDecls emptyLayoutTable (resolveTyWithLocalDecls body.localDecls emptyLayoutTable dstDecl.ty) = some 8 := hsz8 _ mutD ptD (hkD.trans (by rw [hdst_ty])) hptD_nw
      rw [hd8, hop_ty]; dsimp only; rw [hs8]; dsimp only
      generalize resolveTyWithLocalDecls body.localDecls emptyLayoutTable srcDecl.ty = rS at hkS
      generalize resolveTyWithLocalDecls body.localDecls emptyLayoutTable dstDecl.ty = rD at hkD
      rw [hsrc_ty] at hkS; rw [hdst_ty] at hkD
      rcases rS with ⟨sk, sl⟩; rcases rD with ⟨dk, dl⟩; dsimp only at hkS hkD; subst hkS hkD
      have hunion0 : isUnionLayout emptyLayoutTable ⟨.rawPtr mutS ptS, sl⟩ = false := by unfold isUnionLayout; rw [lookup_emptyLayoutTable_ep2]
      have henc : encodeByteCastSourceBytes emptyLayoutTable ⟨.rawPtr mutS ptS, sl⟩ (.ptr ptrVal 8) = some (encodeLittleEndianBytes ptrVal.offsetBytes 8 (some (ptrVal.allocId, ptrVal.tag))) := by
        unfold encodeByteCastSourceBytes encodeTypedValueToBytes; rw [hunion0]; unfold normalizeCodecTy encodeValueToBytes defaultCodecFuel encodeScalarBytes
        cases ptS <;> first | (simp [ep2IsWidePointee] at hptS_nw; done) | rfl
      rw [henc]; dsimp only; rw [encodeLittleEndianBytes_len_ep2, Nat.beq_refl]; dsimp only; have hdec8 := decodeLittleEndianBytes_encode_ep2 8 ptrVal.offsetBytes (some (ptrVal.allocId, ptrVal.tag))
      rw [Nat.mod_eq_of_lt hoff_lt] at hdec8
      have hdecD : decodeTypedValueFromBytes defaultCodecFuel emptyLayoutTable ⟨.rawPtr mutD ptD, dl⟩ (encodeLittleEndianBytes ptrVal.offsetBytes 8 (some (ptrVal.allocId, ptrVal.tag))) = some (.ptr ptrVal 8) := by
        have hlen8 := encodeLittleEndianBytes_len_ep2 ptrVal.offsetBytes 8 (some (ptrVal.allocId, ptrVal.tag))
        have hptr_mk : ({ allocId := ptrVal.allocId, offsetBytes := ptrVal.offsetBytes } : ProvenancePtr) = ptrVal := by cases ptrVal; rfl
        have hlpb : layoutPointerBytes emptyLayoutTable = 8 := rfl; have hunif := abstractBytesUniformProv_encode_some ptrVal.allocId ptrVal.tag ptrVal.offsetBytes 7
        unfold decodeTypedValueFromBytes; dsimp only [defaultCodecFuel, normalizeCodecTy]; rw [hlpb, decodePtrBytesNoForge_thin false ptD hptD_nw, hlen8, Nat.beq_refl]; dsimp only; unfold decodeScalarBytes; rw [hlen8, hdec8]
        simp only [show (8 == 0) = false from rfl, Bool.false_eq_true, ↓reduceIte]; rw [hunif]
      rw [hdecD]
    obtain ⟨ha_step, hblk', hstmt', hdst_a⟩ := trusted_step_assign_rvalue_ok hphase hcal hbb hstmt hkind hrv hlt_af_d hslot_d hnot_dead_d hbor_nil hprot_nil
    exact ⟨_, tf', ha_step, hblk', hstmt', hm_step, hloc', hdst_a, hdst_m, fun _ h => h⟩
section C7Witnesses
private def nonZeroByteTypeLayout : TypeLayout :=
  { size := { bytes := 1 }, align := { bytes := 1 },
    backendRepr := .scalar (.initialized (.int 8 false) { start := 1, end_ := 255 }), variants := .single 0, fields := .arbitrary [{ bytes := 0 }] [0], fieldLayouts := [], isUninhabited := false }
private def u8PrimTypeLayout : TypeLayout :=
  { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := .scalar (.initialized (.int 8 false) { start := 0, end_ := 255 }), variants := .single 0, fields := .primitive, fieldLayouts := [], isUninhabited := false }
private def c7NzLayouts : LayoutTable := { emptyLayoutTable with entries := [nonZeroByteTypeLayout, u8PrimTypeLayout] }
private def c7NzTy : Ty := { kind := .adt "crate::NonZeroByte" .nil, layoutIdx := 0 }
private def c7U8IdxTy : Ty := { kind := .uint .u8, layoutIdx := 1 }
private def mkC7ScalarCase (srcT dstT : Ty) (lays : LayoutTable) (bits sz : Nat) (mszBytes : UInt64) : CapturedMir × MachineState × AnnealStepState :=
  let b := mkEp2Body "wit_c7" [dstT, srcT] [.assign ⟨0, .nil⟩ (.cast .subtype (.copy ⟨1, .nil⟩) dstT)] lays
  let s : MachineState := { frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit, .init (.scalar ⟨bits, sz⟩)] }, memory := emptyMemory }
  let m := mkEp2MiriState b dstT #[⟨.live (.immediate .uninit), some (translateTy dstT lays)⟩, ⟨.live (.immediate (.scalar (miriScalarUInt bits mszBytes))), some (translateTy srcT lays)⟩]
  (b, s, m)
private def witC7PtrBody : CapturedMir := mkEp2Body "wit_c7_ptr" [ep2RawU8PtrTy, ep2RawMutU8PtrTy] [.assign ⟨0, .nil⟩ (.cast .subtype (.copy ⟨1, .nil⟩) ep2RawU8PtrTy)]
private def witC7PtrAnneal : MachineState := { frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit, .init (.ptr ⟨65536, 4⟩ 8)] }, memory := emptyMemory }
private def witC7PtrSc : Miri.Memory.Scalar AnnealProv := Miri.Memory.Scalar.fromPointer annealTargetDataLayout ⟨Miri.ABI.Size.ofBytes (witC6Base + 4), .concrete witC6Aid Miri.Memory.BorTag.one⟩
private def witC7PtrMiri : AnnealStepState := mkEp2MiriState witC7PtrBody ep2RawU8PtrTy #[⟨.live (.immediate .uninit), some (translateTy ep2RawU8PtrTy)⟩, ⟨.live (.immediate (.scalar witC7PtrSc)), some (translateTy ep2RawMutU8PtrTy)⟩]
    (mkEp2AddrMachine witC6Aid witC6Base)
/-- **Concrete `C7` Witness**: verifies both Trusted and Miri written `_0`
values for `bool` (`1`), thin provenance pointer (`witC6Aid + 4`), and
`NonZeroByte` (`42`), plus lockstep UB on invalid `bool` (`2`), null
`&u32`, and `NonZeroByte` (`0`). -/
theorem w_c7_subtype_scalars_ptrs_newtype_and_ub :
    let (bValidBool, sValidBool, mValidBool) := mkC7ScalarCase ep2U8Ty ep2BoolTy emptyLayoutTable 1 1 1; let (bBadBool, sBadBool, mBadBool) := mkC7ScalarCase ep2U8Ty ep2BoolTy emptyLayoutTable 2 1 1
    let (bNullRef, sNullRef, mNullRef) := mkC7ScalarCase ep2UsizeTy ep2RefU32Ty emptyLayoutTable 0 8 8; let (bNzOk, sNzOk, mNzOk) := mkC7ScalarCase c7U8IdxTy c7NzTy c7NzLayouts 42 1 1
    let (bNzUb, sNzUb, mNzUb) := mkC7ScalarCase c7U8IdxTy c7NzTy c7NzLayouts 0 1 1; let rBool := Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosure bValidBool) () mValidBool
    let rPtr := Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosure witC7PtrBody) () witC7PtrMiri; let rNz := Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosure bNzOk) () mNzOk
    (∃ s', stepMirFn bValidBool sValidBool = .step s' ∧ get? s'.frame.locals 0 = some (.init (.scalar ⟨1, 1⟩))) ∧ rBool.2 = .ok true ∧ miriLocalVal? rBool.1 0 = some (.live (.immediate (.scalar (miriScalarUInt 1 1)))) ∧
    stepMirFn bBadBool sBadBool = .fail .ub ∧ (∃ msg, (Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosure bBadBool) () mBadBool).2 = .error (.undefinedBehavior msg)) ∧
    (∃ s', stepMirFn witC7PtrBody witC7PtrAnneal = .step s' ∧ get? s'.frame.locals 0 = some (.init (.ptr ⟨65536, 4⟩ 8))) ∧ rPtr.2 = .ok true ∧ miriLocalVal? rPtr.1 0 = some (.live (.immediate (.scalar witC7PtrSc))) ∧
    stepMirFn bNullRef sNullRef = .fail .ub ∧ (∃ msg, (Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosure bNullRef) () mNullRef).2 = .error (.undefinedBehavior msg)) ∧
    (∃ s', stepMirFn bNzOk sNzOk = .step s' ∧ get? s'.frame.locals 0 = some (.init (.aggregate 0 [.scalar ⟨42, 1⟩]))) ∧ rNz.2 = .ok true ∧ miriLocalVal? rNz.1 0 = some (.live (.immediate (.scalar (miriScalarUInt 42 1)))) ∧
    stepMirFn bNzUb sNzUb = .fail .ub ∧ (∃ msg, (Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosure bNzUb) () mNzUb).2 = .error (.undefinedBehavior msg)) :=
  ⟨⟨_, rfl, rfl⟩, rfl, rfl, rfl, ⟨_, rfl⟩, ⟨_, rfl, rfl⟩, rfl, rfl, rfl, ⟨_, rfl⟩, ⟨_, rfl, rfl⟩, rfl, rfl, rfl, ⟨_, rfl⟩⟩
end C7Witnesses

/-! ## Section 6. `C8` (Non-`Unsize` `CastKind.pointerCoercion` Variants) -/
private theorem step_overlay_eq_base_at_stmtFree {currentBody : CapturedMir} {callees : List CapturedMir} {poppedFrame : Miri.TreeBorrows.FrameState} {fnPtrs : List FnPtrEntry} {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit} {loc : Miri.MIR.Location} {bb : Miri.MIR.BasicBlock} {stmt : Miri.MIR.Statement}
    (hback : m.stack.frames.back? = some topFrame) (hloc : topFrame.location = .mir loc) (hbb : topFrame.body.basicBlocks[loc.block]? = some bb) (hstmt : bb.statements[loc.statementIndex]? = some stmt)
    (hfree : stmtFreeOfUnwindFnPtrClosureOverlay currentBody.localDecls stmt) :
    Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosure currentBody callees poppedFrame fnPtrs) () m = Miri.Interpreter.Step.step (annealStepHooksLM4_1 currentBody callees poppedFrame fnPtrs) () m := by
  unfold Miri.Interpreter.Step.step Miri.Interpreter.Stack.currentFrame?; rw [hback]; dsimp only [Id.run]; rw [hloc]; dsimp only; rw [hbb]; dsimp only; rw [hstmt]; dsimp only; rw [evalStatement_overlay_eq_base_of_stmtFree hfree]
/-- **`C8.1` Coercion-Tag Classification**. -/
theorem reifyFnPointer_coercion_tags_accepted : isReifyFnPointerCoercion "ReifyFnPointer" = true ∧ isReifyFnPointerCoercion "ReifyFnPointer(Safe)" = true ∧ isReifyFnPointerCoercion "ReifyFnPointer(Unsafe)" = true ∧
    translatePointerCoercion "ReifyFnPointer" = .ReifyFnPointer .Safe ∧ translatePointerCoercion "ReifyFnPointer(Safe)" = .ReifyFnPointer .Safe ∧ translatePointerCoercion "ReifyFnPointer(Unsafe)" = .ReifyFnPointer .Unsafe :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
/-- **`C8.1` Multi-Frame `ReifyFnPointer` Simulation Bridge**: holds directly
for the overlay `annealStepHooksUnwindFnPtrClosureForState` because
`ReifyFnPointer` passes conservatively to `annealStepHooksLM4_1`. -/
theorem c8_1_reifyFnPointer_simulation_bridge {rootBody : CapturedMir} {s : MachineState} {m : AnnealStepState} (hstate : MultiFrameStateRel rootBody s m) (hphase : ∀ p, (activeMirBody rootBody s).phase ≠ .other p)
    {bb : BasicBlockData} {fnIdx : Local} {fnDecl : LocalDecl} {defPath : DefPath} {span : String} {callerInputs : List RigidTy} {callerOut : RigidTy} {callerAbi : CallConv}
    {allocId : Nat} {mAllocId : Miri.Memory.AllocId} {baseAddr : UInt64} (hbb : get? (activeMirBody rootBody s).basicBlocks s.frame.blockIdx = some bb) (hstmt : get? bb.statements s.frame.stmtIdx = some
      { kind := .assign ⟨fnIdx, .nil⟩ (.cast (.pointerCoercion "ReifyFnPointer") (.constant { ty := { kind := .fnDef defPath .nil, layoutIdx := 0 }, val := .zeroSized }) fnDecl.ty), span := span })
    (hfn_decl : get? (activeMirBody rootBody s).localDecls fnIdx = some fnDecl) (hfn_ty : fnDecl.ty.kind = .fnPtr callerInputs callerOut .safe callerAbi) (hnot_intr : callConvEq callerAbi .rustIntrinsic = false)
    (hcheck_sig : checkCalleeSig s.memory.callees defPath callerInputs callerOut callerAbi .nil .nil = true) (htraits_nil : s.memory.traitImpls = .nil) (hbor_nil : s.memory.borrows = .nil)
    (hfn_imm : ∀ tf, m.stack.frames.back? = some tf → IsImmediateFrameLocal tf fnIdx) (hfn_live : get? s.frame.locals fnIdx ≠ some .dead) (hfind_none : findFnPtrEntry? s.memory.fnPtrs defPath .nil (some fnDecl.ty.kind) = none)
    (halloc_id : nextFnPtrAllocId s.memory.fnPtrs = allocId) (hmAlloc_eq : mAllocId.value.toNat = allocId) (hbase_lookup : m.machine.lookupBaseAddr mAllocId = some baseAddr) :
    ∃ s₁ m₁ topFrame₁ restMfs, stepMirFn rootBody s = .step s₁ ∧ Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosureForState rootBody s) () m = (m₁, .ok true) ∧
      IndirectFnPtrMovePre rootBody s₁ m₁ topFrame₁ restMfs fnIdx fnDecl { allocId := allocId, offsetBytes := 0 } mAllocId Miri.Memory.BorTag.one baseAddr := by
  have heq_ov : Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosureForState rootBody s) () m = Miri.Interpreter.Step.step (annealStepHooksForState rootBody s) () m := by
    rcases hstate with ⟨topFrame, hback, _, _, _, hlinks, _, _, _, _, _, _, _, _⟩
    have hforall := hlinks.toForall2
    rcases hmfs : m.stack.frames.toList.reverse with _ | ⟨tf₀, _⟩
    · rw [hmfs] at hforall; cases hforall
    · rw [hmfs] at hforall
      cases hforall with
      | cons hframe _ =>
          have hback₀ : m.stack.frames.back? = some tf₀ := by rw [array_eq_of_toList_reverse_cons hmfs]; simp
          have htf : topFrame = tf₀ := Option.some.inj (hback.symm.trans hback₀); subst htf
          exact step_overlay_eq_base_at_stmtFree hback hframe.location_eq (by rw [hframe.body_eq, translateBody_basicBlocks_getElem?, hbb]; rfl) (by rw [translateBasicBlockData_statements_getElem?, hstmt]; rfl)
            (by simp [stmtFreeOfUnwindFnPtrClosureOverlay, isUnwindFnPtrClosureAssign, hasRealUnwrapUnsafeBinder, rvalueUsesPlaceOrClosureOverlay, operandHasRealUnwrapUnsafeBinder, isProjectedClosureOperand, isOverlayCastKind,
                  translateStmt, translateStmtKind, translateRvalue, translateCastKind, translatePointerCoercion, translateOperand, translatePlace])
  obtain ⟨s₁, m₁, tf₁, restMfs, ha, hm, _, _, _, _, _, _, hpre⟩ := step_stmt_assign_reifyFnPointer_to_indirectFnPtrMovePre_simulation hstate hphase hbb hstmt hfn_decl hfn_ty hnot_intr hcheck_sig htraits_nil hbor_nil
      hfn_imm hfn_live hfind_none halloc_id hmAlloc_eq hbase_lookup
  exact ⟨s₁, m₁, tf₁, restMfs, ha, heq_ov.trans hm, hpre⟩
/-- **`C8.2` Universal `ClosureFnPointer` Simulation**: covers `.dead` source
UB equivalence, 0-capture ZST closure lockstep interning (`PtrRel` + PC
advance), and capturing-closure rejection (Trusted `.ub` vs. Miri
`.invalidProgram "capturing closure in pointer cast"`). -/
theorem step_cast_closureFnPointer_simulation {body : CapturedMir} {s : MachineState} {m : AnnealStepState} {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {srcIdx dstIdx : Local} {srcDecl dstDecl : LocalDecl} {defPath : DefPath} {upvars : List RigidTy} {fnInputs : List RigidTy} {fnOutput : RigidTy} {fnSafety : Safety} {fnAbi : CallConv} {coercionTag : String}
    {bb : BasicBlockData} {stmt : Statement} (hframes : m.stack.frames = #[topFrame]) (hbody : topFrame.body = translateBody body) (hloc : topFrame.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩)
    (hphase : ∀ p, body.phase ≠ .other p) (hcal : s.memory.activeCallee = none) (hbor_nil : s.memory.borrows = .nil) (hprot_nil : s.memory.activeProtectors = .nil) (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some stmt) (htag : coercionTag = "ClosureFnPointer(Safe)" ∨ coercionTag = "ClosureFnPointer(Unsafe)") (hkind : stmt.kind = .assign ⟨dstIdx, .nil⟩
      (.cast (.pointerCoercion coercionTag) (.copy ⟨srcIdx, .nil⟩) dstDecl.ty))
    (hsrc_decl : get? body.localDecls srcIdx = some srcDecl) (hdst_decl : get? body.localDecls dstIdx = some dstDecl) (hsrc_ty : srcDecl.ty.kind = .closure defPath upvars)
    (hdst_ty : dstDecl.ty.kind = .fnPtr fnInputs fnOutput fnSafety fnAbi) (hne_sd : dstIdx ≠ srcIdx) {slot_d : LocalSlot} {immDst : Miri.Interpreter.Immediate AnnealProv}
    {cDst : Option Miri.Interpreter.LocalLayout} (hlt_af_d : dstIdx < s.frame.locals.length) (hlt_mf_d : dstIdx < topFrame.locals.size) (hslot_d : get? s.frame.locals dstIdx = some slot_d)
    (hnot_dead_d : slot_d ≠ .dead) (hmls_d : topFrame.locals[dstIdx]'hlt_mf_d = ⟨.live (.immediate immDst), cDst⟩) (hc_d : ∀ l, cDst = some l → l = translateTy dstDecl.ty body.layouts) (hlt_mf_s : srcIdx < topFrame.locals.size) :
    let hooks := annealStepHooksUnwindFnPtrClosureForState body s
    (∀ cSrc, get? s.frame.locals srcIdx = some .dead → topFrame.locals[srcIdx]'hlt_mf_s = ⟨.dead, cSrc⟩ → (∀ l, cSrc = some l → l = translateTy srcDecl.ty body.layouts) →
      StepRel body m (stepMirFn body s) (Miri.Interpreter.Step.step hooks () m)) ∧
    (∀ u0 urest vals cSrc immSrc, upvars = u0 :: urest → get? s.frame.locals srcIdx = some (.init (.aggregate 0 vals)) → topFrame.locals[srcIdx]'hlt_mf_s = ⟨.live (.immediate immSrc), cSrc⟩ →
      (∀ l, cSrc = some l → l = translateTy srcDecl.ty body.layouts) → stepMirFn body s = .fail .ub ∧ (Miri.Interpreter.Step.step hooks () m).2 = .error (.invalidProgram "capturing closure in pointer cast")) ∧
    (∀ (allocId : Nat) (mAllocId : Miri.Memory.AllocId) (baseAddr : UInt64) (cSrc : Option Miri.Interpreter.LocalLayout) (immSrc : Miri.Interpreter.Immediate AnnealProv), upvars = .nil →
      get? s.frame.locals srcIdx = some (.init (.aggregate 0 .nil)) → topFrame.locals[srcIdx]'hlt_mf_s = ⟨.live (.immediate immSrc), cSrc⟩ → (∀ l, cSrc = some l → l = translateTy srcDecl.ty body.layouts) →
      callConvEq fnAbi .rustIntrinsic = false → reifyCoercionSafetyCompatible coercionTag fnSafety = true → checkCalleeSig s.memory.callees defPath fnInputs fnOutput fnAbi .nil s.memory.traitImpls = true →
      (match findFnPtrEntry? s.memory.fnPtrs defPath .nil (some dstDecl.ty.kind) with
       | some e => e.allocId | none => nextFnPtrAllocId s.memory.fnPtrs) = allocId →
      mAllocId.value.toNat = allocId → m.machine.lookupBaseAddr mAllocId = some baseAddr →
      let mptr : Miri.Memory.Pointer AnnealProv := ⟨Miri.ABI.Size.ofBytes baseAddr, .concrete mAllocId Miri.Memory.BorTag.one⟩; let msc := Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr
      ∃ s' tf', stepMirFn body s = .step s' ∧ s'.frame.blockIdx = s.frame.blockIdx ∧ s'.frame.stmtIdx = s.frame.stmtIdx + 1 ∧ Miri.Interpreter.Step.step hooks () m = ({ stack := ⟨#[tf']⟩, machine := m.machine }, .ok true) ∧
        tf'.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx + 1⟩ ∧ get? s'.frame.locals dstIdx = some (.init (.ptr ⟨allocId, 0⟩ 8)) ∧ tf'.locals[dstIdx]? =
          some ⟨.live (.immediate (.scalar msc)), some (translateTy dstDecl.ty body.layouts)⟩ ∧
        (∀ allocMap, PtrRel allocMap ⟨allocId, 0⟩ mptr → PtrRel allocMap ⟨allocId, 0⟩ mptr)) := by
  intro hooks; have hact : activeMirBody body s = body := by simp [activeMirBody, hcal]
  have hov_ck : isOverlayCastKind (translateCastKind (.pointerCoercion coercionTag)) = true := by rcases htag with rfl | rfl <;> rfl
  have hno_wide_s : isWideOverlayPlace body.localDecls ⟨srcIdx, #[]⟩ = false := by
    apply isWideOverlayPlace_eq_false_of_decl hsrc_decl <;> (cases hmk : srcDecl.ty with | mk k _ => rw [hmk] at hsrc_ty; dsimp at hsrc_ty; subst hsrc_ty; rfl)
  have hno_wide_d : isWideOverlayPlace body.localDecls ⟨dstIdx, #[]⟩ = false := by
    apply isWideOverlayPlace_eq_false_of_decl hdst_decl <;> (cases hmk : dstDecl.ty with | mk k _ => rw [hmk] at hdst_ty; dsimp at hdst_ty; subst hdst_ty; rfl)
  let tf_sd := ep2CacheDstSrc topFrame hlt_mf_d hlt_mf_s (translateTy dstDecl.ty body.layouts) (translateTy srcDecl.ty body.layouts); let st_sd : AnnealStepState := { stack := ⟨#[tf_sd]⟩, machine := m.machine }
  have hloc_sd : tf_sd.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩ := by dsimp only [tf_sd]; rw [ep2CacheDstSrc_location]; exact hloc
  have ⟨heval_dead, heval_live⟩ := evalStatement_overlay_assign_cast_copy (callees := s.memory.callees) (poppedFrame := annealPoppedFrameState s) (fnPtrs := s.memory.fnPtrs)
    hframes hkind hov_ck hsrc_decl hdst_decl hno_wide_s hno_wide_d hlt_mf_s hlt_mf_d (by rw [hmls_d]; exact hc_d)
  have hop_ty : operandTy body.localDecls body.layouts (.copy ⟨srcIdx, .nil⟩) = some srcDecl.ty := by simp [operandTy, placeTy, hsrc_decl]
  have hinfo_clos : castTypeInfoOverlay body { stack := ⟨#[tf_sd]⟩, machine := m.machine } (translateTy srcDecl.ty body.layouts).ty = .ok (.closure 0 #[] upvars.length) := by
    have hty_s : (translateTy srcDecl.ty body.layouts).ty = encodeTyId srcDecl.ty := rfl; rw [hty_s]; unfold castTypeInfoOverlay activeClosureCastTypeInfo?; rw [stack_currentFrame?_singleton ⟨#[tf_sd]⟩ tf_sd rfl]; dsimp only
    rw [hloc_sd]; dsimp only; rw [hbb]; dsimp only; rw [hstmt]
    rcases stmt with ⟨fk, sp⟩; dsimp only at hkind; subst hkind; dsimp only; rw [hop_ty]; dsimp only
    cases hmk : srcDecl.ty with | mk k _ => rw [hmk] at hsrc_ty; dsimp at hsrc_ty; subst hsrc_ty; simp
  have hisReify : isReifyFnPointerCoercion coercionTag = true := by rcases htag with rfl | rfl <;> rfl
  have hne_ufp : stringEq coercionTag "UnsafeFnPointer" = false := by rcases htag with rfl | rfl <;> rfl
  have hty_id_eq : encodeTyId dstDecl.ty = (translateTy dstDecl.ty body.layouts).ty := rfl
  have ⟨hlt_d_sd, htf_sd_d⟩ := ep2CacheDstSrc_dst_getElem? topFrame (dstLay := translateTy dstDecl.ty body.layouts) (srcLay := translateTy srcDecl.ty body.layouts) hlt_mf_d hlt_mf_s hne_sd hmls_d; refine ⟨?_, ?_, ?_⟩
  · intro cSrc hslot_s hmls_s hc_s
    have hmls_s? : topFrame.locals[srcIdx]? = some ⟨.dead, cSrc⟩ := by rw [Array.getElem?_eq_getElem hlt_mf_s, hmls_s]
    have hm_err : Miri.Interpreter.Step.evalStatement hooks () (translateStmt stmt) m = (st_sd, .error (.undefinedBehavior "read of dead local")) := by
      dsimp only [hooks]; unfold annealStepHooksUnwindFnPtrClosureForState; rw [hact]; exact heval_dead cSrc hmls_s? hc_s
    have ha_ub := trusted_step_assign_rvalue_ub hphase hcal hbb hstmt hkind (by unfold evalRvalue; dsimp only; unfold evalReifyFnPointer; rw [hisReify]; dsimp only; rw [hne_ufp]; dsimp only; rw [evalOperand_copy_nil, hslot_s])
    rw [ha_ub, miri_step_at_statement_error _ hframes hbody hloc hbb hstmt hm_err]; exact .ub _ _
  · intro u0 urest vals cSrc immSrc hup hslot_s hmls_s hc_s
    have ha_ub := trusted_step_assign_rvalue_ub hphase hcal hbb hstmt hkind (by
      unfold evalRvalue; dsimp only; unfold evalReifyFnPointer; rw [hisReify]; dsimp only; rw [hne_ufp]; dsimp only; rw [evalOperand_copy_nil, hslot_s]; dsimp only
      cases vals with
      | cons _ _ => rfl
      | nil =>
        rw [hdst_ty]; dsimp only
        cases Bool.and (Bool.not (callConvEq fnAbi .rustIntrinsic)) (reifyCoercionSafetyCompatible coercionTag fnSafety)
        · rfl
        · dsimp only; rw [hop_ty]
          have hnone : extractReifyCoercionTarget? coercionTag (some srcDecl.ty) = none := by
            cases hmk : srcDecl.ty with | mk sk sl =>
            rw [hmk] at hsrc_ty; dsimp at hsrc_ty; subst hsrc_ty; subst hup
            rcases htag with rfl | rfl <;> rfl
          rw [hnone]; rfl)
    have hmls_s? : topFrame.locals[srcIdx]? = some ⟨.live (.immediate immSrc), cSrc⟩ := by rw [Array.getElem?_eq_getElem hlt_mf_s, hmls_s]
    have hlen_nz : (upvars.length != 0) = true := by rw [hup]; rfl
    have hinfo_clos' : castTypeInfoOverlay body { stack := ⟨#[ep2CacheDstSrc topFrame hlt_mf_d hlt_mf_s (translateTy dstDecl.ty body.layouts) (translateTy srcDecl.ty body.layouts)]⟩, machine := m.machine }
        (translateTy srcDecl.ty body.layouts).ty = .ok (.closure 0 #[] upvars.length) := hinfo_clos
    have hm_err : Miri.Interpreter.Step.evalStatement hooks () (translateStmt stmt) m = (st_sd, .error (.invalidProgram "capturing closure in pointer cast")) := by
      dsimp only [hooks]; unfold annealStepHooksUnwindFnPtrClosureForState; rw [hact]; rw [heval_live immSrc cSrc hmls_s? hc_s]
      rcases htag with rfl | rfl <;> (
        unfold Miri.Interpreter.runRvalue annealRvalueHooksUnwindFnPtrClosure; dsimp only [translateCastKind, translatePointerCoercion, isOverlayCastKind, ↓reduceIte, st_sd]
        unfold Miri.Interpreter.Cast.cast annealCastHooksUnwindFnPtrClosure annealCastHooksLM4_1 annealCastHooks
        simp only [Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, get, getThe, MonadStateOf.get, EStateM.get, hty_id_eq, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte, hinfo_clos', hlen_nz]; rfl)
    exact ⟨ha_ub, by rw [miri_step_at_statement_error _ hframes hbody hloc hbb hstmt hm_err]⟩
  · intro allocId mAllocId baseAddr cSrc immSrc hup hslot_s hmls_s hc_s hnot_intr hsaf_ok hsig_ok haid_eq hmaid hbase mptr msc
    have hmls_s? : topFrame.locals[srcIdx]? = some ⟨.live (.immediate immSrc), cSrc⟩ := by rw [Array.getElem?_eq_getElem hlt_mf_s, hmls_s]
    have halloc_fn : annealReifyOrClosureFnPointerAlloc body s.memory.fnPtrs { stack := ⟨#[tf_sd]⟩, machine := m.machine } = .ok mptr.withOptionalProvenance { stack := ⟨#[tf_sd]⟩, machine := m.machine } := by
      unfold annealReifyOrClosureFnPointerAlloc; rw [stack_currentFrame?_singleton ⟨#[tf_sd]⟩ tf_sd rfl]; dsimp only; rw [hloc_sd]; dsimp only; rw [hbb]; dsimp only; rw [hstmt]
      rcases stmt with ⟨fk, sp⟩; dsimp only at hkind; subst hkind; dsimp only; rw [hop_ty]
      have hextr : extractOverlayCoercionTarget? coercionTag (some srcDecl.ty) = some (defPath, .nil) := by
        cases hmk : srcDecl.ty with | mk sk sl =>
        rw [hmk] at hsrc_ty; dsimp at hsrc_ty; subst hsrc_ty; subst hup
        rcases htag with rfl | rfl <;> rfl
      rw [hextr]; dsimp only; rw [haid_eq]; have hne0 : UInt64.ofNat allocId ≠ 0 := by rw [← hmaid, UInt64.ofNat_toNat]; exact mAllocId.nonzero
      have hmk_aid : (⟨UInt64.ofNat allocId, hne0⟩ : Miri.Memory.AllocId) = mAllocId := by cases mAllocId with | mk v hnz => dsimp at hmaid; subst hmaid; simp [UInt64.ofNat_toNat]
      rw [dite_eq_left_of_eq_true (eq_true hne0), hmk_aid, hbase]; dsimp only [mptr, Miri.Memory.Pointer.withOptionalProvenance]; rw [show UInt64.ofNat 0 = (0 : UInt64) from rfl, UInt64.add_zero]
    have hlen_z : (upvars.length != 0) = false := by rw [hup]; rfl
    have hinfo_clos' : castTypeInfoOverlay body { stack := ⟨#[ep2CacheDstSrc topFrame hlt_mf_d hlt_mf_s (translateTy dstDecl.ty body.layouts) (translateTy srcDecl.ty body.layouts)]⟩, machine := m.machine }
        (translateTy srcDecl.ty body.layouts).ty = .ok (.closure 0 #[] upvars.length) := hinfo_clos
    have halloc_fn' : annealReifyOrClosureFnPointerAlloc body s.memory.fnPtrs
          { stack := ⟨#[ep2CacheDstSrc topFrame hlt_mf_d hlt_mf_s (translateTy dstDecl.ty body.layouts) (translateTy srcDecl.ty body.layouts)]⟩, machine := m.machine } =
        .ok mptr.withOptionalProvenance { stack := ⟨#[ep2CacheDstSrc topFrame hlt_mf_d hlt_mf_s (translateTy dstDecl.ty body.layouts) (translateTy srcDecl.ty body.layouts)]⟩, machine := m.machine } :=
      halloc_fn
    have hm_eval : Miri.Interpreter.Step.evalStatement hooks () (translateStmt stmt) m = Miri.Interpreter.runRvalue (annealWriteImmediateLM2_2 (.scalar msc)
            ⟨.local 0 dstIdx none topFrame.localsIdentity, translateTy dstDecl.ty body.layouts⟩) st_sd := by
      dsimp only [hooks]; unfold annealStepHooksUnwindFnPtrClosureForState; rw [hact]; rw [heval_live immSrc cSrc hmls_s? hc_s]
      rcases htag with rfl | rfl <;> (
        unfold Miri.Interpreter.runRvalue annealRvalueHooksUnwindFnPtrClosure; dsimp only [translateCastKind, translatePointerCoercion, isOverlayCastKind, ↓reduceIte, st_sd]
        unfold Miri.Interpreter.Cast.cast annealCastHooksUnwindFnPtrClosure annealCastHooksLM4_1 annealCastHooks
        simp only [Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, get, getThe, MonadStateOf.get, EStateM.get, hty_id_eq, beq_self_eq_true, hinfo_clos', hlen_z, Bool.false_eq_true, ↓reduceIte, halloc_fn']; rfl)
    obtain ⟨tf', hm_step, hloc', hdst_m⟩ := miri_step_write_immediate_root hooks hframes hbody hloc hloc_sd hbb hstmt hlt_d_sd htf_sd_d hm_eval
    have hrv : evalRvalue s.frame.locals (.cast (.pointerCoercion coercionTag) (.copy ⟨srcIdx, .nil⟩) dstDecl.ty) s.memory body.localDecls body.layouts = .ok (.ptr ⟨allocId, 0⟩ 8) s.frame.locals
          (internFnPtr s.memory defPath .nil (some dstDecl.ty.kind)).2 := by
      unfold evalRvalue; dsimp only; unfold evalReifyFnPointer; rw [hisReify]; dsimp only; rw [hne_ufp]; dsimp only; rw [evalOperand_copy_nil, hslot_s]; dsimp only
      rw [hdst_ty]; dsimp only; rw [hnot_intr, hsaf_ok]; simp only [Bool.not_false, Bool.true_and]; rw [hop_ty]
      have hextr : extractReifyCoercionTarget? coercionTag (some srcDecl.ty) = some (defPath, .nil) := by
        cases hmk : srcDecl.ty with | mk sk sl =>
        rw [hmk] at hsrc_ty; dsimp at hsrc_ty; subst hsrc_ty; subst hup
        rcases htag with rfl | rfl <;> rfl
      rw [hextr]; dsimp only; rw [hsig_ok]; dsimp only
      have hfst : (internFnPtr s.memory defPath .nil (some dstDecl.ty.kind)).1 = allocId := by unfold internFnPtr; cases hfd : findFnPtrEntry? s.memory.fnPtrs defPath .nil (some dstDecl.ty.kind) <;> (rw [hfd] at haid_eq; exact haid_eq)
      rw [← hdst_ty, hfst]
    have hmem_bor : (internFnPtr s.memory defPath .nil (some dstDecl.ty.kind)).2.borrows = .nil := by unfold internFnPtr; cases findFnPtrEntry? s.memory.fnPtrs defPath .nil (some dstDecl.ty.kind) <;> simpa using hbor_nil
    have hmem_prot : (internFnPtr s.memory defPath .nil (some dstDecl.ty.kind)).2.activeProtectors = .nil := by unfold internFnPtr; cases findFnPtrEntry? s.memory.fnPtrs defPath .nil (some dstDecl.ty.kind) <;> simpa using hprot_nil
    obtain ⟨ha_step, hblk', hstmt', hdst_a⟩ := trusted_step_assign_rvalue_ok hphase hcal hbb hstmt hkind hrv hlt_af_d hslot_d hnot_dead_d hmem_bor hmem_prot
    exact ⟨_, tf', ha_step, hblk', hstmt', hm_step, hloc', hdst_a, hdst_m, fun _ h => h⟩
/-- **`C8.3` Universal `UnsafeFnPointer` Simulation & Divergence**: proves end-
to-end UB equivalence on `.dead`/`.uninit`/dangling-int/nonzero-offset/
non-fn-alloc, positive safe-to-unsafe lockstep preserving `PtrRel`, AND the
strict-check `unsafe fn -> unsafe fn` divergence vs. Miri `Cast.lean:342`. -/
theorem step_cast_unsafeFnPointer_simulation {body : CapturedMir} {s : MachineState} {m : AnnealStepState} {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {srcIdx dstIdx : Local} {srcDecl dstDecl : LocalDecl} {ins : List RigidTy} {out : RigidTy} {srcSaf : Safety} {abi : CallConv} {bb : BasicBlockData} {stmt : Statement}
    (hframes : m.stack.frames = #[topFrame]) (hbody : topFrame.body = translateBody body) (hloc : topFrame.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩) (hphase : ∀ p, body.phase ≠ .other p) (hcal : s.memory.activeCallee = none)
    (hbor_nil : s.memory.borrows = .nil) (hprot_nil : s.memory.activeProtectors = .nil) (hbb : get? body.basicBlocks s.frame.blockIdx = some bb) (hstmt : get? bb.statements s.frame.stmtIdx = some stmt)
    (hkind : stmt.kind = .assign ⟨dstIdx, .nil⟩ (.cast (.pointerCoercion "UnsafeFnPointer") (.copy ⟨srcIdx, .nil⟩) dstDecl.ty)) (hsrc_decl : get? body.localDecls srcIdx = some srcDecl)
    (hdst_decl : get? body.localDecls dstIdx = some dstDecl) (hsrc_ty : srcDecl.ty.kind = .fnPtr ins out srcSaf abi) (hdst_ty : dstDecl.ty.kind = .fnPtr ins out .unsafe_ abi)
    (hne_sd : dstIdx ≠ srcIdx) {slot_d : LocalSlot} {immDst : Miri.Interpreter.Immediate AnnealProv} {cDst : Option Miri.Interpreter.LocalLayout} (hlt_af_d : dstIdx < s.frame.locals.length)
    (hlt_mf_d : dstIdx < topFrame.locals.size) (hslot_d : get? s.frame.locals dstIdx = some slot_d) (hnot_dead_d : slot_d ≠ .dead) (hmls_d : topFrame.locals[dstIdx]'hlt_mf_d = ⟨.live (.immediate immDst), cDst⟩)
    (hc_d : ∀ l, cDst = some l → l = translateTy dstDecl.ty body.layouts) (hlt_mf_s : srcIdx < topFrame.locals.size) :
    let hooks := annealStepHooksUnwindFnPtrClosureForState body s
    (∀ cSrc, get? s.frame.locals srcIdx = some .dead → topFrame.locals[srcIdx]'hlt_mf_s = ⟨.dead, cSrc⟩ → (∀ l, cSrc = some l → l = translateTy srcDecl.ty body.layouts) →
      StepRel body m (stepMirFn body s) (Miri.Interpreter.Step.step hooks () m)) ∧
    (∀ cSrc, get? s.frame.locals srcIdx = some .uninit → topFrame.locals[srcIdx]'hlt_mf_s = ⟨.live (.immediate .uninit), cSrc⟩ → (∀ l, cSrc = some l → l = translateTy srcDecl.ty body.layouts) →
      StepRel body m (stepMirFn body s) (Miri.Interpreter.Step.step hooks () m)) ∧
    (∀ sc msc cSrc, ScalarRel sc msc → sc.sizeBytes = 8 → get? s.frame.locals srcIdx = some (.init (.scalar sc)) → topFrame.locals[srcIdx]'hlt_mf_s = ⟨.live (.immediate (.scalar (.fromScalarInt msc))), cSrc⟩ →
      (∀ l, cSrc = some l → l = translateTy srcDecl.ty body.layouts) → StepRel body m (stepMirFn body s) (Miri.Interpreter.Step.step hooks () m)) ∧
    (∀ (ptrVal : ProvenancePtr) (mAllocId : Miri.Memory.AllocId) (mTag : Miri.Memory.BorTag) (baseAddr : UInt64) (cSrc : Option Miri.Interpreter.LocalLayout), get? s.frame.locals srcIdx = some (.init (.ptr ptrVal 8)) →
      mAllocId.value.toNat = ptrVal.allocId → m.machine.lookupBaseAddr mAllocId = some baseAddr → baseAddr ≤ baseAddr + UInt64.ofNat ptrVal.offsetBytes →
      (baseAddr + UInt64.ofNat ptrVal.offsetBytes - baseAddr).toNat = ptrVal.offsetBytes →
      let mptr : Miri.Memory.Pointer AnnealProv := ⟨Miri.ABI.Size.ofBytes (baseAddr + UInt64.ofNat ptrVal.offsetBytes), .concrete mAllocId mTag⟩; let msc := Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr
      topFrame.locals[srcIdx]'hlt_mf_s = ⟨.live (.immediate (.scalar msc)), cSrc⟩ → (∀ l, cSrc = some l → l = translateTy srcDecl.ty body.layouts) → (ptrVal.offsetBytes ≠ 0 →
        StepRel body m (stepMirFn body s) (Miri.Interpreter.Step.step hooks () m)) ∧
      (ptrVal.offsetBytes = 0 → s.memory.fnPtrs ≠ [] → lookupFnPtr s.memory.fnPtrs ptrVal.allocId = none → StepRel body m (stepMirFn body s) (Miri.Interpreter.Step.step hooks () m)) ∧
      (∀ entry, ptrVal.offsetBytes = 0 → s.memory.fnPtrs ≠ [] → lookupFnPtr s.memory.fnPtrs ptrVal.allocId = some entry → (srcSaf = .safe → callConvEq abi .rustIntrinsic = false → entry.fnSig = none →
          rigidTyListEq ins ins = true → rigidTyEq out out = true → callConvEq abi abi = true → ∃ s' tf', stepMirFn body s = .step s' ∧ s'.frame.blockIdx = s.frame.blockIdx ∧ s'.frame.stmtIdx = s.frame.stmtIdx + 1 ∧
            Miri.Interpreter.Step.step hooks () m = ({ stack := ⟨#[tf']⟩, machine := m.machine }, .ok true) ∧ tf'.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx + 1⟩ ∧ get? s'.frame.locals dstIdx = some (.init (.ptr ptrVal 8)) ∧
            tf'.locals[dstIdx]? = some ⟨.live (.immediate (.scalar msc)), some (translateTy dstDecl.ty body.layouts)⟩ ∧ (∀ allocMap, PtrRel allocMap ptrVal mptr → PtrRel allocMap ptrVal mptr)) ∧
        (srcSaf = .unsafe_ → stepMirFn body s = .fail .ub ∧ ∃ tf', Miri.Interpreter.Step.step hooks () m = ({ stack := ⟨#[tf']⟩, machine := m.machine }, .ok true) ∧ tf'.locals[dstIdx]? =
              some ⟨.live (.immediate (.scalar msc)), some (translateTy dstDecl.ty body.layouts)⟩))) := by
  intro hooks; have hact : activeMirBody body s = body := by simp [activeMirBody, hcal]
  have hhooks_eq : hooks = annealStepHooksUnwindFnPtrClosure body s.memory.callees (annealPoppedFrameState s) s.memory.fnPtrs := by dsimp only [hooks]; unfold annealStepHooksUnwindFnPtrClosureForState; rw [hact]
  have hty42_d : encodeTyId dstDecl.ty = 42 := by unfold encodeTyId; cases hmk : dstDecl.ty with | mk k _ => rw [hmk] at hdst_ty; dsimp at hdst_ty; subst hdst_ty; rfl
  have hno_wide_d : isWideOverlayPlace body.localDecls ⟨dstIdx, #[]⟩ = false := by
    apply isWideOverlayPlace_eq_false_of_decl hdst_decl <;> (cases hmk : dstDecl.ty with | mk k _ => rw [hmk] at hdst_ty; dsimp at hdst_ty; subst hdst_ty; rfl)
  have ⟨hm_dead, hm_uninit, hm_int, hm_ptr⟩ := evalStatement_overlay_cast_fnPtr_common (callees := s.memory.callees) (poppedFrame := annealPoppedFrameState s) (fnPtrs := s.memory.fnPtrs)
    hframes hloc hbb hstmt hkind hsrc_decl hdst_decl hsrc_ty hno_wide_d
    hlt_mf_s hlt_mf_d (by rw [hmls_d]; exact hc_d) (Or.inr ⟨rfl, hty42_d⟩)
  have ⟨hlt_d_sd, htf_sd_d⟩ := ep2CacheDstSrc_dst_getElem? topFrame (dstLay := translateTy dstDecl.ty body.layouts) (srcLay := translateTy srcDecl.ty body.layouts) hlt_mf_d hlt_mf_s hne_sd hmls_d
  let tf_sd := ep2CacheDstSrc topFrame hlt_mf_d hlt_mf_s (translateTy dstDecl.ty body.layouts) (translateTy srcDecl.ty body.layouts)
  have hloc_sd : tf_sd.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩ := by dsimp only [tf_sd]; rw [ep2CacheDstSrc_location]; exact hloc
  have hop_ty : operandTy body.localDecls body.layouts (.copy ⟨srcIdx, .nil⟩) = some srcDecl.ty := by simp [operandTy, placeTy, hsrc_decl]
  have hr_ufp : evalRvalue s.frame.locals (.cast (.pointerCoercion "UnsafeFnPointer") (.copy ⟨srcIdx, .nil⟩) dstDecl.ty) s.memory body.localDecls body.layouts =
      evalUnsafeFnPointer s.frame.locals (.copy ⟨srcIdx, .nil⟩) dstDecl.ty s.memory body.localDecls body.layouts := rfl
  rw [hhooks_eq]; refine ⟨?_, ?_, ?_, ?_⟩
  · intro cSrc hslot_s hmls_s hc_s
    have ha := trusted_step_assign_rvalue_ub hphase hcal hbb hstmt hkind (by rw [hr_ufp]; unfold evalUnsafeFnPointer; rw [evalOperand_copy_nil, hslot_s])
    rw [ha, miri_step_at_statement_error _ hframes hbody hloc hbb hstmt (hm_dead cSrc hmls_s hc_s)]; exact .ub _ _
  · intro cSrc hslot_s hmls_s hc_s
    have ha := trusted_step_assign_rvalue_ub hphase hcal hbb hstmt hkind (by rw [hr_ufp]; unfold evalUnsafeFnPointer; rw [evalOperand_copy_nil, hslot_s])
    rw [ha, miri_step_at_statement_error _ hframes hbody hloc hbb hstmt (hm_uninit cSrc hmls_s hc_s)]; exact .ub _ _
  · intro sc msc cSrc hrel hsc8 hslot_s hmls_s hc_s
    have ha := trusted_step_assign_rvalue_ub hphase hcal hbb hstmt hkind (by rw [hr_ufp]; unfold evalUnsafeFnPointer; rw [evalOperand_copy_nil, hslot_s])
    rw [ha, miri_step_at_statement_error _ hframes hbody hloc hbb hstmt (hm_int sc msc cSrc hrel hsc8 hmls_s hc_s)]; exact .ub _ _
  · intro ptrVal mAllocId mTag baseAddr cSrc hslot_s haid hbase hnow1 hnow2 mptr msc hmls_s hc_s
    have ⟨hchk_off, hchk_none, hchk_some⟩ := annealCheckFnPointerOverlay_cases (fnPtrs := s.memory.fnPtrs) (st := { stack := ⟨#[tf_sd]⟩, machine := m.machine }) (mTag := mTag) haid hbase hnow1 hnow2
    have ⟨hptr_err, hptr_ok⟩ := hm_ptr mptr cSrc hmls_s hc_s; refine ⟨?_, ?_, ?_⟩
    · intro hoff_ne
      have hbeq_off : Nat.beq ptrVal.offsetBytes 0 = false := if hb : Nat.beq ptrVal.offsetBytes 0 = true then False.elim (hoff_ne (Nat.eq_of_beq_eq_true hb)) else Bool.eq_false_iff.mpr hb
      have ha := trusted_step_assign_rvalue_ub hphase hcal hbb hstmt hkind (by
        rw [hr_ufp]; unfold evalUnsafeFnPointer; rw [evalOperand_copy_nil, hslot_s, hdst_ty]; dsimp only
        cases callConvEq abi .rustIntrinsic <;> simp [hbeq_off])
      rw [ha, miri_step_at_statement_error _ hframes hbody hloc hbb hstmt (hptr_err _ (hchk_off hoff_ne))]; exact .ub _ _
    · intro hoff0 hfn_ne hnone
      have ha := trusted_step_assign_rvalue_ub hphase hcal hbb hstmt hkind (by
        rw [hr_ufp]; unfold evalUnsafeFnPointer; rw [evalOperand_copy_nil, hslot_s, hdst_ty]; dsimp only
        cases callConvEq abi .rustIntrinsic
        · rw [hoff0, hbor_nil]; dsimp only [Nat.beq, lookupBorrow]
          cases hfp : s.memory.fnPtrs with
          | nil => exact False.elim (hfn_ne hfp)
          | cons _ _ => dsimp only; rw [← hfp, hnone]; simp
        · rfl)
      rw [ha, miri_step_at_statement_error _ hframes hbody hloc hbb hstmt (hptr_err _ (hchk_none hoff0 hfn_ne hnone))]; exact .ub _ _
    · intro entry hoff0 hfn_ne hsome
      obtain ⟨tf', hm_step, hloc', hdst_m⟩ := miri_step_write_immediate_root (annealStepHooksUnwindFnPtrClosure body s.memory.callees (annealPoppedFrameState s) s.memory.fnPtrs)
        hframes hbody hloc hloc_sd hbb hstmt hlt_d_sd htf_sd_d (hptr_ok (hchk_some entry hoff0 hfn_ne hsome))
      refine ⟨?_, ?_⟩
      · intro hsaf hnot_intr hsig_none hins hout habi
        have hrv : evalRvalue s.frame.locals (.cast (.pointerCoercion "UnsafeFnPointer") (.copy ⟨srcIdx, .nil⟩) dstDecl.ty) s.memory body.localDecls body.layouts = .ok (.ptr ptrVal 8) s.frame.locals s.memory := by
          rw [hr_ufp]; unfold evalUnsafeFnPointer; rw [evalOperand_copy_nil, hslot_s, hdst_ty]; dsimp only; rw [hnot_intr, hop_ty, hoff0, hbor_nil]; dsimp only [Nat.beq, lookupBorrow]
          cases hfp : s.memory.fnPtrs with
          | nil => exact False.elim (hfn_ne hfp)
          | cons _ _ =>
            dsimp only; rw [← hfp, hsome]; dsimp only; rw [hsig_none]; dsimp only
            cases hmk : srcDecl.ty with | mk k _ =>
              rw [hmk] at hsrc_ty; dsimp at hsrc_ty; subst hsrc_ty; subst hsaf; simp [habi, hins, hout]
        obtain ⟨ha_step, hblk', hstmt', hdst_a⟩ := trusted_step_assign_rvalue_ok hphase hcal hbb hstmt hkind hrv hlt_af_d hslot_d hnot_dead_d hbor_nil hprot_nil
        exact ⟨_, tf', ha_step, hblk', hstmt', hm_step, hloc', hdst_a, hdst_m, fun _ h => h⟩
      · intro hunsaf
        have ha_ub := trusted_step_assign_rvalue_ub hphase hcal hbb hstmt hkind (by
          rw [hr_ufp]; unfold evalUnsafeFnPointer; rw [evalOperand_copy_nil, hslot_s, hdst_ty]; dsimp only
          cases callConvEq abi .rustIntrinsic
          · rw [hop_ty]
            cases hmk : srcDecl.ty with | mk k _ =>
              rw [hmk] at hsrc_ty; dsimp at hsrc_ty; subst hsrc_ty; subst hunsaf; rfl
          · rfl)
        exact ⟨ha_ub, tf', hm_step, hdst_m⟩
private theorem evalStatement_overlay_cast_thinPtrToPtr {body : CapturedMir} {callees : List CapturedMir} {poppedFrame : Miri.TreeBorrows.FrameState} {fnPtrs : List FnPtrEntry} {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit} {bb : BasicBlockData} {stmt : Statement} {coercionTag : String} {srcIdx dstIdx : Local} {srcDecl dstDecl : LocalDecl}
    {mutS mutD : Mutability} {ptS ptD : RigidTy} {ptIdS ptIdD : Miri.MIR.TyId} {blockIdx stmtIdx : Nat} (hframes : m.stack.frames = #[topFrame]) (hloc : topFrame.location = .mir ⟨blockIdx, stmtIdx⟩)
    (hbb : get? body.basicBlocks blockIdx = some bb) (hstmt : get? bb.statements stmtIdx = some stmt) (htag : coercionTag = "MutToConstPointer" ∨ coercionTag = "ArrayToPointer") (hkind : stmt.kind = .assign ⟨dstIdx, .nil⟩
      (.cast (.pointerCoercion coercionTag) (.copy ⟨srcIdx, .nil⟩) dstDecl.ty))
    (hsrc_decl : get? body.localDecls srcIdx = some srcDecl) (hdst_decl : get? body.localDecls dstIdx = some dstDecl) (hsrc_ty : srcDecl.ty.kind = .rawPtr mutS ptS) (hdst_ty : dstDecl.ty.kind = .rawPtr mutD ptD)
    (hsrc_thin : isWideSliceOrPointeeTy srcDecl.ty = false ∧ isWideDynRawPtrTy srcDecl.ty = false) (hdst_thin : isWideSliceOrPointeeTy dstDecl.ty = false ∧ isWideDynRawPtrTy dstDecl.ty = false) (hsrc_info : encodeTyId srcDecl.ty = 40 ∨
      castTypeInfoOfEncodedTyIdWideSlice (encodeTyId srcDecl.ty) = .ok (.rawPointer ptIdS))
    (hdst_info : encodeTyId dstDecl.ty = 40 ∨ castTypeInfoOfEncodedTyIdWideSlice (encodeTyId dstDecl.ty) = .ok (.rawPointer ptIdD)) (hlt_s : srcIdx < topFrame.locals.size) (hlt_d : dstIdx < topFrame.locals.size)
    (hc_d : ∀ l, (topFrame.locals[dstIdx]'hlt_d).layout = some l → l = translateTy dstDecl.ty body.layouts) :
    let tf_sd := ep2CacheDstSrc topFrame hlt_d hlt_s (translateTy dstDecl.ty body.layouts) (translateTy srcDecl.ty body.layouts); let st_sd : AnnealStepState := { stack := ⟨#[tf_sd]⟩, machine := m.machine }
    (∀ cSrc, topFrame.locals[srcIdx]? = some ⟨.dead, cSrc⟩ → (∀ l, cSrc = some l → l = translateTy srcDecl.ty body.layouts) → Miri.Interpreter.Step.evalStatement
        (annealStepHooksUnwindFnPtrClosure body callees poppedFrame fnPtrs) () (translateStmt stmt) m =
      (st_sd, .error (.undefinedBehavior "read of dead local"))) ∧
    (∀ cSrc, topFrame.locals[srcIdx]? = some ⟨.live (.immediate .uninit), cSrc⟩ → (∀ l, cSrc = some l → l = translateTy srcDecl.ty body.layouts) → Miri.Interpreter.Step.evalStatement
        (annealStepHooksUnwindFnPtrClosure body callees poppedFrame fnPtrs) () (translateStmt stmt) m =
      (st_sd, .error (.undefinedBehavior "read of uninitialized local"))) ∧
    (∀ sc cSrc, topFrame.locals[srcIdx]? = some ⟨.live (.immediate (.scalar sc)), cSrc⟩ → (∀ l, cSrc = some l → l = translateTy srcDecl.ty body.layouts) → Miri.Interpreter.Step.evalStatement
        (annealStepHooksUnwindFnPtrClosure body callees poppedFrame fnPtrs) () (translateStmt stmt) m =
      Miri.Interpreter.runRvalue (annealWriteImmediateLM2_2 (.scalar sc) ⟨.local 0 dstIdx none topFrame.localsIdentity, translateTy dstDecl.ty body.layouts⟩) st_sd) := by
  intro tf_sd st_sd; have hov_ck : isOverlayCastKind (translateCastKind (.pointerCoercion coercionTag)) = true := by rcases htag with rfl | rfl <;> rfl
  have hno_wide_s := isWideOverlayPlace_eq_false_of_decl hsrc_decl hsrc_thin.1 hsrc_thin.2; have hno_wide_d := isWideOverlayPlace_eq_false_of_decl hdst_decl hdst_thin.1 hdst_thin.2
  have ⟨heval_dead, heval_live⟩ := evalStatement_overlay_assign_cast_copy (callees := callees) (poppedFrame := poppedFrame) (fnPtrs := fnPtrs) hframes hkind hov_ck hsrc_decl hdst_decl hno_wide_s hno_wide_d hlt_s hlt_d hc_d
  have hloc_sd : tf_sd.location = .mir ⟨blockIdx, stmtIdx⟩ := by dsimp only [tf_sd]; rw [ep2CacheDstSrc_location]; exact hloc
  have hact_ck : activeCastCoercionKind? body { stack := ⟨#[tf_sd]⟩, machine := m.machine } = some coercionTag := by
    rcases stmt with ⟨fk, sp⟩; dsimp only at hkind; subst hkind
    exact ep2_activeCastCoercionKind?_singleton hloc_sd hbb hstmt rfl
  have hop_ty : operandTy body.localDecls body.layouts (.copy ⟨srcIdx, .nil⟩) = some srcDecl.ty := by simp [operandTy, placeTy, hsrc_decl]
  have hnone_act : ∀ tyId, activeClosureCastTypeInfo? body { stack := ⟨#[tf_sd]⟩, machine := m.machine } tyId = none := by
    intro tyId; apply ep2_activeClosureCastTypeInfo?_none hloc_sd hbb hstmt; exact Or.inr ⟨⟨dstIdx, .nil⟩, coercionTag, .copy ⟨srcIdx, .nil⟩, dstDecl.ty, srcDecl.ty, hkind, hop_ty, fun dp uv hk => by rw [hsrc_ty] at hk; cases hk⟩
  have hinfo_raw : ∀ (decl : LocalDecl) (mt : Mutability) (pt : RigidTy) (pid : Miri.MIR.TyId), decl.ty.kind = .rawPtr mt pt →
      (encodeTyId decl.ty = 40 ∨ castTypeInfoOfEncodedTyIdWideSlice (encodeTyId decl.ty) = .ok (.rawPointer pid)) →
      ∃ p', castTypeInfoOverlay body { stack := ⟨#[tf_sd]⟩, machine := m.machine } (encodeTyId decl.ty) = .ok (.rawPointer p') := by
    intro decl mt pt pid _ hinf; unfold castTypeInfoOverlay; rw [hnone_act]; dsimp only
    rcases hinf with h40 | hok
    · exact ⟨40, by simp [h40]⟩
    · by_cases h40 : (encodeTyId decl.ty == 40) = true
      · exact ⟨40, by simp [h40]⟩
      · have hne41 : (encodeTyId decl.ty == 41) = false := if h : encodeTyId decl.ty = 41 then by rw [h] at hok; cases hok else beq_false_of_ne h
        have hne42 : (encodeTyId decl.ty == 42) = false := if h : encodeTyId decl.ty = 42 then by rw [h] at hok; cases hok else beq_false_of_ne h
        by_cases hDyn : (encodeTyId decl.ty == wideRawDynPtrTyId) = true
        · exact ⟨dynPointeeTyId, by simp [h40, hne41, hne42, hDyn]⟩
        · exact ⟨pid, by simp [h40, hne41, hne42, hDyn, hok]⟩
  obtain ⟨pS', hinfoS⟩ := hinfo_raw srcDecl mutS ptS ptIdS hsrc_ty hsrc_info; obtain ⟨pD', hinfoD⟩ := hinfo_raw dstDecl mutD ptD ptIdD hdst_ty hdst_info
  have hlay_raw : ∀ (decl : LocalDecl) (mt : Mutability) (pt : RigidTy), decl.ty.kind = .rawPtr mt pt → isWideSliceOrPointeeTy decl.ty = false → isWideDynRawPtrTy decl.ty = false →
      (translateTy decl.ty body.layouts).layout = pointerLayoutData false := by
    intro decl mt pt hk h1 h2; unfold translateTy; cases hmk : decl.ty with | mk k _ => rw [hmk] at hk h1 h2; dsimp at hk; subst hk; rfl
  have hlayS := hlay_raw srcDecl mutS ptS hsrc_ty hsrc_thin.1 hsrc_thin.2; have hlayD := hlay_raw dstDecl mutD ptD hdst_ty hdst_thin.1 hdst_thin.2
  have href_eq : (if encodeTyId dstDecl.ty == 40 then (translateTy dstDecl.ty body.layouts).ty else encodeTyId dstDecl.ty) = (translateTy dstDecl.ty body.layouts).ty := by
    have h : encodeTyId dstDecl.ty = (translateTy dstDecl.ty body.layouts).ty := rfl
    split <;> simp [h]
  have hcast_ptr : ∀ immS cSrc, topFrame.locals[srcIdx]? = some ⟨.live (.immediate immS), cSrc⟩ → (∀ l, cSrc = some l → l = translateTy srcDecl.ty body.layouts) → Miri.Interpreter.Step.evalStatement
        (annealStepHooksUnwindFnPtrClosure body callees poppedFrame fnPtrs) () (translateStmt stmt) m =
      Miri.Interpreter.runRvalue (Miri.Interpreter.Cast.cast (annealCastHooksUnwindFnPtrClosure body fnPtrs) () 16 ⟨.immediate immS, translateTy srcDecl.ty body.layouts⟩ .PtrToPtr (translateTy dstDecl.ty body.layouts).ty
          ⟨.local 0 dstIdx none topFrame.localsIdentity, translateTy dstDecl.ty body.layouts⟩) st_sd := by
    intro immS cSrc hmls_s hc_s; rw [heval_live immS cSrc hmls_s hc_s]
    rcases htag with rfl | rfl <;> (
      unfold Miri.Interpreter.runRvalue annealRvalueHooksUnwindFnPtrClosure; dsimp only [translateCastKind, translatePointerCoercion, st_sd]; dsimp only [tf_sd] at hact_ck
      with_unfolding_all
        simp only [Bind.bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, hact_ck, href_eq]; rfl)
  have hsz_nz_eq : (Miri.ABI.Size.ofBytes 8 = Miri.ABI.Size.ZERO) ↔ False := by decide
  refine ⟨heval_dead, ?_, ?_⟩
  · intro cSrc hmls_s hc_s
    rw [hcast_ptr .uninit cSrc hmls_s hc_s]; dsimp only [st_sd]; unfold Miri.Interpreter.runRvalue Miri.Interpreter.Cast.cast annealCastHooksUnwindFnPtrClosure annealCastHooksLM4_1 annealCastHooks annealReadImmediateOverlay
    have htyS : (translateTy srcDecl.ty body.layouts).ty = encodeTyId srcDecl.ty := rfl; have hsz8_eq : (Miri.ABI.Size.ofBytes 8 == Miri.ABI.Size.ZERO) = false := by decide
    simp only [Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, get, getThe, MonadStateOf.get, EStateM.get, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte, htyS, hinfoS, hlayS, pointerLayoutData, hsz8_eq, Bool.false_and]; rfl
  · intro sc cSrc hmls_s hc_s
    rw [hcast_ptr (.scalar sc) cSrc hmls_s hc_s]; dsimp only [st_sd]; have htyS : (translateTy srcDecl.ty body.layouts).ty = encodeTyId srcDecl.ty := rfl
    have htyD : (translateTy dstDecl.ty body.layouts).ty = encodeTyId dstDecl.ty := rfl
    have hptr_ok : Miri.Interpreter.Cast.ptrToPtr (annealCastHooksUnwindFnPtrClosure body fnPtrs) () ⟨.scalar sc, translateTy srcDecl.ty body.layouts⟩ (translateTy dstDecl.ty body.layouts)
          { stack := ⟨#[tf_sd]⟩, machine := m.machine } =
        .ok ⟨.scalar sc, translateTy dstDecl.ty body.layouts⟩ { stack := ⟨#[tf_sd]⟩, machine := m.machine } := by
      with_unfolding_all
        simp only [Miri.Interpreter.Cast.ptrToPtr, annealCastHooksUnwindFnPtrClosure, htyS, htyD, hinfoS, hlayS, hlayD, pointerLayoutData, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, get, getThe, MonadStateOf.get, EStateM.get]
        change (if false = true then _ else _ : Miri.Interpreter.RvalueM AnnealStepState _) _ = _
        simp only [Bool.false_eq_true, ↓reduceIte, EStateM.bind, EStateM.pure, EStateM.get, hinfoD, beq_self_eq_true]
    have hstep1 : Miri.Interpreter.runRvalue (Miri.Interpreter.Cast.cast (annealCastHooksUnwindFnPtrClosure body fnPtrs) () 16 ⟨.immediate (.scalar sc), translateTy srcDecl.ty body.layouts⟩ .PtrToPtr
            (translateTy dstDecl.ty body.layouts).ty ⟨.local 0 dstIdx none topFrame.localsIdentity, translateTy dstDecl.ty body.layouts⟩)
          { stack := ⟨#[tf_sd]⟩, machine := m.machine } =
        Miri.Interpreter.runRvalue (do
            let result ← Miri.Interpreter.Cast.ptrToPtr (annealCastHooksUnwindFnPtrClosure body fnPtrs) () ⟨.scalar sc, translateTy srcDecl.ty body.layouts⟩ (translateTy dstDecl.ty body.layouts)
            annealWriteImmediateLM2_2 result.imm ⟨.local 0 dstIdx none topFrame.localsIdentity, translateTy dstDecl.ty body.layouts⟩)
          { stack := ⟨#[tf_sd]⟩, machine := m.machine } := by
      unfold Miri.Interpreter.runRvalue Miri.Interpreter.Cast.cast annealCastHooksUnwindFnPtrClosure annealCastHooksLM4_1 annealCastHooks annealReadImmediateOverlay
      simp only [Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, get, getThe, MonadStateOf.get, EStateM.get, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte, htyS, hinfoS, hlayS, pointerLayoutData]
    rw [hstep1]; dsimp only [Miri.Interpreter.runRvalue, Bind.bind, EStateM.bind]; rw [hptr_ok]
private theorem step_cast_thinPtrCoercion_core {body : CapturedMir} {s : MachineState} {m : AnnealStepState} {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {srcIdx dstIdx : Local} {srcDecl dstDecl : LocalDecl} {coercionTag : String} {mutS mutD : Mutability} {ptS ptD : RigidTy} {ptIdS ptIdD : Miri.MIR.TyId} {bb : BasicBlockData} {stmt : Statement}
    (hframes : m.stack.frames = #[topFrame]) (hbody : topFrame.body = translateBody body) (hloc : topFrame.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩) (hphase : ∀ p, body.phase ≠ .other p)
    (hcal : s.memory.activeCallee = none) (hbor_nil : s.memory.borrows = .nil) (hprot_nil : s.memory.activeProtectors = .nil) (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some stmt) (htag : coercionTag = "MutToConstPointer" ∨ coercionTag = "ArrayToPointer") (hkind : stmt.kind = .assign ⟨dstIdx, .nil⟩
      (.cast (.pointerCoercion coercionTag) (.copy ⟨srcIdx, .nil⟩) dstDecl.ty))
    (hsrc_decl : get? body.localDecls srcIdx = some srcDecl) (hdst_decl : get? body.localDecls dstIdx = some dstDecl) (hsrc_ty : srcDecl.ty.kind = .rawPtr mutS ptS) (hdst_ty : dstDecl.ty.kind = .rawPtr mutD ptD)
    (hsrc_thin : isWideSliceOrPointeeTy srcDecl.ty = false ∧ isWideDynRawPtrTy srcDecl.ty = false) (hdst_thin : isWideSliceOrPointeeTy dstDecl.ty = false ∧ isWideDynRawPtrTy dstDecl.ty = false) (hsrc_info : encodeTyId srcDecl.ty = 40 ∨
      castTypeInfoOfEncodedTyIdWideSlice (encodeTyId srcDecl.ty) = .ok (.rawPointer ptIdS))
    (hdst_info : encodeTyId dstDecl.ty = 40 ∨ castTypeInfoOfEncodedTyIdWideSlice (encodeTyId dstDecl.ty) = .ok (.rawPointer ptIdD)) (hne_sd : dstIdx ≠ srcIdx) {slot_d : LocalSlot} {immDst : Miri.Interpreter.Immediate AnnealProv}
    {cDst : Option Miri.Interpreter.LocalLayout} (hlt_af_d : dstIdx < s.frame.locals.length) (hlt_mf_d : dstIdx < topFrame.locals.size) (hslot_d : get? s.frame.locals dstIdx = some slot_d)
    (hnot_dead_d : slot_d ≠ .dead) (hmls_d : topFrame.locals[dstIdx]'hlt_mf_d = ⟨.live (.immediate immDst), cDst⟩) (hc_d : ∀ l, cDst = some l → l = translateTy dstDecl.ty body.layouts) (hlt_mf_s : srcIdx < topFrame.locals.size)
    (ha_ptr : ∀ ptrVal, get? s.frame.locals srcIdx = some (.init (.ptr ptrVal 8)) → evalRvalue s.frame.locals (.cast (.pointerCoercion coercionTag) (.copy ⟨srcIdx, .nil⟩) dstDecl.ty)
        s.memory body.localDecls body.layouts = .ok (.ptr ptrVal 8) s.frame.locals s.memory)
    (ha_sc : ∀ sc msc, ScalarRel sc msc → sc.sizeBytes = 8 → get? s.frame.locals srcIdx = some (.init (.scalar sc)) → evalRvalue s.frame.locals (.cast (.pointerCoercion coercionTag) (.copy ⟨srcIdx, .nil⟩) dstDecl.ty)
        s.memory body.localDecls body.layouts = .ok (.scalar sc) s.frame.locals s.memory) :
    let hooks := annealStepHooksUnwindFnPtrClosure body
    (∀ cSrc, get? s.frame.locals srcIdx = some .dead → topFrame.locals[srcIdx]'hlt_mf_s = ⟨.dead, cSrc⟩ → (∀ l, cSrc = some l → l = translateTy srcDecl.ty body.layouts) →
      StepRel body m (stepMirFn body s) (Miri.Interpreter.Step.step hooks () m)) ∧
    (∀ cSrc, get? s.frame.locals srcIdx = some .uninit → topFrame.locals[srcIdx]'hlt_mf_s = ⟨.live (.immediate .uninit), cSrc⟩ → (∀ l, cSrc = some l → l = translateTy srcDecl.ty body.layouts) →
      StepRel body m (stepMirFn body s) (Miri.Interpreter.Step.step hooks () m)) ∧
    (∀ (ptrVal : ProvenancePtr) (mptr : Miri.Memory.Pointer AnnealProv) cSrc, get? s.frame.locals srcIdx = some (.init (.ptr ptrVal 8)) →
      let msc := Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr
      topFrame.locals[srcIdx]'hlt_mf_s = ⟨.live (.immediate (.scalar msc)), cSrc⟩ → (∀ l, cSrc = some l → l = translateTy srcDecl.ty body.layouts) → ∃ s' tf', stepMirFn body s = .step s' ∧ s'.frame.blockIdx = s.frame.blockIdx ∧
        s'.frame.stmtIdx = s.frame.stmtIdx + 1 ∧ Miri.Interpreter.Step.step hooks () m = ({ stack := ⟨#[tf']⟩, machine := m.machine }, .ok true) ∧ tf'.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx + 1⟩ ∧
        get? s'.frame.locals dstIdx = some (.init (.ptr ptrVal 8)) ∧ tf'.locals[dstIdx]? = some ⟨.live (.immediate (.scalar msc)), some (translateTy dstDecl.ty body.layouts)⟩ ∧
        (∀ allocMap, PtrRel allocMap ptrVal mptr → PtrRel allocMap ptrVal mptr)) ∧
    (∀ sc msc cSrc, ScalarRel sc msc → sc.sizeBytes = 8 → get? s.frame.locals srcIdx = some (.init (.scalar sc)) → topFrame.locals[srcIdx]'hlt_mf_s = ⟨.live (.immediate (.scalar (.fromScalarInt msc))), cSrc⟩ →
      (∀ l, cSrc = some l → l = translateTy srcDecl.ty body.layouts) → ∃ s' tf', stepMirFn body s = .step s' ∧ Miri.Interpreter.Step.step hooks () m = ({ stack := ⟨#[tf']⟩, machine := m.machine }, .ok true) ∧
        get? s'.frame.locals dstIdx = some (.init (.scalar sc)) ∧ tf'.locals[dstIdx]? = some ⟨.live (.immediate (.scalar (.fromScalarInt msc))), some (translateTy dstDecl.ty body.layouts)⟩) := by
  intro hooks
  have ⟨hdead_m, huninit_m, hsc_m⟩ := evalStatement_overlay_cast_thinPtrToPtr (callees := .nil) (poppedFrame := {}) (fnPtrs := .nil) hframes hloc hbb hstmt htag hkind hsrc_decl hdst_decl hsrc_ty hdst_ty
    hsrc_thin hdst_thin hsrc_info hdst_info hlt_mf_s hlt_mf_d (by rw [hmls_d]; exact hc_d)
  have ⟨hlt_d_sd, htf_sd_d⟩ := ep2CacheDstSrc_dst_getElem? topFrame (dstLay := translateTy dstDecl.ty body.layouts) (srcLay := translateTy srcDecl.ty body.layouts) hlt_mf_d hlt_mf_s hne_sd hmls_d
  have hloc_sd : (ep2CacheDstSrc topFrame hlt_mf_d hlt_mf_s (translateTy dstDecl.ty body.layouts) (translateTy srcDecl.ty body.layouts)).location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩ := by rw [ep2CacheDstSrc_location]; exact hloc
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro cSrc hslot_s hmls_s hc_s
    have ha := trusted_step_assign_rvalue_ub hphase hcal hbb hstmt hkind (by
      rcases htag with rfl | rfl <;>
        (unfold evalRvalue; dsimp only; unfold evalReifyFnPointer; rw [evalOperand_copy_nil, hslot_s]; rfl))
    rw [ha, miri_step_at_statement_error _ hframes hbody hloc hbb hstmt (hdead_m cSrc (by rw [Array.getElem?_eq_getElem hlt_mf_s, hmls_s]) hc_s)]; exact .ub _ _
  · intro cSrc hslot_s hmls_s hc_s
    have ha := trusted_step_assign_rvalue_ub hphase hcal hbb hstmt hkind (by
      rcases htag with rfl | rfl <;>
        (unfold evalRvalue; dsimp only; unfold evalReifyFnPointer; rw [evalOperand_copy_nil, hslot_s]; rfl))
    rw [ha, miri_step_at_statement_error _ hframes hbody hloc hbb hstmt (huninit_m cSrc (by rw [Array.getElem?_eq_getElem hlt_mf_s, hmls_s]) hc_s)]; exact .ub _ _
  · intro ptrVal mptr cSrc hslot_s msc hmls_s hc_s
    obtain ⟨tf', hm_step, hloc', hdst_m⟩ := miri_step_write_immediate_root hooks hframes hbody hloc hloc_sd hbb hstmt hlt_d_sd htf_sd_d (hsc_m msc cSrc (by rw [Array.getElem?_eq_getElem hlt_mf_s, hmls_s]) hc_s)
    obtain ⟨ha_step, hblk', hstmt', hdst_a⟩ := trusted_step_assign_rvalue_ok hphase hcal hbb hstmt hkind (ha_ptr ptrVal hslot_s) hlt_af_d hslot_d hnot_dead_d hbor_nil hprot_nil
    exact ⟨_, tf', ha_step, hblk', hstmt', hm_step, hloc', hdst_a, hdst_m, fun _ h => h⟩
  · intro sc msc cSrc hrel hsc8 hslot_s hmls_s hc_s
    obtain ⟨tf', hm_step, _, hdst_m⟩ := miri_step_write_immediate_root hooks hframes hbody hloc hloc_sd hbb hstmt hlt_d_sd htf_sd_d (hsc_m (.fromScalarInt msc) cSrc (by rw [Array.getElem?_eq_getElem hlt_mf_s, hmls_s]) hc_s)
    obtain ⟨ha_step, _, _, hdst_a⟩ := trusted_step_assign_rvalue_ok hphase hcal hbb hstmt hkind (ha_sc sc msc hrel hsc8 hslot_s) hlt_af_d hslot_d hnot_dead_d hbor_nil hprot_nil; exact ⟨_, tf', ha_step, hm_step, hdst_a, hdst_m⟩
private theorem wrapScalarBits_id_of_rel8 {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt} (hrel : ScalarRel sc msc) (hsc8 : sc.sizeBytes = 8) :
    ({ bits := wrapScalarBits sc.bits (scalarModulus 8), sizeBytes := 8 } : MirAst.ScalarInt) = sc := by
  have hc := hrel.canonical; rw [hsc8] at hc
  have hw : wrapScalarBits sc.bits (scalarModulus 8) = sc.bits := by have hble : (scalarModulus 8).ble sc.bits = false := Bool.eq_false_iff.mpr fun h => absurd (Nat.ble_eq.mp h) (by omega); unfold wrapScalarBits; rw [hble]
  rw [hw]; cases sc with | mk b sz => dsimp at hsc8; subst hsc8; rfl
/-- **`C8.4` Universal Thin `MutToConstPointer` Simulation**: covers `.dead`/
`.uninit` UB, provenance-bearing pointer `PtrRel` lockstep, and 8-byte
scalar address `ScalarRel` lockstep across arbitrary thin `*mut T -> *const
T`. -/
theorem step_cast_mutToConstPointer_thin_simulation {body : CapturedMir} {s : MachineState} {m : AnnealStepState} {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {srcIdx dstIdx : Local} {srcDecl dstDecl : LocalDecl} {pt : RigidTy} {ptId : Miri.MIR.TyId} {bb : BasicBlockData} {stmt : Statement} (hframes : m.stack.frames = #[topFrame]) (hbody : topFrame.body = translateBody body)
    (hloc : topFrame.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩) (hphase : ∀ p, body.phase ≠ .other p) (hlay_empty : body.layouts = emptyLayoutTable) (hcal : s.memory.activeCallee = none) (hbor_nil : s.memory.borrows = .nil)
    (hprot_nil : s.memory.activeProtectors = .nil) (hbb : get? body.basicBlocks s.frame.blockIdx = some bb) (hstmt : get? bb.statements s.frame.stmtIdx = some stmt) (hkind : stmt.kind = .assign ⟨dstIdx, .nil⟩
      (.cast (.pointerCoercion "MutToConstPointer") (.copy ⟨srcIdx, .nil⟩) dstDecl.ty))
    (hsrc_decl : get? body.localDecls srcIdx = some srcDecl) (hdst_decl : get? body.localDecls dstIdx = some dstDecl) (hsrc_ty : srcDecl.ty.kind = .rawPtr .mut pt) (hdst_ty : dstDecl.ty.kind = .rawPtr .not pt)
    (hpt_eq : rigidTyEq pt pt = true) (hdst_thin : isWideRawPtrTy dstDecl.ty = false ∧ isWideSliceOrPointeeTy dstDecl.ty = false ∧ isWideDynRawPtrTy dstDecl.ty = false)
    (hsrc_thin : isWideSliceOrPointeeTy srcDecl.ty = false ∧ isWideDynRawPtrTy srcDecl.ty = false) (hinfo : encodeTyId dstDecl.ty = 40 ∨ castTypeInfoOfEncodedTyIdWideSlice (encodeTyId dstDecl.ty) = .ok (.rawPointer ptId))
    (hne_sd : dstIdx ≠ srcIdx) {slot_d : LocalSlot} {immDst : Miri.Interpreter.Immediate AnnealProv} {cDst : Option Miri.Interpreter.LocalLayout} (hlt_af_d : dstIdx < s.frame.locals.length)
    (hlt_mf_d : dstIdx < topFrame.locals.size) (hslot_d : get? s.frame.locals dstIdx = some slot_d) (hnot_dead_d : slot_d ≠ .dead) (hmls_d : topFrame.locals[dstIdx]'hlt_mf_d = ⟨.live (.immediate immDst), cDst⟩)
    (hc_d : ∀ l, cDst = some l → l = translateTy dstDecl.ty body.layouts) (hlt_mf_s : srcIdx < topFrame.locals.size) :
    let hooks := annealStepHooksUnwindFnPtrClosure body
    (∀ cSrc, get? s.frame.locals srcIdx = some .dead → topFrame.locals[srcIdx]'hlt_mf_s = ⟨.dead, cSrc⟩ → (∀ l, cSrc = some l → l = translateTy srcDecl.ty body.layouts) →
      StepRel body m (stepMirFn body s) (Miri.Interpreter.Step.step hooks () m)) ∧
    (∀ cSrc, get? s.frame.locals srcIdx = some .uninit → topFrame.locals[srcIdx]'hlt_mf_s = ⟨.live (.immediate .uninit), cSrc⟩ → (∀ l, cSrc = some l → l = translateTy srcDecl.ty body.layouts) →
      StepRel body m (stepMirFn body s) (Miri.Interpreter.Step.step hooks () m)) ∧
    (∀ (ptrVal : ProvenancePtr) (mptr : Miri.Memory.Pointer AnnealProv) cSrc, get? s.frame.locals srcIdx = some (.init (.ptr ptrVal 8)) →
      let msc := Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr
      topFrame.locals[srcIdx]'hlt_mf_s = ⟨.live (.immediate (.scalar msc)), cSrc⟩ → (∀ l, cSrc = some l → l = translateTy srcDecl.ty body.layouts) → ∃ s' tf', stepMirFn body s = .step s' ∧ s'.frame.blockIdx = s.frame.blockIdx ∧
        s'.frame.stmtIdx = s.frame.stmtIdx + 1 ∧ Miri.Interpreter.Step.step hooks () m = ({ stack := ⟨#[tf']⟩, machine := m.machine }, .ok true) ∧ tf'.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx + 1⟩ ∧
        get? s'.frame.locals dstIdx = some (.init (.ptr ptrVal 8)) ∧ tf'.locals[dstIdx]? = some ⟨.live (.immediate (.scalar msc)), some (translateTy dstDecl.ty body.layouts)⟩ ∧
        (∀ allocMap, PtrRel allocMap ptrVal mptr → PtrRel allocMap ptrVal mptr)) ∧
    (∀ sc msc cSrc, ScalarRel sc msc → sc.sizeBytes = 8 → get? s.frame.locals srcIdx = some (.init (.scalar sc)) → topFrame.locals[srcIdx]'hlt_mf_s = ⟨.live (.immediate (.scalar (.fromScalarInt msc))), cSrc⟩ →
      (∀ l, cSrc = some l → l = translateTy srcDecl.ty body.layouts) → ∃ s' tf', stepMirFn body s = .step s' ∧ Miri.Interpreter.Step.step hooks () m = ({ stack := ⟨#[tf']⟩, machine := m.machine }, .ok true) ∧
        get? s'.frame.locals dstIdx = some (.init (.scalar sc)) ∧ tf'.locals[dstIdx]? = some ⟨.live (.immediate (.scalar (.fromScalarInt msc))), some (translateTy dstDecl.ty body.layouts)⟩) := by
  have henc_eq : encodeTyId srcDecl.ty = encodeTyId dstDecl.ty := by
    unfold encodeTyId; cases h1 : srcDecl.ty with | mk k1 _ => cases h2 : dstDecl.ty with | mk k2 _ =>
    rw [h1] at hsrc_ty; rw [h2] at hdst_ty; dsimp at hsrc_ty hdst_ty; subst hsrc_ty hdst_ty; rfl
  have hshape : mutToConstTargetShape? (operandTy body.localDecls body.layouts (.copy ⟨srcIdx, .nil⟩)) dstDecl.ty = some none := by
    have hop_ty : operandTy body.localDecls body.layouts (.copy ⟨srcIdx, .nil⟩) = some srcDecl.ty := by simp [operandTy, placeTy, hsrc_decl]
    unfold mutToConstTargetShape?; rw [hop_ty, hdst_ty, hdst_thin.1]; cases hmk : srcDecl.ty with | mk k _ => rw [hmk] at hsrc_ty; dsimp at hsrc_ty; subst hsrc_ty; simp [hpt_eq]
  exact step_cast_thinPtrCoercion_core hframes hbody hloc hphase hcal hbor_nil hprot_nil hbb hstmt (Or.inl rfl) hkind hsrc_decl hdst_decl hsrc_ty hdst_ty hsrc_thin ⟨hdst_thin.2.1, hdst_thin.2.2⟩
    (by rw [henc_eq]; exact hinfo) hinfo hne_sd hlt_af_d hlt_mf_d hslot_d hnot_dead_d hmls_d hc_d hlt_mf_s (fun ptrVal hs => by
      unfold evalRvalue; dsimp only; unfold evalReifyFnPointer; rw [hshape, hlay_empty, evalOperand_copy_nil, hs]; rfl)
    (fun sc msc hrel hsc8 hs => by
      unfold evalRvalue; dsimp only; unfold evalReifyFnPointer; rw [hshape, hlay_empty, evalOperand_copy_nil, hs]; dsimp only [isReifyFnPointerCoercion, stringEq, layoutPointerBytes, emptyLayoutTable]
      rw [hsc8, Nat.beq_refl]; dsimp only; rw [wrapScalarBits_id_of_rel8 hrel hsc8]; rfl)
/-- **`C8.5` Universal Thin `ArrayToPointer` Simulation**: covers `.dead`/
`.uninit` UB, untracked provenance-pointer `PtrRel` lockstep, and 8-byte
scalar address `ScalarRel` lockstep for `*const/*mut [T; N] -> *const/*mut
T`. -/
theorem step_cast_arrayToPointer_thin_simulation {body : CapturedMir} {s : MachineState} {m : AnnealStepState} {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {srcIdx dstIdx : Local} {srcDecl dstDecl : LocalDecl} {mutS mutD : Mutability} {elem : RigidTy} {arrLen : Nat} {ptIdD : Miri.MIR.TyId} {bb : BasicBlockData} {stmt : Statement}
    (hframes : m.stack.frames = #[topFrame]) (hbody : topFrame.body = translateBody body) (hloc : topFrame.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩)
    (hphase : ∀ p, body.phase ≠ .other p) (hlay_empty : body.layouts = emptyLayoutTable) (hcal : s.memory.activeCallee = none) (hbor_nil : s.memory.borrows = .nil) (hprot_nil : s.memory.activeProtectors = .nil)
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb) (hstmt : get? bb.statements s.frame.stmtIdx = some stmt) (hkind : stmt.kind = .assign ⟨dstIdx, .nil⟩
      (.cast (.pointerCoercion "ArrayToPointer") (.copy ⟨srcIdx, .nil⟩) dstDecl.ty))
    (hsrc_decl : get? body.localDecls srcIdx = some srcDecl) (hdst_decl : get? body.localDecls dstIdx = some dstDecl) (hsrc_ty : srcDecl.ty.kind = .rawPtr mutS (.array elem arrLen)) (hdst_ty : dstDecl.ty.kind = .rawPtr mutD elem)
    (hmut_ok : unsizeMutabilityCompatible mutS mutD = true) (helem_eq : rigidTyEq elem elem = true) (hdst_thin : isWideRawPtrTy dstDecl.ty = false ∧ isWideSliceOrPointeeTy dstDecl.ty = false ∧ isWideDynRawPtrTy dstDecl.ty = false)
    (hdst_info : encodeTyId dstDecl.ty = 40 ∨ castTypeInfoOfEncodedTyIdWideSlice (encodeTyId dstDecl.ty) = .ok (.rawPointer ptIdD)) (hne_sd : dstIdx ≠ srcIdx) {slot_d : LocalSlot} {immDst : Miri.Interpreter.Immediate AnnealProv}
    {cDst : Option Miri.Interpreter.LocalLayout} (hlt_af_d : dstIdx < s.frame.locals.length) (hlt_mf_d : dstIdx < topFrame.locals.size) (hslot_d : get? s.frame.locals dstIdx = some slot_d)
    (hnot_dead_d : slot_d ≠ .dead) (hmls_d : topFrame.locals[dstIdx]'hlt_mf_d = ⟨.live (.immediate immDst), cDst⟩) (hc_d : ∀ l, cDst = some l → l = translateTy dstDecl.ty body.layouts) (hlt_mf_s : srcIdx < topFrame.locals.size) :
    let hooks := annealStepHooksUnwindFnPtrClosure body
    (∀ cSrc, get? s.frame.locals srcIdx = some .dead → topFrame.locals[srcIdx]'hlt_mf_s = ⟨.dead, cSrc⟩ → (∀ l, cSrc = some l → l = translateTy srcDecl.ty body.layouts) →
      StepRel body m (stepMirFn body s) (Miri.Interpreter.Step.step hooks () m)) ∧
    (∀ cSrc, get? s.frame.locals srcIdx = some .uninit → topFrame.locals[srcIdx]'hlt_mf_s = ⟨.live (.immediate .uninit), cSrc⟩ → (∀ l, cSrc = some l → l = translateTy srcDecl.ty body.layouts) →
      StepRel body m (stepMirFn body s) (Miri.Interpreter.Step.step hooks () m)) ∧
    (∀ (ptrVal : ProvenancePtr) (mptr : Miri.Memory.Pointer AnnealProv) cSrc, get? s.frame.locals srcIdx = some (.init (.ptr ptrVal 8)) →
      let msc := Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr
      topFrame.locals[srcIdx]'hlt_mf_s = ⟨.live (.immediate (.scalar msc)), cSrc⟩ → (∀ l, cSrc = some l → l = translateTy srcDecl.ty body.layouts) → ∃ s' tf', stepMirFn body s = .step s' ∧ s'.frame.blockIdx = s.frame.blockIdx ∧
        s'.frame.stmtIdx = s.frame.stmtIdx + 1 ∧ Miri.Interpreter.Step.step hooks () m = ({ stack := ⟨#[tf']⟩, machine := m.machine }, .ok true) ∧ tf'.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx + 1⟩ ∧
        get? s'.frame.locals dstIdx = some (.init (.ptr ptrVal 8)) ∧ tf'.locals[dstIdx]? = some ⟨.live (.immediate (.scalar msc)), some (translateTy dstDecl.ty body.layouts)⟩ ∧
        (∀ allocMap, PtrRel allocMap ptrVal mptr → PtrRel allocMap ptrVal mptr)) ∧
    (∀ sc msc cSrc, ScalarRel sc msc → sc.sizeBytes = 8 → get? s.frame.locals srcIdx = some (.init (.scalar sc)) → topFrame.locals[srcIdx]'hlt_mf_s = ⟨.live (.immediate (.scalar (.fromScalarInt msc))), cSrc⟩ →
      (∀ l, cSrc = some l → l = translateTy srcDecl.ty body.layouts) → ∃ s' tf', stepMirFn body s = .step s' ∧ Miri.Interpreter.Step.step hooks () m = ({ stack := ⟨#[tf']⟩, machine := m.machine }, .ok true) ∧
        get? s'.frame.locals dstIdx = some (.init (.scalar sc)) ∧ tf'.locals[dstIdx]? = some ⟨.live (.immediate (.scalar (.fromScalarInt msc))), some (translateTy dstDecl.ty body.layouts)⟩) := by
  have hsrc_40 : encodeTyId srcDecl.ty = 40 := by unfold encodeTyId; cases hmk : srcDecl.ty with | mk k _ => rw [hmk] at hsrc_ty; dsimp at hsrc_ty; subst hsrc_ty; rfl
  have hsrc_thin : isWideSliceOrPointeeTy srcDecl.ty = false ∧ isWideDynRawPtrTy srcDecl.ty = false := by cases hmk : srcDecl.ty with | mk k _ => rw [hmk] at hsrc_ty; dsimp at hsrc_ty; subst hsrc_ty; exact ⟨rfl, rfl⟩
  have helen : arrayToPointerElemLen? (operandTy body.localDecls body.layouts (.copy ⟨srcIdx, .nil⟩)) dstDecl.ty = some (some arrLen) := by
    have hop_ty : operandTy body.localDecls body.layouts (.copy ⟨srcIdx, .nil⟩) = some srcDecl.ty := by simp [operandTy, placeTy, hsrc_decl]
    unfold arrayToPointerElemLen?; rw [hop_ty, hdst_ty, hdst_thin.1]; cases hmk : srcDecl.ty with | mk k _ => rw [hmk] at hsrc_ty; dsimp at hsrc_ty; subst hsrc_ty; simp [hmut_ok, helem_eq]
  exact step_cast_thinPtrCoercion_core (ptIdS := 40) hframes hbody hloc hphase hcal hbor_nil hprot_nil hbb hstmt (Or.inr rfl) hkind hsrc_decl hdst_decl hsrc_ty hdst_ty hsrc_thin ⟨hdst_thin.2.1, hdst_thin.2.2⟩
    (Or.inl hsrc_40) hdst_info hne_sd hlt_af_d hlt_mf_d hslot_d hnot_dead_d hmls_d hc_d hlt_mf_s (fun ptrVal hs => by
      unfold evalRvalue; dsimp only; unfold evalReifyFnPointer; rw [evalOperand_copy_nil, hs]; dsimp only [isReifyFnPointerCoercion, stringEq]; rw [helen, hlay_empty, hbor_nil]; rfl)
    (fun sc msc hrel hsc8 hs => by
      unfold evalRvalue; dsimp only; unfold evalReifyFnPointer; rw [evalOperand_copy_nil, hs]; dsimp only [isReifyFnPointerCoercion, stringEq]; rw [helen, hlay_empty]; dsimp only [layoutPointerBytes, emptyLayoutTable]
      rw [hsc8, Nat.beq_refl]; dsimp only; rw [wrapScalarBits_id_of_rel8 hrel hsc8]; rfl)
section C8SimulationsAndWitnesses
private def c8ZstClosureLayout : TypeLayout := { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := .memory, variants := .single 0, fields := .arbitrary .nil .nil, fieldLayouts := .nil, isUninhabited := false }
private def c8ClosureLayouts : LayoutTable := { emptyLayoutTable with entries := [c8ZstClosureLayout] }
private def c8ClosTy : Ty := { kind := .closure "c8_zst_clos" .nil, layoutIdx := 0 }
private def c8CapClosTy : Ty := { kind := .closure "c8_cap_clos" [.uint .u32], layoutIdx := 0 }
private def c8FnDefTy : Ty := { kind := .fnDef "c8_zst_clos" .nil, layoutIdx := 0 }
private def c8SafeFnTy : Ty := { kind := .fnPtr [.uint .u32] (.uint .u32) .safe .rust, layoutIdx := 0 }
private def c8UnsafeFnTy : Ty := { kind := .fnPtr [.uint .u32] (.uint .u32) .unsafe_ .rust, layoutIdx := 0 }
private def c8IntrFnTy : Ty := { kind := .fnPtr [.uint .u32] (.uint .u32) .safe .rustIntrinsic, layoutIdx := 0 }
private def c8BadSigFnTy : Ty := { kind := .fnPtr .nil (.uint .u32) .unsafe_ .rust, layoutIdx := 0 }
private def c8ClosCallee : CapturedMir := mkEp2Body "c8_zst_clos" [ep2U32Ty, ep2U32Ty] [.assign ⟨0, .nil⟩ (.use (.copy ⟨1, .nil⟩))]
private def c8Aid : Miri.Memory.AllocId := ⟨65536, by decide⟩
private def c8Base : UInt64 := annealStackBaseAddr c8Aid
private def c8PtrSc : Miri.Memory.Scalar AnnealProv := Miri.Memory.Scalar.fromPointer annealTargetDataLayout ⟨Miri.ABI.Size.ofBytes c8Base, .concrete c8Aid .one⟩
/-- **`C8.1` Witness**: verifies `ReifyFnPointer(Safe)` and
`ReifyFnPointer(Unsafe)` write exact `c8Aid` pointer in both Trusted and
Miri, plus `rust-intrinsic` ABI UB. -/
theorem w_c8_1_reifyFnPointer_overlay_safe_unsafe_and_abi :
    let mach := mkEp2AddrMachine c8Aid c8Base; let mem0 : Memory := { emptyMemory with nextAllocId := 65536, callees := [{ c8ClosCallee with argCount := 1 }] }
    let bSafe := mkEp2Body "c8_1_safe" [c8SafeFnTy] [.assign ⟨0, .nil⟩ (.cast (.pointerCoercion "ReifyFnPointer(Safe)") (.constant { ty := c8FnDefTy, val := .zeroSized }) c8SafeFnTy)]
    let bUnsafe := mkEp2Body "c8_1_unsafe" [c8UnsafeFnTy] [.assign ⟨0, .nil⟩ (.cast (.pointerCoercion "ReifyFnPointer(Unsafe)") (.constant { ty := c8FnDefTy, val := .zeroSized }) c8UnsafeFnTy)]
    let bIntr := mkEp2Body "c8_1_intr" [c8IntrFnTy] [.assign ⟨0, .nil⟩ (.cast (.pointerCoercion "ReifyFnPointer") (.constant { ty := c8FnDefTy, val := .zeroSized }) c8IntrFnTy)]
    let s0 : MachineState := { frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit] }, memory := mem0 }; let mSafe := mkEp2MiriState bSafe c8SafeFnTy #[⟨.live (.immediate .uninit), some (translateTy c8SafeFnTy)⟩] mach
    let mUnsafe := mkEp2MiriState bUnsafe c8UnsafeFnTy #[⟨.live (.immediate .uninit), some (translateTy c8UnsafeFnTy)⟩] mach; let rSafe := Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosureForState bSafe s0) () mSafe
    let rUnsafe := Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosureForState bUnsafe s0) () mUnsafe
    (∃ s', stepMirFn bSafe s0 = .step s' ∧ get? s'.frame.locals 0 = some (.init (.ptr ⟨65536, 0⟩ 8))) ∧ rSafe.2 = .ok true ∧ miriLocalVal? rSafe.1 0 = some (.live (.immediate (.scalar c8PtrSc))) ∧
    (∃ s', stepMirFn bUnsafe s0 = .step s' ∧ get? s'.frame.locals 0 = some (.init (.ptr ⟨65536, 0⟩ 8))) ∧ rUnsafe.2 = .ok true ∧ miriLocalVal? rUnsafe.1 0 = some (.live (.immediate (.scalar c8PtrSc))) ∧
    stepMirFn bIntr s0 = .fail .ub := by
  refine ⟨⟨_, rfl, rfl⟩, ?_, ?_, ⟨_, rfl, rfl⟩, ?_, ?_, rfl⟩ <;> (with_unfolding_all rfl)
/-- **`C8.2` Witness**: base-hook boundary, lockstep ZST `ClosureFnPointer`
(`Safe` & `Unsafe`) verifying Miri `_0 = c8PtrSc`, `.dead` UB, capturing-
closure rejection, `.uninit` ZST divergence, and
`"ClosureFnPointer(Normal)"` divergence. -/
theorem w_c8_2_closureFnPointer_simulation_capturing_and_divergences :
    let mach := mkEp2AddrMachine c8Aid c8Base; let mem0 : Memory := { emptyMemory with nextAllocId := 65536, callees := [{ c8ClosCallee with argCount := 1 }] }
    let bOk := mkEp2Body "c8_2_ok" [c8SafeFnTy, c8ClosTy] [.assign ⟨0, .nil⟩ (.cast (.pointerCoercion "ClosureFnPointer(Safe)") (.copy ⟨1, .nil⟩) c8SafeFnTy)] c8ClosureLayouts
    let bUnsaf := mkEp2Body "c8_2_unsaf" [c8UnsafeFnTy, c8ClosTy] [.assign ⟨0, .nil⟩ (.cast (.pointerCoercion "ClosureFnPointer(Unsafe)") (.copy ⟨1, .nil⟩) c8UnsafeFnTy)] c8ClosureLayouts
    let sOk : MachineState := { frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit, .init (.aggregate 0 .nil)] }, memory := mem0 }
    let mOk := mkEp2MiriState bOk c8SafeFnTy #[⟨.live (.immediate .uninit), some (translateTy c8SafeFnTy c8ClosureLayouts)⟩, ⟨.live (.immediate .uninit), some (translateTy c8ClosTy c8ClosureLayouts)⟩] mach
    let mUnsaf := mkEp2MiriState bUnsaf c8UnsafeFnTy #[⟨.live (.immediate .uninit), some (translateTy c8UnsafeFnTy c8ClosureLayouts)⟩, ⟨.live (.immediate .uninit), some (translateTy c8ClosTy c8ClosureLayouts)⟩] mach
    let sDead : MachineState := { sOk with frame := { sOk.frame with locals := [.uninit, .dead] } }
    let mDead := mkEp2MiriState bOk c8SafeFnTy #[⟨.live (.immediate .uninit), some (translateTy c8SafeFnTy c8ClosureLayouts)⟩, ⟨.dead, some (translateTy c8ClosTy c8ClosureLayouts)⟩] mach
    let bCap := mkEp2Body "c8_2_cap" [c8SafeFnTy, c8CapClosTy] [.assign ⟨0, .nil⟩ (.cast (.pointerCoercion "ClosureFnPointer(Safe)") (.copy ⟨1, .nil⟩) c8SafeFnTy)] c8ClosureLayouts
    let sCap : MachineState := { frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit, .init (.aggregate 0 [.scalar ⟨7, 4⟩])] }, memory := mem0 }
    let mCap := mkEp2MiriState bCap c8SafeFnTy #[⟨.live (.immediate .uninit), some (translateTy c8SafeFnTy c8ClosureLayouts)⟩, ⟨.live (.immediate .uninit), some (translateTy c8CapClosTy c8ClosureLayouts)⟩] mach
    let sUninit : MachineState := { sOk with frame := { sOk.frame with locals := [.uninit, .uninit] } }
    let bNorm := mkEp2Body "c8_2_norm" [c8SafeFnTy, c8ClosTy] [.assign ⟨0, .nil⟩ (.cast (.pointerCoercion "ClosureFnPointer(Normal)") (.copy ⟨1, .nil⟩) c8SafeFnTy)] c8ClosureLayouts
    let mNorm := mkEp2MiriState bNorm c8SafeFnTy #[⟨.live (.immediate .uninit), some (translateTy c8SafeFnTy c8ClosureLayouts)⟩, ⟨.live (.immediate .uninit), some (translateTy c8ClosTy c8ClosureLayouts)⟩] mach
    let rOk := Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosureForState bOk sOk) () mOk; let rUnsaf := Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosureForState bUnsaf sOk) () mUnsaf
    (∃ msg, (Miri.Interpreter.Step.step (annealStepHooksForState bOk sOk) () mOk).2 = .error (.unsupported msg)) ∧ (∃ s', stepMirFn bOk sOk = .step s' ∧ get? s'.frame.locals 0 = some (.init (.ptr ⟨65536, 0⟩ 8))) ∧
    rOk.2 = .ok true ∧ miriLocalVal? rOk.1 0 = some (.live (.immediate (.scalar c8PtrSc))) ∧ (∃ s', stepMirFn bUnsaf sOk = .step s' ∧ get? s'.frame.locals 0 = some (.init (.ptr ⟨65536, 0⟩ 8))) ∧
    rUnsaf.2 = .ok true ∧ miriLocalVal? rUnsaf.1 0 = some (.live (.immediate (.scalar c8PtrSc))) ∧ stepMirFn bOk sDead = .fail .ub ∧ (Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosureForState bOk sDead) () mDead).2 =
      .error (.undefinedBehavior "read of dead local") ∧
    stepMirFn bCap sCap = .fail .ub ∧ (Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosureForState bCap sCap) () mCap).2 = .error (.invalidProgram "capturing closure in pointer cast") ∧ stepMirFn bOk sUninit = .fail .ub ∧
    (Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosureForState bOk sUninit) () mOk).2 = .ok true ∧ stepMirFn bNorm sOk = .unsupported ∧
    (Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosureForState bNorm sOk) () mNorm).2 = .ok true := by
  refine ⟨?_, ⟨_, rfl, rfl⟩, ?_, ?_, ⟨_, rfl, rfl⟩, ?_, ?_, rfl, ?_, rfl, ?_, rfl, ?_, rfl, ?_⟩ <;> first | (with_unfolding_all exact ⟨_, rfl⟩) | (with_unfolding_all rfl)
/-- **`C8.3` Witness**: `UnsafeFnPointer` dispatch, base-hook boundary,
lockstep safe-to-unsafe (checking Miri `_0 = c8PtrSc`), 4 UB regimes,
strict-check divergences, and fail-closed unrecognized-tag check on both
Trusted and overlay. -/
theorem w_c8_3_unsafeFnPointer_simulation_ub_and_divergences :
    let mscOff4 := Miri.Memory.Scalar.fromPointer annealTargetDataLayout ⟨Miri.ABI.Size.ofBytes (c8Base + 4), .concrete c8Aid .one⟩
    let fnMem : Memory :=
      { emptyMemory with
        callees := [{ c8ClosCallee with argCount := 1 }], fnPtrs := [{ allocId := 65536, defPath := "c8_zst_clos", typeArgs := .nil, fnSig := some c8SafeFnTy.kind }] }
    let mach := mkEp2AddrMachine c8Aid c8Base; let bOk := mkEp2Body "c8_ufn_ok" [c8UnsafeFnTy, c8SafeFnTy] [.assign ⟨0, .nil⟩ (.cast (.pointerCoercion "UnsafeFnPointer") (.copy ⟨1, .nil⟩) c8UnsafeFnTy)]
    let sOk : MachineState := { frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit, .init (.ptr ⟨65536, 0⟩ 8)] }, memory := fnMem }
    let mOk := mkEp2MiriState bOk c8UnsafeFnTy #[⟨.live (.immediate .uninit), some (translateTy c8UnsafeFnTy)⟩, ⟨.live (.immediate (.scalar c8PtrSc)), some (translateTy c8SafeFnTy)⟩] mach
    let sDead : MachineState := { sOk with frame := { sOk.frame with locals := [.uninit, .dead] } }
    let mDead := mkEp2MiriState bOk c8UnsafeFnTy #[⟨.live (.immediate .uninit), some (translateTy c8UnsafeFnTy)⟩, ⟨.dead, some (translateTy c8SafeFnTy)⟩] mach
    let sUninit : MachineState := { sOk with frame := { sOk.frame with locals := [.uninit, .uninit] } }
    let mUninit := mkEp2MiriState bOk c8UnsafeFnTy #[⟨.live (.immediate .uninit), some (translateTy c8UnsafeFnTy)⟩, ⟨.live (.immediate .uninit), some (translateTy c8SafeFnTy)⟩] mach
    let sInt : MachineState := { sOk with frame := { sOk.frame with locals := [.uninit, .init (.scalar ⟨0x2000, 8⟩)] } }
    let mInt := mkEp2MiriState bOk c8UnsafeFnTy #[⟨.live (.immediate .uninit), some (translateTy c8UnsafeFnTy)⟩, ⟨.live (.immediate (.scalar (miriScalarUInt 0x2000 8))), some (translateTy c8SafeFnTy)⟩] mach
    let sOff4 : MachineState := { sOk with frame := { sOk.frame with locals := [.uninit, .init (.ptr ⟨65536, 4⟩ 8)] } }
    let mOff4 := mkEp2MiriState bOk c8UnsafeFnTy #[⟨.live (.immediate .uninit), some (translateTy c8UnsafeFnTy)⟩, ⟨.live (.immediate (.scalar mscOff4)), some (translateTy c8SafeFnTy)⟩] mach
    let bAlready := mkEp2Body "c8_ufn_already" [c8UnsafeFnTy, c8UnsafeFnTy] [.assign ⟨0, .nil⟩ (.cast (.pointerCoercion "UnsafeFnPointer") (.copy ⟨1, .nil⟩) c8UnsafeFnTy)]
    let mAlready := mkEp2MiriState bAlready c8UnsafeFnTy #[⟨.live (.immediate .uninit), some (translateTy c8UnsafeFnTy)⟩, ⟨.live (.immediate (.scalar c8PtrSc)), some (translateTy c8UnsafeFnTy)⟩] mach
    let bBadSig := mkEp2Body "c8_ufn_badsig" [c8BadSigFnTy, c8SafeFnTy] [.assign ⟨0, .nil⟩ (.cast (.pointerCoercion "UnsafeFnPointer") (.copy ⟨1, .nil⟩) c8BadSigFnTy)]
    let mBadSig := mkEp2MiriState bBadSig c8BadSigFnTy #[⟨.live (.immediate .uninit), some (translateTy c8BadSigFnTy)⟩, ⟨.live (.immediate (.scalar c8PtrSc)), some (translateTy c8SafeFnTy)⟩] mach
    let bUnrecRaw := mkEp2Body "c8_unrec_raw" [ep2RawU8PtrTy, ep2RawMutU8PtrTy] [.assign ⟨0, .nil⟩ (.cast (.pointerCoercion "CustomUnknownCoercion") (.copy ⟨1, .nil⟩) ep2RawU8PtrTy)]
    let mUnrecRaw := mkEp2MiriState bUnrecRaw ep2RawU8PtrTy #[⟨.live (.immediate .uninit), some (translateTy ep2RawU8PtrTy)⟩, ⟨.live (.immediate (.scalar c8PtrSc)), some (translateTy ep2RawMutU8PtrTy)⟩] mach
    let rOk := Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosureForState bOk sOk) () mOk
    isReifyFnPointerCoercion "UnsafeFnPointer" = true ∧ (∃ msg, (Miri.Interpreter.Step.step (annealStepHooksForState bOk sOk) () mOk).2 = .error (.unsupported msg)) ∧
    (∃ s', stepMirFn bOk sOk = .step s' ∧ get? s'.frame.locals 0 = some (.init (.ptr ⟨65536, 0⟩ 8))) ∧ rOk.2 = .ok true ∧ miriLocalVal? rOk.1 0 = some (.live (.immediate (.scalar c8PtrSc))) ∧ stepMirFn bOk sDead = .fail .ub ∧
    (Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosureForState bOk sDead) () mDead).2 = .error (.undefinedBehavior "read of dead local") ∧ stepMirFn bOk sUninit = .fail .ub ∧
    (Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosureForState bOk sUninit) () mUninit).2 = .error (.undefinedBehavior "read of uninitialized local") ∧ stepMirFn bOk sInt = .fail .ub ∧
    (Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosureForState bOk sInt) () mInt).2 = .error (.undefinedBehavior "DanglingIntPointer") ∧ stepMirFn bOk sOff4 = .fail .ub ∧
    (Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosureForState bOk sOff4) () mOff4).2 = .error (.undefinedBehavior "InvalidFunctionPointer") ∧ stepMirFn bAlready sOk = .fail .ub ∧
    (Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosureForState bAlready sOk) () mAlready).2 = .ok true ∧ stepMirFn bBadSig sOk = .fail .ub ∧
    (Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosureForState bBadSig sOk) () mBadSig).2 = .ok true ∧ stepMirFn bUnrecRaw sOk = .unsupported ∧
    (Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosureForState bUnrecRaw sOk) () mUnrecRaw).2 = .error (.invalidProgram "borrowck-only pointer coercion in runtime MIR") := by
  refine ⟨rfl, ?_, ⟨_, rfl, rfl⟩, ?_, ?_, rfl, ?_, rfl, ?_, rfl, ?_, rfl, ?_, rfl, ?_, rfl, ?_, rfl, ?_⟩ <;> first | (with_unfolding_all exact ⟨_, rfl⟩) | (with_unfolding_all rfl)
/-- **`C8.4` & `C8.5` Canonical Runtime-MIR Boundary**: vendored `Cast.cast`
rejects borrowck-only `MutToConstPointer` and `ArrayToPointer`. -/
theorem miri_cast_mutToConst_and_arrayToPointer_canonical_boundary :
    let b := mkEp2Body "c8_canon_boundary" [ep2RawU8PtrTy, ep2RawMutU8PtrTy] []; let hooks := annealCastHooksUnwindFnPtrClosure b .nil
    let src : Miri.Interpreter.OpTy AnnealProv := ⟨.immediate (.scalar c8PtrSc), translateTy ep2RawMutU8PtrTy⟩
    let dst : Miri.Interpreter.RuntimePlace AnnealProv := ⟨.local 0 0 none (.ofAllocationToken 0), translateTy ep2RawU8PtrTy⟩; let st := mkEp2MiriState b ep2RawU8PtrTy #[⟨.live (.immediate .uninit), some (translateTy ep2RawU8PtrTy)⟩]
    (Miri.Interpreter.runRvalue (Miri.Interpreter.Cast.cast hooks () 16 src (.PointerCoercion .MutToConstPointer .Implicit) (encodeTyId ep2RawU8PtrTy) dst) st).2 =
      .error (.invalidProgram "borrowck-only pointer coercion in runtime MIR") ∧
    (Miri.Interpreter.runRvalue (Miri.Interpreter.Cast.cast hooks () 16 src (.PointerCoercion .ArrayToPointer .Implicit) (encodeTyId ep2RawU8PtrTy) dst) st).2 =
      .error (.invalidProgram "borrowck-only pointer coercion in runtime MIR") := by
  constructor <;> (with_unfolding_all rfl)
/-- **`C8.4` Witness**: thin pointer, scalar-addr, 16-byte wide slice, and
16-byte wide `dyn Trait` `MutToConstPointer` checking exact Miri `_0`
outputs, plus mismatched thin-to-wide shape fault and const-to-const
divergence. -/
theorem w_c8_4_mutToConstPointer_thin_wideSlice_and_wideDyn :
    let mutSliceTy : Ty := { kind := .rawPtr .mut (.slice (.uint .u8)), layoutIdx := 0 }; let constSliceTy : Ty := { kind := .rawPtr .not (.slice (.uint .u8)), layoutIdx := 0 }
    let mutDynTy : Ty := { kind := .rawPtr .mut (.dynamic "MyTrait"), layoutIdx := 0 }; let constDynTy : Ty := { kind := .rawPtr .not (.dynamic "MyTrait"), layoutIdx := 0 }; let vtAid : Miri.Memory.AllocId := ⟨65537, by decide⟩
    let vtBase : UInt64 := annealStackBaseAddr vtAid
    let mach : AnnealMachine :=
      { AnnealMachine.empty with
        addresses := { AnnealMachine.empty.addresses with baseAddr := #[⟨c8Aid, c8Base⟩, ⟨vtAid, vtBase⟩] } }
    let vtSc := Miri.Memory.Scalar.fromPointer annealTargetDataLayout ⟨Miri.ABI.Size.ofBytes vtBase, .concrete vtAid .one⟩
    let bThin := mkEp2Body "c8_4_thin" [ep2RawU8PtrTy, ep2RawMutU8PtrTy] [.assign ⟨0, .nil⟩ (.cast (.pointerCoercion "MutToConstPointer") (.copy ⟨1, .nil⟩) ep2RawU8PtrTy)]
    let sThinPtr : MachineState := { frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit, .init (.ptr ⟨65536, 0⟩ 8)] }, memory := emptyMemory }
    let mThinPtr := mkEp2MiriState bThin ep2RawU8PtrTy #[⟨.live (.immediate .uninit), some (translateTy ep2RawU8PtrTy)⟩, ⟨.live (.immediate (.scalar c8PtrSc)), some (translateTy ep2RawMutU8PtrTy)⟩] mach
    let sThinAddr : MachineState := { frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit, .init (.scalar ⟨0x4000, 8⟩)] }, memory := emptyMemory }
    let mThinAddr := mkEp2MiriState bThin ep2RawU8PtrTy #[⟨.live (.immediate .uninit), some (translateTy ep2RawU8PtrTy)⟩, ⟨.live (.immediate (.scalar (miriScalarUInt 0x4000 8))), some (translateTy ep2RawMutU8PtrTy)⟩] mach
    let bSlice := mkEp2Body "c8_4_slice" [constSliceTy, mutSliceTy] [.assign ⟨0, .nil⟩ (.cast (.pointerCoercion "MutToConstPointer") (.copy ⟨1, .nil⟩) constSliceTy)]
    let sSlice : MachineState := { frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit, .init (.aggregate 0 [.ptr ⟨65536, 0⟩ 8, .scalar ⟨3, 8⟩])] }, memory := emptyMemory }
    let mSlice := mkEp2MiriState bSlice constSliceTy #[⟨.live (.immediate .uninit), some (translateTyOverlay constSliceTy)⟩, ⟨.live (.immediate (.scalarPair c8PtrSc (miriScalarUInt 3 8))), some (translateTyOverlay mutSliceTy)⟩] mach
    let bDyn := mkEp2Body "c8_4_dyn" [constDynTy, mutDynTy] [.assign ⟨0, .nil⟩ (.cast (.pointerCoercion "MutToConstPointer") (.copy ⟨1, .nil⟩) constDynTy)]
    let sDyn : MachineState := { frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit, .init (.aggregate 0 [.ptr ⟨65536, 0⟩ 8, .ptr ⟨65537, 0⟩ 8])] }, memory := emptyMemory }
    let mDyn := mkEp2MiriState bDyn constDynTy #[⟨.live (.immediate .uninit), some (translateTyOverlay constDynTy)⟩, ⟨.live (.immediate (.scalarPair c8PtrSc vtSc)), some (translateTyOverlay mutDynTy)⟩] mach
    let sDynUninit : MachineState := { frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit, .uninit] }, memory := emptyMemory }
    let mDynUninit := mkEp2MiriState bDyn constDynTy #[⟨.live (.immediate .uninit), some (translateTyOverlay constDynTy)⟩, ⟨.live (.immediate .uninit), some (translateTyOverlay mutDynTy)⟩] mach
    let bBadShape := mkEp2Body "c8_4_badshape" [constSliceTy, ep2RawMutU8PtrTy] [.assign ⟨0, .nil⟩ (.cast (.pointerCoercion "MutToConstPointer") (.copy ⟨1, .nil⟩) constSliceTy)]
    let mBadShape := mkEp2MiriState bBadShape constSliceTy #[⟨.live (.immediate .uninit), some (translateTyOverlay constSliceTy)⟩, ⟨.live (.immediate (.scalar c8PtrSc)), some (translateTy ep2RawMutU8PtrTy)⟩] mach
    let bConstConst := mkEp2Body "c8_4_constconst" [ep2RawU8PtrTy, ep2RawU8PtrTy] [.assign ⟨0, .nil⟩ (.cast (.pointerCoercion "MutToConstPointer") (.copy ⟨1, .nil⟩) ep2RawU8PtrTy)]
    let mConstConst := mkEp2MiriState bConstConst ep2RawU8PtrTy #[⟨.live (.immediate .uninit), some (translateTy ep2RawU8PtrTy)⟩, ⟨.live (.immediate (.scalar c8PtrSc)), some (translateTy ep2RawU8PtrTy)⟩] mach
    let rThin := Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosure bThin) () mThinPtr; let rAddr := Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosure bThin) () mThinAddr
    let rSlice := Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosure bSlice) () mSlice; let rDyn := Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosure bDyn) () mDyn
    (∃ s', stepMirFn bThin sThinPtr = .step s' ∧ get? s'.frame.locals 0 = some (.init (.ptr ⟨65536, 0⟩ 8))) ∧ rThin.2 = .ok true ∧ miriLocalVal? rThin.1 0 = some (.live (.immediate (.scalar c8PtrSc))) ∧
    (∃ s', stepMirFn bThin sThinAddr = .step s' ∧ get? s'.frame.locals 0 = some (.init (.scalar ⟨0x4000, 8⟩))) ∧ rAddr.2 = .ok true ∧ miriLocalVal? rAddr.1 0 = some (.live (.immediate (.scalar (miriScalarUInt 0x4000 8)))) ∧
    (∃ s', stepMirFn bSlice sSlice = .step s' ∧ get? s'.frame.locals 0 = some (.init (.aggregate 0 [.ptr ⟨65536, 0⟩ 8, .scalar ⟨3, 8⟩]))) ∧ rSlice.2 = .ok true ∧
    miriLocalVal? rSlice.1 0 = some (.live (.immediate (.scalarPair c8PtrSc (miriScalarUInt 3 8)))) ∧ (∃ s', stepMirFn bDyn sDyn = .step s' ∧
      get? s'.frame.locals 0 = some (.init (.aggregate 0 [.ptr ⟨65536, 0⟩ 8, .ptr ⟨65537, 0⟩ 8]))) ∧
    rDyn.2 = .ok true ∧ miriLocalVal? rDyn.1 0 = some (.live (.immediate (.scalarPair c8PtrSc vtSc))) ∧ stepMirFn bDyn sDynUninit = .fail .ub ∧ (Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosure bDyn) () mDynUninit).2 =
      .error (.undefinedBehavior "read of uninitialized local") ∧
    stepMirFn bBadShape sThinPtr = .fail .ub ∧ (Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosure bBadShape) () mBadShape).2 = .error (.invalidProgram "fat-to-thin pointer size mismatch") ∧
    stepMirFn bConstConst sThinPtr = .fail .ub ∧ (Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosure bConstConst) () mConstConst).2 = .ok true := by
  refine ⟨⟨_, rfl, rfl⟩, ?_, ?_, ⟨_, rfl, rfl⟩, ?_, ?_, ⟨_, rfl, rfl⟩, ?_, ?_, ⟨_, rfl, rfl⟩, ?_, ?_, rfl, ?_, rfl, ?_, rfl, ?_⟩ <;> (with_unfolding_all rfl)
/-- **`C8.5` Witness**: `ArrayToPointer` across untracked pointer, 8-byte
scalar address (`0x4000`), active stack borrow (`deriveStackElemThinPtr`),
and eager `.disabled`-tag UB vs. Miri cast-time tag preservation. -/
theorem w_c8_5_arrayToPointer_borrows_and_disabled_divergence :
    let arr2U8Ty : Ty := { kind := .array (.uint .u8) 2, layoutIdx := 0 }; let ptrArrTy : Ty := { kind := .rawPtr .not (.array (.uint .u8) 2), layoutIdx := 0 }
    let bArr := mkEp2Body "c8_5_arr" [ep2RawU8PtrTy, ptrArrTy, arr2U8Ty] [.assign ⟨0, .nil⟩ (.cast (.pointerCoercion "ArrayToPointer") (.copy ⟨1, .nil⟩) ep2RawU8PtrTy)]; let mach := mkEp2AddrMachine c8Aid c8Base
    let arrVal : Value := .aggregate 0 [.scalar ⟨11, 1⟩, .scalar ⟨22, 1⟩]
    let sUntracked : MachineState := { frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit, .init (.ptr ⟨65536, 0⟩ 8), .init arrVal] }, memory := emptyMemory }
    let mPtr := mkEp2MiriState bArr ep2RawU8PtrTy #[⟨.live (.immediate .uninit), some (translateTy ep2RawU8PtrTy)⟩, ⟨.live (.immediate (.scalar c8PtrSc)), some (translateTy ptrArrTy)⟩,
        ⟨.live (.immediate .uninit), some (translateTy arr2U8Ty)⟩] mach
    let sAddr : MachineState := { frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit, .init (.scalar ⟨0x4000, 8⟩), .init arrVal] }, memory := emptyMemory }
    let mAddr := mkEp2MiriState bArr ep2RawU8PtrTy #[⟨.live (.immediate .uninit), some (translateTy ep2RawU8PtrTy)⟩, ⟨.live (.immediate (.scalar (miriScalarUInt 0x4000 8))), some (translateTy ptrArrTy)⟩,
        ⟨.live (.immediate .uninit), some (translateTy arr2U8Ty)⟩] mach
    let activeEntry : BorrowEntry := { tag := 1, parentTag := none, targetLocal := 2, targetProjection := .nil, perm := .frozen, protector := none, targetFrameDepth := 0 }
    let sBorrowed : MachineState :=
      { sUntracked with
        frame := { sUntracked.frame with locals := [.uninit, .init (.ptr ⟨1, 0⟩ 8), .init arrVal] }, memory := { emptyMemory with borrows := [activeEntry], nextTag := 2, nextAllocId := 2 } }
    let sDisabled : MachineState := { sBorrowed with memory := { sBorrowed.memory with borrows := [{ activeEntry with perm := .disabled }] } }
    let disTag : Miri.Memory.BorTag := ⟨7, by decide⟩
    let disSc := Miri.Memory.Scalar.fromPointer annealTargetDataLayout ⟨Miri.ABI.Size.ofBytes c8Base, .concrete c8Aid disTag⟩
    let btDis : Miri.Interpreter.MachineHooks.BorrowState := { global := { protectedTags := { entries := #[] }, rootPointerTags := #[(c8Aid, .one)] }, retagMode := .Default }
    let mDis := mkEp2MiriState bArr ep2RawU8PtrTy #[⟨.live (.immediate .uninit), some (translateTy ep2RawU8PtrTy)⟩, ⟨.live (.immediate (.scalar disSc)), some (translateTy ptrArrTy)⟩,
        ⟨.live (.immediate .uninit), some (translateTy arr2U8Ty)⟩]
      { mach with borrowTracker := some btDis }
    let rPtr := Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosure bArr) () mPtr; let rAddr := Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosure bArr) () mAddr
    let rDis := Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosure bArr) () mDis
    (∃ s', stepMirFn bArr sUntracked = .step s' ∧ get? s'.frame.locals 0 = some (.init (.ptr ⟨65536, 0⟩ 8))) ∧ rPtr.2 = .ok true ∧ miriLocalVal? rPtr.1 0 = some (.live (.immediate (.scalar c8PtrSc))) ∧
    (∃ s', stepMirFn bArr sAddr = .step s' ∧ get? s'.frame.locals 0 = some (.init (.scalar ⟨0x4000, 8⟩))) ∧ rAddr.2 = .ok true ∧ miriLocalVal? rAddr.1 0 = some (.live (.immediate (.scalar (miriScalarUInt 0x4000 8)))) ∧
    (∃ s', stepMirFn bArr sBorrowed = .step s' ∧ get? s'.frame.locals 0 = some (.init (.ptr ⟨2, 0⟩ 8)) ∧ s'.memory.borrows.length = 2 ∧ (lookupBorrow s'.memory.borrows 2).map (fun e => (e.targetLocal, e.targetProjection, e.perm)) =
        some (2, [.subslice 0 2 false], .frozen)) ∧
    stepMirFn bArr sDisabled = .fail .ub ∧ rDis.2 = .ok true ∧ miriLocalVal? rDis.1 0 = some (.live (.immediate (.scalar disSc))) := by
  refine ⟨⟨_, rfl, rfl⟩, ?_, ?_, ⟨_, rfl, rfl⟩, ?_, ?_, ⟨_, rfl, rfl, rfl, rfl⟩, rfl, ?_, ?_⟩ <;> (with_unfolding_all rfl)
/-- **`C8` End-to-End 5-Step Witness**: closure construction ->
`ClosureFnPointer(Safe)` -> indirect call -> callee body -> `return_`. -/
theorem w_c8_end_to_end_closure_coercion_and_indirect_call :
    let callerBody : CapturedMir :=
      { defPath := "c8_e2e_caller", phase := .runtimePostCleanup, role := .subject, argCount := 0, localDecls := [ep2U32Ty, c8SafeFnTy, c8ClosTy].map mkEp2Decl, basicBlocks :=
          [{ statements :=
               [mkEp2Stmt (.assign ⟨2, .nil⟩ (.aggregate (.closure "c8_zst_clos") .nil)), mkEp2Stmt (.assign ⟨1, .nil⟩ (.cast (.pointerCoercion "ClosureFnPointer(Safe)") (.copy ⟨2, .nil⟩) c8SafeFnTy))],
             terminator := mkEp2Term (.call (.move ⟨1, .nil⟩) [.constant { ty := ep2U32Ty, val := .scalar (.int ⟨42, 4⟩) }] ⟨0, .nil⟩ (some 1) .continue_), isCleanup := false },
           { statements := .nil, terminator := mkEp2Term .return_, isCleanup := false }],
        fnAbi := Witness.fnAbi0, layouts := c8ClosureLayouts, allocations := .nil }
    let s0 : MachineState := { frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit, .uninit, .uninit] }, memory := { emptyMemory with nextAllocId := 65536, callees := [{ c8ClosCallee with argCount := 1 }] } }
    let m0 := mkEp2MiriState callerBody ep2U32Ty #[⟨.live (.immediate .uninit), some (translateTy ep2U32Ty c8ClosureLayouts)⟩, ⟨.live (.immediate .uninit), some (translateTy c8SafeFnTy c8ClosureLayouts)⟩,
        ⟨.live (.immediate .uninit), some (translateTy c8ClosTy c8ClosureLayouts)⟩]
      (mkEp2AddrMachine c8Aid c8Base)
    ∃ s1 s2 s3 s4 s5, stepMirFn callerBody s0 = .step s1 ∧ stepMirFn callerBody s1 = .step s2 ∧ stepMirFn callerBody s2 = .step s3 ∧ stepMirFn callerBody s3 = .step s4 ∧ stepMirFn callerBody s4 = .step s5 ∧ s5.frame.blockIdx = 1 ∧
      get? s5.frame.locals 0 = some (.init (.scalar ⟨42, 4⟩)) ∧
      let r1 := Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosureForState callerBody s0) () m0; let r2 := Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosureForState callerBody s1) () r1.1
      let r3 := Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosureForState callerBody s2) () r2.1; let r4 := Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosureForState callerBody s3) () r3.1
      let r5 := Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosureForState callerBody s4) () r4.1
      r1.2 = .ok true ∧ r2.2 = .ok true ∧ r3.2 = .ok true ∧ r4.2 = .ok true ∧ r5.2 = .ok true ∧ r5.1.stack.frames.size = 1 ∧ miriLocalVal? r5.1 0 = some (.live (.immediate (.scalar (miriScalarUInt 42 4)))) := by
  refine ⟨_, _, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  with_unfolding_all exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
end C8SimulationsAndWitnesses

/-! ## Section 7. `C9` (`ProjectionElem.unwrapUnsafeBinder`) -/
/-- **`C9` Stage-1 Value-Projection Transparency**. -/
theorem readProjectedValue_unwrapUnsafeBinder (locals : List LocalSlot) (val : Value) (innerTy : Ty) (rest : List ProjectionElem) : readProjectedValue locals val (.unwrapUnsafeBinder innerTy :: rest) =
      readProjectedValue locals val rest := by
  cases val <;> rfl
/-- **`C9` Stage-1 Write-Projection Transparency**. -/
theorem writeProjectedValue_unwrapUnsafeBinder (locals : List LocalSlot) (val : Value) (innerTy : Ty) (rest : List ProjectionElem) (newVal : Value) : writeProjectedValue locals val (.unwrapUnsafeBinder innerTy :: rest) newVal =
      writeProjectedValue locals val rest newVal := by
  cases val <;> rfl
/-- **`C9` Scalar-Compatibility Transparency**. -/
theorem isScalarCompatibleProj_unwrapUnsafeBinder (innerTy : Ty) (rest : List ProjectionElem) : isScalarCompatibleProj (.unwrapUnsafeBinder innerTy :: rest) = isScalarCompatibleProj rest := rfl
/-- **`C9` Vendored `Miri.Interpreter.project` Equivalence**. -/
theorem miri_project_unwrapUnsafeBinder_eq_transmute (cx : Miri.Interpreter.ProjectionCx AnnealProv) (base : Miri.Interpreter.OpTy AnnealProv) (ty : Miri.MIR.TyId) : Miri.Interpreter.project cx base (.UnwrapUnsafeBinder ty) =
      (cx.layoutOf ty).bind (base.transmute cx) := rfl
section C9UnwrapUnsafeBinderSimulations
private def c9BinderU32Layout : TypeLayout :=
  { size := { bytes := 4 }, align := { bytes := 4 },
    backendRepr := .scalar (.initialized (.int 32 false) { start := 0, end_ := 0xFFFFFFFF }), variants := .single 0, fields := .arbitrary [{ bytes := 0 }] [0], fieldLayouts := .nil, isUninhabited := false }
private def c9BinderPtrLayout : TypeLayout :=
  { size := { bytes := 8 }, align := { bytes := 8 },
    backendRepr := .scalar (.initialized (.pointer 0) { start := 0, end_ := 0xFFFFFFFFFFFFFFFF }), variants := .single 0, fields := .arbitrary [{ bytes := 0 }] [0], fieldLayouts := .nil, isUninhabited := false }
private def c9BinderArrLayout : TypeLayout := { size := { bytes := 8 }, align := { bytes := 4 }, backendRepr := .memory, variants := .single 0, fields := .array { bytes := 4 } 2, fieldLayouts := .nil, isUninhabited := false }
private def c9Layouts : LayoutTable := { emptyLayoutTable with entries := [c9BinderU32Layout, c9BinderPtrLayout, c9BinderArrLayout] }
private def c9BinderU32Ty : Ty := { kind := .adt "UnsafeBinderU32" [.uint .u32], layoutIdx := 0 }
private def c9BinderPtrTy : Ty := { kind := .adt "UnsafeBinderPtr" [.rawPtr .not (.uint .u32)], layoutIdx := 1 }
private def c9RawU32PtrTy : Ty := { kind := .rawPtr .not (.uint .u32), layoutIdx := 0 }
private def c9Arr2U32Ty : Ty := { kind := .array (.uint .u32) 2, layoutIdx := 2 }
/-- **`C9` Universal Stage-1 `evalOperand` Unwrap-Transparency**. -/
theorem evalOperand_copy_unwrapUnsafeBinder_eq (locals : List LocalSlot) (idx : Local) (innerTy : Ty) (rest : List ProjectionElem) (borrows : List BorrowEntry) (globals : List CapturedAllocation)
    (layouts : LayoutTable) (callerLocals : List LocalSlot) (localDecls : List LocalDecl) (callStack : List SavedCallerFrame) (hno_union : placeTouchesUnion localDecls layouts ⟨idx, .unwrapUnsafeBinder innerTy :: rest⟩ = false) :
    evalOperand locals (.copy ⟨idx, .unwrapUnsafeBinder innerTy :: rest⟩) borrows globals layouts callerLocals localDecls callStack =
      match get? locals idx with
      | some (.init rootVal) =>
          match readProjectedValue locals rootVal rest with
          | .ok fieldVal => .ok fieldVal locals
          | .ub => .ub
          | .unsupported => .unsupported
      | _ => .ub := by
  unfold evalOperand; dsimp only
  cases get? locals idx with
  | none => rfl
  | some sl =>
    cases sl with
    | dead | uninit => rfl
    | init rootVal =>
      dsimp only; rw [hno_union]; dsimp only; rw [readProjectedValue_unwrapUnsafeBinder]; rfl
private theorem annealResolveAndCacheLocalLayoutOverlay_eq {localDecls : List LocalDecl} {layouts : LayoutTable} {idx : Nat} {decl : LocalDecl} {known : Option Miri.Interpreter.LocalLayout} {m : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit} {v : Miri.Interpreter.LocalValue AnnealProv} {c : Option Miri.Interpreter.LocalLayout} (hframes : m.stack.frames = #[tf]) (hlt : idx < tf.locals.size)
    (hdecl : get? localDecls idx = some decl) (hnw : isWideOverlayPlace localDecls ⟨idx, #[]⟩ = false ∧ translateTyOverlay decl.ty layouts = translateTy decl.ty layouts) (hmls : tf.locals[idx]'hlt = ⟨v, c⟩)
    (hc : ∀ l, c = some l → l = translateTy decl.ty layouts) :
    let tf' := cacheFrameLocalLayout tf idx hlt (translateTy decl.ty layouts)
    annealResolveAndCacheLocalLayoutOverlay localDecls layouts idx known m = .ok (tf', translateTy decl.ty layouts) { stack := ⟨#[tf']⟩, machine := m.machine } ∧ tf'.getLocal idx = .ok ⟨v, some (translateTy decl.ty layouts)⟩ := by
  intro tf'; have hmls? : tf.locals[idx]? = some ⟨v, c⟩ := by rw [Array.getElem?_eq_getElem hlt, hmls]
  have hget := frame_getLocal_of_getElem? tf idx _ hmls?
  have hcache : tf.getOrCacheLocalLayout idx (translateTy decl.ty layouts) = .ok (tf', translateTy decl.ty layouts) := by
    unfold Miri.Interpreter.Frame.getOrCacheLocalLayout; rw [hget]; dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
    cases hc' : c with
    | none =>
      subst hc'; let newLoc : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout := { value := v, layout := some (translateTy decl.ty layouts) }
      have hfr_eq : { tf with locals := tf.locals.set idx newLoc hlt } = tf' := by
        dsimp [tf', cacheFrameLocalLayout, newLoc]; congr 1; apply Array.ext_getElem?; intro k
        by_cases hk : idx = k
        · subst hk; simp [Array.getElem?_set_self hlt, hmls]
        · simp [Array.getElem?_set_ne hlt hk]
      rw [dite_eq_left_of_eq_true (eq_true hlt)]; dsimp only [Pure.pure, Except.pure]; rw [hfr_eq]
    | some l =>
      have hl := hc l hc'; subst hl; subst hc'
      have hfr_eq : tf = tf' := by
        dsimp [tf', cacheFrameLocalLayout]; cases tf with | mk b bi fi ex rc rp li locs vl tc lo =>
        dsimp at hlt hmls ⊢; congr 1; apply Array.ext_getElem?; intro k
        by_cases hk : idx = k
        · subst hk; rw [Array.getElem?_set_self hlt, Array.getElem?_eq_getElem hlt, hmls]
        · simp [Array.getElem?_set_ne hlt hk]
      dsimp only [Pure.pure, Except.pure]; rw [hfr_eq]
  have hget' : tf'.getLocal idx = .ok ⟨v, some (translateTy decl.ty layouts)⟩ := by
    apply frame_getLocal_of_getElem?; dsimp [tf', cacheFrameLocalLayout]
    rw [Array.getElem?_set_self hlt, hmls]
  refine ⟨?_, hget'⟩
  cases m with | mk st mach =>
  obtain ⟨frs⟩ := st; dsimp only at hframes; subst hframes; have hfr_sz : tf'.locals.size = tf.locals.size := by simp [tf', cacheFrameLocalLayout]
  have hopt : (Option.map (fun x => translateTyOverlay x.ty layouts) (some decl) <|> c <|> known) = some (translateTy decl.ty layouts) := by simp only [Option.map_some, hnw.2]; rfl
  unfold annealResolveAndCacheLocalLayoutOverlay
  dsimp only [Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, get, getThe, MonadStateOf.get, EStateM.get, set, MonadStateOf.set, EStateM.set]; rw [stack_currentFrame?_singleton ⟨#[tf]⟩ tf rfl]; dsimp only
  rw [hget]; dsimp only [Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]; rw [hdecl, hopt]; dsimp only [Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]; rw [hcache]; dsimp only
  simp [hfr_sz, hlt, hnw.1, EStateM.bind, EStateM.pure, EStateM.set]
private theorem readProjectedValue_nil (ls : List LocalSlot) (v : Value) : readProjectedValue ls v .nil = .ok v := by cases v <;> rfl
private def ep2PlaceLiftResult {A S : Type} (value : Except Miri.Interpreter.StepError A) : Miri.Interpreter.PlaceM S A := match value with | .ok value => pure value | .error error => throw error
private def ep2PlaceSizeResult {A S : Type} (value : Except Miri.ABI.SizeError A) : Miri.Interpreter.PlaceM S A := ep2PlaceLiftResult (value.mapError fun error => .invalidProgram s!"place size: {repr error}")
private theorem ep2_offsetWithMeta_local_zero (h : Miri.Interpreter.PlaceProjectionHooks AnnealProv AnnealStepState Unit Unit) (dstIdx : Nat) (id0 : Miri.Interpreter.LocalsIdentity)
    (dstLay srcLay : Miri.Interpreter.LocalLayout) (st : AnnealStepState) (mode : Miri.Interpreter.OffsetMode) (hs2 : srcLay.layout.isSized = true) (hsz : dstLay.layout.size = srcLay.layout.size) :
    Miri.Interpreter.PlaceDynamic.offsetWithMeta h () ⟨.local 0 dstIdx none id0, dstLay⟩ Miri.ABI.Size.ZERO mode .none srcLay st = .ok ⟨.local 0 dstIdx (some Miri.ABI.Size.ZERO) id0, srcLay⟩ st := by
  have hza : ∀ sz : Miri.ABI.Size, Miri.ABI.Size.ZERO.add sz = .ok sz := fun sz => by cases sz; unfold Miri.ABI.Size.add Miri.ABI.Size.ZERO; simp [UInt64.lt_iff_toNat_lt]; rfl
  unfold Miri.Interpreter.PlaceDynamic.offsetWithMeta; simp only [Bind.bind, EStateM.bind, Pure.pure, hs2, hsz, hza, Miri.Interpreter.MemPlaceMeta.hasMeta, Option.getD_none, Bool.not_true, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
  refine Eq.trans (b := EStateM.bind (ep2PlaceSizeResult (Except.ok srcLay.layout.size)) (fun bound =>
      if bound.bytes > srcLay.layout.size.bytes then EStateM.bind (throw (.invalidProgram "local projection exceeds enclosing place")) fun (_ : Unit) => EStateM.bind (ep2PlaceSizeResult (Except.ok Miri.ABI.Size.ZERO)) fun offset =>
            EStateM.pure ⟨.local 0 dstIdx (some offset) id0, srcLay⟩
      else EStateM.bind (ep2PlaceSizeResult (Except.ok Miri.ABI.Size.ZERO)) fun offset => EStateM.pure ⟨.local 0 dstIdx (some offset) id0, srcLay⟩) st) ?_ ?_
  · with_unfolding_all rfl
  · simp only [ep2PlaceSizeResult, ep2PlaceLiftResult, Except.mapError, pure, Pure.pure, EStateM.pure, EStateM.bind, UInt64.lt_irrefl, ↓reduceIte]
/-- **`C9` Universal Read Simulation
(`step_unwrapUnsafeBinder_copy_simulation`)**: proves `.dead`/`.uninit` UB
equivalence and positive lockstep reads through vendored
`Miri.Interpreter.project` (`base.transmute`) for arbitrary equal-size non-
ZST immediate binder and inner layouts. -/
theorem step_unwrapUnsafeBinder_copy_simulation {body : CapturedMir} {s : MachineState} {m : AnnealStepState} {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {srcIdx dstIdx : Local} {srcDecl dstDecl : LocalDecl} {bb : BasicBlockData} {stmt : Statement} (hframes : m.stack.frames = #[topFrame]) (hbody : topFrame.body = translateBody body)
    (hloc : topFrame.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩) (hphase : ∀ p, body.phase ≠ .other p) (hcal : s.memory.activeCallee = none) (hbor_nil : s.memory.borrows = .nil) (hprot_nil : s.memory.activeProtectors = .nil)
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb) (hstmt : get? bb.statements s.frame.stmtIdx = some stmt) (hkind : stmt.kind = .assign ⟨dstIdx, .nil⟩ (.use (.copy ⟨srcIdx, [.unwrapUnsafeBinder dstDecl.ty]⟩)))
    (hsrc_decl : get? body.localDecls srcIdx = some srcDecl) (hdst_decl : get? body.localDecls dstIdx = some dstDecl) (hno_union : placeTouchesUnion body.localDecls body.layouts ⟨srcIdx, [.unwrapUnsafeBinder dstDecl.ty]⟩ = false)
    (hne_meta : encodeTyId dstDecl.ty ≠ arraySliceMetaTyId) (hsrc_nw : isWideOverlayPlace body.localDecls ⟨srcIdx, #[]⟩ = false ∧ translateTyOverlay srcDecl.ty body.layouts = translateTy srcDecl.ty body.layouts)
    (hdst_nw : isWideOverlayPlace body.localDecls ⟨dstIdx, #[]⟩ = false ∧ layoutOfEncodedTyIdOverlay (encodeTyId dstDecl.ty) body.layouts = translateTy dstDecl.ty body.layouts)
    (hsized : (translateTy srcDecl.ty body.layouts).layout.isSized = true ∧ (translateTy dstDecl.ty body.layouts).layout.isSized = true) (hdst_nonforget : (translateTy dstDecl.ty body.layouts).layout.isUninhabited = false ∧
      (translateTy dstDecl.ty body.layouts).layout.isZst = false ∧ (match (translateTy dstDecl.ty body.layouts).layout.backendRepr, (translateTy dstDecl.ty body.layouts).layout.variants,
          (translateTy dstDecl.ty body.layouts).layout.fields with
       | .Memory, .Single _, .Arbitrary offs _ => offs.isEmpty
       | _, _, _ => false) = false)
    (hsz_eq : (translateTy srcDecl.ty body.layouts).layout.size = (translateTy dstDecl.ty body.layouts).layout.size) (hsz_nz : (translateTy srcDecl.ty body.layouts).layout.size ≠ Miri.ABI.Size.ZERO)
    (hne_sd : dstIdx ≠ srcIdx) {slot_d : LocalSlot} {immDst : Miri.Interpreter.Immediate AnnealProv} {cDst : Option Miri.Interpreter.LocalLayout} (hlt_af_d : dstIdx < s.frame.locals.length)
    (hlt_mf_d : dstIdx < topFrame.locals.size) (hslot_d : get? s.frame.locals dstIdx = some slot_d) (hnot_dead_d : slot_d ≠ .dead) (hmls_d : topFrame.locals[dstIdx]'hlt_mf_d = ⟨.live (.immediate immDst), cDst⟩)
    (hc_d : ∀ l, cDst = some l → l = translateTy dstDecl.ty body.layouts) (hlt_mf_s : srcIdx < topFrame.locals.size) :
    let hooks := annealStepHooksUnwindFnPtrClosure body
    (∀ cSrc, get? s.frame.locals srcIdx = some .dead → topFrame.locals[srcIdx]'hlt_mf_s = ⟨.dead, cSrc⟩ → (∀ l, cSrc = some l → l = translateTy srcDecl.ty body.layouts) →
      StepRel body m (stepMirFn body s) (Miri.Interpreter.Step.step hooks () m)) ∧
    (∀ cSrc, get? s.frame.locals srcIdx = some .uninit → topFrame.locals[srcIdx]'hlt_mf_s = ⟨.live (.immediate .uninit), cSrc⟩ → (∀ l, cSrc = some l → l = translateTy srcDecl.ty body.layouts) →
      StepRel body m (stepMirFn body s) (Miri.Interpreter.Step.step hooks () m)) ∧
    (∀ (val : Value) (sc : Miri.Memory.Scalar AnnealProv) (cSrc : Option Miri.Interpreter.LocalLayout), get? s.frame.locals srcIdx = some (.init val) →
      validateLoadedValue body.layouts body.localDecls (.copy ⟨srcIdx, [.unwrapUnsafeBinder dstDecl.ty]⟩) val = true → topFrame.locals[srcIdx]'hlt_mf_s = ⟨.live (.immediate (.scalar sc)), cSrc⟩ →
      (∀ l, cSrc = some l → l = translateTy srcDecl.ty body.layouts) → ∃ s' tf', stepMirFn body s = .step s' ∧ s'.frame.blockIdx = s.frame.blockIdx ∧ s'.frame.stmtIdx = s.frame.stmtIdx + 1 ∧
        Miri.Interpreter.Step.step hooks () m = ({ stack := ⟨#[tf']⟩, machine := m.machine }, .ok true) ∧ tf'.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx + 1⟩ ∧ get? s'.frame.locals dstIdx = some (.init val) ∧
        tf'.locals[dstIdx]? = some ⟨.live (.immediate (.scalar sc)), some (translateTy dstDecl.ty body.layouts)⟩) := by
  intro hooks; have hreal : isRealUnwrapUnsafeBinderElem (.UnwrapUnsafeBinder (encodeTyId dstDecl.ty)) = true := by simp [isRealUnwrapUnsafeBinderElem, hne_meta]
  have hhas : hasRealUnwrapUnsafeBinder ⟨srcIdx, #[.UnwrapUnsafeBinder (encodeTyId dstDecl.ty)]⟩ = true := by simp [hasRealUnwrapUnsafeBinder, hreal]
  have hov : isUnwindFnPtrClosureAssign body.localDecls ⟨dstIdx, #[]⟩ (.Use (.Copy ⟨srcIdx, #[.UnwrapUnsafeBinder (encodeTyId dstDecl.ty)]⟩) .No) = true := by
    simp [isUnwindFnPtrClosureAssign, rvalueUsesPlaceOrClosureOverlay, operandHasRealUnwrapUnsafeBinder, hhas]
  cases m with | mk st mach =>
  obtain ⟨frs⟩ := st; dsimp only at hframes; subst hframes
  have heval_dst := annealEvalPlace_unprojected_root (m := { stack := ⟨#[topFrame]⟩, machine := mach })
    rfl hlt_mf_d hdst_decl (by rw [hmls_d]; exact hc_d)
  let tf_sd := ep2CacheDstSrc topFrame hlt_mf_d hlt_mf_s (translateTy dstDecl.ty body.layouts) (translateTy srcDecl.ty body.layouts); let st_sd : AnnealStepState := { stack := ⟨#[tf_sd]⟩, machine := mach }
  have hloc_sd : tf_sd.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩ := by dsimp only [tf_sd]; rw [ep2CacheDstSrc_location]; exact hloc
  have hlt_s' : srcIdx < (cacheFrameLocalLayout topFrame dstIdx hlt_mf_d (translateTy dstDecl.ty body.layouts)).locals.size := by rw [cacheFrameLocalLayout_size]; exact hlt_mf_s
  have hres_s : ∀ v cSrc, topFrame.locals[srcIdx]'hlt_mf_s = ⟨v, cSrc⟩ → (∀ l, cSrc = some l → l = translateTy srcDecl.ty body.layouts) → annealResolveAndCacheLocalLayoutOverlay body.localDecls body.layouts srcIdx
        (some (translateTy dstDecl.ty body.layouts))
        { stack := ⟨#[cacheFrameLocalLayout topFrame dstIdx hlt_mf_d (translateTy dstDecl.ty body.layouts)]⟩, machine := mach } =
      .ok (tf_sd, translateTy srcDecl.ty body.layouts) st_sd ∧ tf_sd.getLocal srcIdx = .ok ⟨v, some (translateTy srcDecl.ty body.layouts)⟩ := by
    intro v cSrc hmls_s hc_s; have hmls_s? : topFrame.locals[srcIdx]? = some ⟨v, cSrc⟩ := by rw [Array.getElem?_eq_getElem hlt_mf_s, hmls_s]
    obtain ⟨cSrc', hmls_sd, hc_sd⟩ := cacheFrameLocalLayout_getElem?_preserve topFrame hdst_decl hsrc_decl hlt_mf_d hmls_s? hc_s
    exact annealResolveAndCacheLocalLayoutOverlay_eq rfl hlt_s' hsrc_decl hsrc_nw (Option.some.inj ((Array.getElem?_eq_getElem hlt_s').symm.trans hmls_sd)) hc_sd
  have hev_prefix : ∀ (v : Miri.Interpreter.LocalValue AnnealProv) (cSrc : Option Miri.Interpreter.LocalLayout), topFrame.locals[srcIdx]'hlt_mf_s = ⟨v, cSrc⟩ → (∀ l, cSrc = some l → l = translateTy srcDecl.ty body.layouts) →
      (∀ mp, v ≠ .live (.indirect mp)) → Miri.Interpreter.Step.evalStatement hooks () (translateStmt stmt) { stack := ⟨#[topFrame]⟩, machine := mach } = Miri.Interpreter.runRvalue (do
          let opVal ← match tf_sd.getLocalOperand srcIdx with
            | .ok ov => pure ov
            | .error (.localExpectedLive _) => throw (.undefinedBehavior "read of dead local")
            | .error e => throw (.stack e)
          let projected ← annealEvalUnwrapChainOp body.localDecls body.layouts srcIdx tf_sd ⟨opVal, translateTy srcDecl.ty body.layouts⟩ [.UnwrapUnsafeBinder (encodeTyId dstDecl.ty)]
          let imm ← annealReadImmediateOverlay projected
          annealWriteImmediateLM2_2 imm.imm ⟨.local 0 dstIdx none topFrame.localsIdentity, translateTy dstDecl.ty body.layouts⟩) st_sd := by
    intro v cSrc hmls_s hc_s hnot_ind; obtain ⟨hrc, hget_sd⟩ := hres_s v cSrc hmls_s hc_s
    have hop_not_ind : ∀ mp, tf_sd.getLocalOperand srcIdx ≠ .ok (.indirect mp) := by
      intro mp h; unfold Miri.Interpreter.Frame.getLocalOperand at h; rw [hget_sd] at h; cases v with | dead => cases h | live op => cases op <;> cases h; exact hnot_ind _ rfl
    dsimp only [hooks]; unfold Miri.Interpreter.Step.evalStatement annealStepHooksUnwindFnPtrClosure translateStmt; rw [hkind]
    dsimp only [translateStmtKind, translateRvalue, translateOperand, translatePlace, translateProjectionElem, List.map, List.toArray, Miri.Interpreter.evalRvalueIntoPlace, annealRvalueHooksUnwindFnPtrClosure]
    rw [hov]; simp only [↓reduceIte]; unfold Miri.Interpreter.runRvalue; rw [annealEvalPlaceOverlay_unprojected_nonWide _ _ _ true hdst_nw.1, EStateM.bind_eq_ok heval_dst]; unfold annealEvalOperandOverlay; simp only [hhas, ↓reduceIte]
    dsimp only [Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, get, getThe, MonadStateOf.get, EStateM.get]
    rw [stack_currentFrame?_singleton ⟨#[cacheFrameLocalLayout topFrame dstIdx hlt_mf_d (translateTy dstDecl.ty body.layouts)]⟩ _ rfl]
    simp only [Option.isNone_some, Bool.false_eq_true, ↓reduceIte, annealRvalueHooksLM4_1, annealRvalueHooks]; rw [EStateM.bind, hrc]; dsimp only
    cases hgop : tf_sd.getLocalOperand srcIdx with
    | error e => cases e <;> rfl
    | ok ov => cases ov with
      | indirect mp => exact False.elim (hop_not_ind mp hgop)
      | immediate _ => rfl
  refine ⟨?_, ?_, ?_⟩
  · intro cSrc hslot_s hmls_s hc_s
    obtain ⟨_, hget_sd⟩ := hres_s .dead cSrc hmls_s hc_s; have hdead_op : tf_sd.getLocalOperand srcIdx = .error (.localExpectedLive srcIdx) := by unfold Miri.Interpreter.Frame.getLocalOperand; rw [hget_sd]; rfl
    have hm_err : Miri.Interpreter.Step.evalStatement hooks () (translateStmt stmt) { stack := ⟨#[topFrame]⟩, machine := mach } = (st_sd, .error (.undefinedBehavior "read of dead local")) := by
      rw [hev_prefix .dead cSrc hmls_s hc_s (fun _ h => by cases h), hdead_op]; rfl
    have ha_ub := trusted_step_assign_rvalue_ub hphase hcal hbb hstmt hkind (by unfold evalRvalue; dsimp only; rw [evalOperand_copy_unwrapUnsafeBinder_eq _ _ _ _ _ _ _ _ _ _ hno_union, hslot_s])
    rw [ha_ub, miri_step_at_statement_error _ rfl hbody hloc hbb hstmt hm_err]; exact .ub _ _
  · intro cSrc hslot_s hmls_s hc_s
    obtain ⟨_, hget_sd⟩ := hres_s (.live (.immediate .uninit)) cSrc hmls_s hc_s; have hop_u : tf_sd.getLocalOperand srcIdx = .ok (.immediate .uninit) := by unfold Miri.Interpreter.Frame.getLocalOperand; rw [hget_sd]; rfl
    have hm_err : Miri.Interpreter.Step.evalStatement hooks () (translateStmt stmt) { stack := ⟨#[topFrame]⟩, machine := mach } = (st_sd, .error (.undefinedBehavior "projected read of uninitialized local")) := by
      rw [hev_prefix _ cSrc hmls_s hc_s (fun _ h => by cases h), hop_u]
      unfold Miri.Interpreter.runRvalue annealEvalUnwrapChainOp
      simp [beq_false_of_ne hne_meta, bne_iff_ne.mpr hsz_nz, get, getThe, MonadStateOf.get, EStateM.get, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, throw, throwThe, MonadExceptOf.throw, EStateM.throw]
    have ha_ub := trusted_step_assign_rvalue_ub hphase hcal hbb hstmt hkind (by unfold evalRvalue; dsimp only; rw [evalOperand_copy_unwrapUnsafeBinder_eq _ _ _ _ _ _ _ _ _ _ hno_union, hslot_s])
    rw [ha_ub, miri_step_at_statement_error _ rfl hbody hloc hbb hstmt hm_err]; exact .ub _ _
  · intro val sc cSrc hslot_s hval_s hmls_s hc_s
    obtain ⟨_, hget_sd⟩ := hres_s (.live (.immediate (.scalar sc))) cSrc hmls_s hc_s; have hop_s : tf_sd.getLocalOperand srcIdx = .ok (.immediate (.scalar sc)) := by unfold Miri.Interpreter.Frame.getLocalOperand; rw [hget_sd]; rfl
    obtain ⟨hlt_d_sd, htf_sd_d⟩ := ep2CacheDstSrc_dst_getElem? topFrame (dstLay := translateTy dstDecl.ty body.layouts) (srcLay := translateTy srcDecl.ty body.layouts) hlt_mf_d hlt_mf_s hne_sd hmls_d
    have hzero_add : ∀ sz : Miri.ABI.Size, Miri.ABI.Size.ZERO.add sz = .ok sz := fun sz => by cases sz; unfold Miri.ABI.Size.add Miri.ABI.Size.ZERO; simp [UInt64.lt_iff_toNat_lt]; rfl
    have hproj_ok : Miri.Interpreter.project
        { annealProjectionCx tf_sd body.layouts st_sd.machine with
          layoutOf := fun t => .ok (layoutOfEncodedTyIdOverlay t body.layouts), memoryOffset := fun place offset mode metaVal => Miri.Interpreter.projectionMemoryOffset annealPointerArithmetic
              (annealPointerResolver st_sd.machine) (annealLiveAllocationLookup st_sd.machine)
              place offset mode metaVal }
        ⟨.immediate (.scalar sc), translateTy srcDecl.ty body.layouts⟩ (.UnwrapUnsafeBinder (encodeTyId dstDecl.ty)) = .ok ⟨.immediate (.scalar sc), translateTy dstDecl.ty body.layouts⟩ := by
      unfold Miri.Interpreter.project; dsimp only; rw [hdst_nw.2]; dsimp only [Bind.bind, Except.bind]; unfold annealProjectionCx; dsimp only
      unfold Miri.Interpreter.OpTy.transmute Miri.Interpreter.OpTy.offsetWithMeta Miri.Interpreter.projectionImmediateOffset
      simp [hsized.1, hsized.2, hsz_eq, hdst_nonforget.1, hdst_nonforget.2.1, hzero_add, Miri.Interpreter.MemPlaceMeta.hasMeta, Except.mapError, UInt64.lt_irrefl, Bind.bind, Except.bind, Pure.pure, Except.pure]
      have hf_false := hdst_nonforget.2.2
      cases hbr : (translateTy dstDecl.ty body.layouts).layout.backendRepr <;> cases hvr : (translateTy dstDecl.ty body.layouts).layout.variants <;> cases hfl : (translateTy dstDecl.ty body.layouts).layout.fields <;>
        simp [hbr, hvr, hfl] at hf_false ⊢ <;> simp [hf_false]
    have hif_false : (!(translateTy srcDecl.ty body.layouts).layout.isSized) = false := by simp [hsized.1]
    have hm_eval : Miri.Interpreter.Step.evalStatement hooks () (translateStmt stmt) { stack := ⟨#[topFrame]⟩, machine := mach } = Miri.Interpreter.runRvalue (annealWriteImmediateLM2_2 (.scalar sc)
            ⟨.local 0 dstIdx none topFrame.localsIdentity, translateTy dstDecl.ty body.layouts⟩) st_sd := by
      rw [hev_prefix _ cSrc hmls_s hc_s (fun _ h => by cases h), hop_s]
      unfold Miri.Interpreter.runRvalue annealEvalUnwrapChainOp
      simp only [Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, get, getThe, MonadStateOf.get, EStateM.get, beq_false_of_ne hne_meta, Bool.false_eq_true, ↓reduceIte, hif_false]; rw [hproj_ok]; rfl
    obtain ⟨tf', hm_step, hloc', hdst_m⟩ := miri_step_write_immediate_root hooks rfl hbody hloc hloc_sd hbb hstmt hlt_d_sd htf_sd_d hm_eval
    have hrv : evalRvalue s.frame.locals (.use (.copy ⟨srcIdx, [.unwrapUnsafeBinder dstDecl.ty]⟩)) s.memory body.localDecls body.layouts = .ok val s.frame.locals s.memory := by
      unfold evalRvalue; dsimp only; rw [evalOperand_copy_unwrapUnsafeBinder_eq _ _ _ _ _ _ _ _ _ _ hno_union, hslot_s]; dsimp only; rw [readProjectedValue_nil]; dsimp only; rw [hval_s]
    obtain ⟨ha_step, hblk', hstmt', hdst_a⟩ := trusted_step_assign_rvalue_ok hphase hcal hbb hstmt hkind hrv hlt_af_d hslot_d hnot_dead_d hbor_nil hprot_nil; exact ⟨_, tf', ha_step, hblk', hstmt', hm_step, hloc', hdst_a, hdst_m⟩
/-- **`C9` Universal Write Simulation & `.uninit` Divergence
(`step_unwrapUnsafeBinder_write_simulation`)**: proves lockstep initialized
write and `.dead`-local UB through vendored `PlaceDynamic.evalPlace`, plus
the explicit `.uninit`-destination divergence (Trusted `.fail .ub` vs.
canonical Miri initializing `dstIdx`). -/
theorem step_unwrapUnsafeBinder_write_simulation {body : CapturedMir} {s : MachineState} {m : AnnealStepState} {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {srcIdx dstIdx : Local} {srcDecl dstDecl : LocalDecl} {bb : BasicBlockData} {stmt : Statement} (hframes : m.stack.frames = #[topFrame]) (hbody : topFrame.body = translateBody body)
    (hloc : topFrame.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩) (hphase : ∀ p, body.phase ≠ .other p) (hcal : s.memory.activeCallee = none) (hbor_nil : s.memory.borrows = .nil) (hprot_nil : s.memory.activeProtectors = .nil)
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb) (hstmt : get? bb.statements s.frame.stmtIdx = some stmt) (hkind : stmt.kind = .assign ⟨dstIdx, [.unwrapUnsafeBinder srcDecl.ty]⟩ (.use (.copy ⟨srcIdx, .nil⟩)))
    (hsrc_decl : get? body.localDecls srcIdx = some srcDecl) (hdst_decl : get? body.localDecls dstIdx = some dstDecl) (hno_union : placeTouchesUnion body.localDecls body.layouts ⟨dstIdx, [.unwrapUnsafeBinder srcDecl.ty]⟩ = false)
    (hne_meta : encodeTyId srcDecl.ty ≠ arraySliceMetaTyId) (hsrc_nw : isWideOverlayPlace body.localDecls ⟨srcIdx, #[]⟩ = false ∧ layoutOfEncodedTyIdOverlay (encodeTyId srcDecl.ty) body.layouts = translateTy srcDecl.ty body.layouts)
    (hdst_nw : isWideOverlayPlace body.localDecls ⟨dstIdx, #[]⟩ = false ∧ translateTyOverlay dstDecl.ty body.layouts = translateTy dstDecl.ty body.layouts) (hsized : (translateTy dstDecl.ty body.layouts).layout.isSized = true ∧
      (translateTy srcDecl.ty body.layouts).layout.isSized = true)
    (hsz_eq : (translateTy dstDecl.ty body.layouts).layout.size = (translateTy srcDecl.ty body.layouts).layout.size) (hne_sd : dstIdx ≠ srcIdx) (hlt_af_d : dstIdx < s.frame.locals.length) (hlt_mf_d : dstIdx < topFrame.locals.size)
    (hlt_mf_s : srcIdx < topFrame.locals.size) {valS : Value} {scS : Miri.Memory.Scalar AnnealProv} {cSrc : Option Miri.Interpreter.LocalLayout} (hslot_s : get? s.frame.locals srcIdx = some (.init valS))
    (hval_s : validateLoadedValue body.layouts body.localDecls (.copy ⟨srcIdx, .nil⟩) valS = true) (hmls_s : topFrame.locals[srcIdx]'hlt_mf_s = ⟨.live (.immediate (.scalar scS)), cSrc⟩)
    (hc_s : ∀ l, cSrc = some l → l = translateTy srcDecl.ty body.layouts) :
    let hooks := annealStepHooksUnwindFnPtrClosure body
    (∀ cDst, get? s.frame.locals dstIdx = some .dead → topFrame.locals[dstIdx]'hlt_mf_d = ⟨.dead, cDst⟩ → (∀ l, cDst = some l → l = translateTy dstDecl.ty body.layouts) →
      StepRel body m (stepMirFn body s) (Miri.Interpreter.Step.step hooks () m)) ∧
    (∀ (oldVal : Value) (immDst : Miri.Interpreter.Immediate AnnealProv) (cDst : Option Miri.Interpreter.LocalLayout), get? s.frame.locals dstIdx = some (.init oldVal) →
      topFrame.locals[dstIdx]'hlt_mf_d = ⟨.live (.immediate immDst), cDst⟩ → (∀ l, cDst = some l → l = translateTy dstDecl.ty body.layouts) → ∃ s' tf', stepMirFn body s = .step s' ∧ s'.frame.blockIdx = s.frame.blockIdx ∧
        s'.frame.stmtIdx = s.frame.stmtIdx + 1 ∧ Miri.Interpreter.Step.step hooks () m = ({ stack := ⟨#[tf']⟩, machine := m.machine }, .ok true) ∧ tf'.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx + 1⟩ ∧
        get? s'.frame.locals dstIdx = some (.init valS) ∧ tf'.locals[dstIdx]? = some ⟨.live (.immediate (.scalar scS)), some (translateTy dstDecl.ty body.layouts)⟩) ∧
    (∀ cDst, get? s.frame.locals dstIdx = some .uninit → topFrame.locals[dstIdx]'hlt_mf_d = ⟨.live (.immediate .uninit), cDst⟩ → (∀ l, cDst = some l → l = translateTy dstDecl.ty body.layouts) → stepMirFn body s = .fail .ub ∧ ∃ tf',
        Miri.Interpreter.Step.step hooks () m = ({ stack := ⟨#[tf']⟩, machine := m.machine }, .ok true) ∧ tf'.locals[dstIdx]? = some ⟨.live (.immediate (.scalar scS)), some (translateTy dstDecl.ty body.layouts)⟩) := by
  intro hooks; have hact : activeMirBody body s = body := by simp [activeMirBody, hcal]
  have hreal : isRealUnwrapUnsafeBinderElem (.UnwrapUnsafeBinder (encodeTyId srcDecl.ty)) = true := by simp [isRealUnwrapUnsafeBinderElem, hne_meta]
  have hhas : hasRealUnwrapUnsafeBinder ⟨dstIdx, #[.UnwrapUnsafeBinder (encodeTyId srcDecl.ty)]⟩ = true := by simp [hasRealUnwrapUnsafeBinder, hreal]
  have hov : isUnwindFnPtrClosureAssign body.localDecls ⟨dstIdx, #[.UnwrapUnsafeBinder (encodeTyId srcDecl.ty)]⟩ (.Use (.Copy ⟨srcIdx, #[]⟩) .No) = true := by simp [isUnwindFnPtrClosureAssign, hhas]
  cases m with | mk st mach =>
  obtain ⟨frs⟩ := st; dsimp only at hframes; subst hframes
  let tf_sd := ep2CacheDstSrc topFrame hlt_mf_d hlt_mf_s (translateTy dstDecl.ty body.layouts) (translateTy srcDecl.ty body.layouts); let st_sd : AnnealStepState := { stack := ⟨#[tf_sd]⟩, machine := mach }
  have hloc_sd : tf_sd.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩ := by dsimp only [tf_sd]; rw [ep2CacheDstSrc_location]; exact hloc
  let tf_d := cacheFrameLocalLayout topFrame dstIdx hlt_mf_d (translateTy dstDecl.ty body.layouts); have hlt_s' : srcIdx < tf_d.locals.size := by rw [cacheFrameLocalLayout_size]; exact hlt_mf_s
  have hev_write : ∀ vD cDst, topFrame.locals[dstIdx]'hlt_mf_d = ⟨vD, cDst⟩ → (∀ l, cDst = some l → l = translateTy dstDecl.ty body.layouts) →
      Miri.Interpreter.Step.evalStatement hooks () (translateStmt stmt) { stack := ⟨#[topFrame]⟩, machine := mach } = Miri.Interpreter.runRvalue (annealWriteImmediateLM2_2 (.scalar scS)
          ⟨.local 0 dstIdx none topFrame.localsIdentity, translateTy srcDecl.ty body.layouts⟩) st_sd := by
    intro vD cDst hmls_d hc_d; obtain ⟨hres_d, htf_d_get⟩ := annealResolveAndCacheLocalLayoutOverlay_eq (m := { stack := ⟨#[topFrame]⟩, machine := mach }) (known := none) rfl hlt_mf_d hdst_decl hdst_nw hmls_d hc_d
    have heval_pd : annealEvalPlaceDynamicCanonical body.localDecls body.layouts ⟨dstIdx, #[.UnwrapUnsafeBinder (encodeTyId srcDecl.ty)]⟩ true { stack := ⟨#[topFrame]⟩, machine := mach } =
        .ok ⟨.local 0 dstIdx none topFrame.localsIdentity, translateTy srcDecl.ty body.layouts⟩ { stack := ⟨#[tf_d]⟩, machine := mach } := by
      have hne_d : (#[Miri.MIR.ProjectionElem.UnwrapUnsafeBinder (encodeTyId srcDecl.ty)] == #[Miri.MIR.ProjectionElem.Deref]) = false := rfl; have hcf_d := stack_currentFrame?_singleton ⟨#[tf_d]⟩ tf_d rfl
      have hltp : Miri.Interpreter.localToPlace (annealPlaceProjectionHooksOverlay body.localDecls body.layouts).place () dstIdx { stack := ⟨#[tf_d]⟩, machine := mach } =
          .ok ⟨.local 0 dstIdx none topFrame.localsIdentity, translateTy dstDecl.ty body.layouts⟩ { stack := ⟨#[tf_d]⟩, machine := mach } := by
        unfold Miri.Interpreter.localToPlace Miri.Interpreter.placeLayoutOfLocal
        dsimp only [annealPlaceProjectionHooksOverlay, annealMutablePlaceHooks, annealPlaceHooks, Bind.bind, Pure.pure, get, getThe, MonadStateOf.get]; unfold EStateM.get EStateM.pure EStateM.bind; dsimp only [tf_d] at hcf_d ⊢
        rw [hcf_d]; dsimp only; rw [htf_d_get, Miri.Interpreter.stackLift_ok]; dsimp only [Pure.pure, Bind.bind]; unfold EStateM.pure; simp [hsized.1, hcf_d]; rfl
      dsimp only [tf_d] at hltp
      have hlayOf : (annealPlaceProjectionHooksOverlay body.localDecls body.layouts).layoutOf () (encodeTyId srcDecl.ty) { stack := ⟨#[tf_d]⟩, machine := mach } =
          .ok (translateTy srcDecl.ty body.layouts) { stack := ⟨#[tf_d]⟩, machine := mach } := by
        unfold annealPlaceProjectionHooksOverlay; simp [Pure.pure, EStateM.pure, hsrc_nw.2]
      have hoff := ep2_offsetWithMeta_local_zero (annealPlaceProjectionHooksOverlay body.localDecls body.layouts) dstIdx topFrame.localsIdentity (translateTy dstDecl.ty body.layouts)
        (translateTy srcDecl.ty body.layouts) { stack := ⟨#[tf_d]⟩, machine := mach }
        .wrapping hsized.2 hsz_eq
      have hchk : (annealPlaceProjectionHooksOverlay body.localDecls body.layouts).place.checkPlaceType () ⟨dstIdx, #[.UnwrapUnsafeBinder (encodeTyId srcDecl.ty)]⟩
          ⟨.local 0 dstIdx (some Miri.ABI.Size.ZERO) topFrame.localsIdentity, translateTy srcDecl.ty body.layouts⟩
          { stack := ⟨#[tf_d]⟩, machine := mach } = .ok () { stack := ⟨#[tf_d]⟩, machine := mach } := rfl
      unfold annealEvalPlaceDynamicCanonical; rw [EStateM.bind_eq_ok hres_d]; dsimp only; unfold Miri.Interpreter.PlaceDynamic.evalPlace; dsimp only; rw [bind_assoc, EStateM.bind_eq_ok hltp]
      dsimp only [Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]; simp only [hne_d, Bool.true_and, Bool.false_eq_true, ↓reduceIte]; rw [← Array.forIn_toList]
      simp only [List.forIn_cons, List.forIn_nil, Miri.Interpreter.PlaceDynamic.project, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]; dsimp only [tf_d] at hlayOf hoff hchk; rw [hlayOf]
      simp only [hsized.1, hsized.2, hsz_eq, Bool.not_true, Bool.false_or, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hoff]; unfold EStateM.pure; dsimp only [tf_d] at *; rw [hchk]; simp
    have hmls_s? : topFrame.locals[srcIdx]? = some ⟨.live (.immediate (.scalar scS)), cSrc⟩ := by rw [Array.getElem?_eq_getElem hlt_mf_s, hmls_s]
    obtain ⟨cSrc', hmls_sd, hc_sd⟩ := cacheFrameLocalLayout_getElem?_preserve topFrame hdst_decl hsrc_decl hlt_mf_d hmls_s? hc_s
    have hop_live := annealEvalOperand_copy_live (m := { stack := ⟨#[tf_d]⟩, machine := mach }) (known := some (translateTy srcDecl.ty body.layouts)) rfl hlt_s' hsrc_decl
      (Option.some.inj ((Array.getElem?_eq_getElem hlt_s').symm.trans hmls_sd)) hc_sd
    dsimp only at hop_live; dsimp only [hooks]; unfold Miri.Interpreter.Step.evalStatement annealStepHooksUnwindFnPtrClosure translateStmt; rw [hkind]
    dsimp only [translateStmtKind, translateRvalue, translateOperand, translatePlace, translateProjectionElem, List.map, List.toArray, Miri.Interpreter.evalRvalueIntoPlace, annealRvalueHooksUnwindFnPtrClosure, annealEvalPlaceOverlay]
    rw [hov, hhas]; simp only [↓reduceIte]; unfold Miri.Interpreter.runRvalue; dsimp only [annealRvalueHooksLM4_1, annealRvalueHooks]; rw [EStateM.bind_eq_ok heval_pd]
    rw [annealEvalOperandOverlay_copy_nonWide _ _ _ _ hsrc_nw.1, EStateM.bind_eq_ok hop_live]; rfl
  have hrv : evalRvalue s.frame.locals (.use (.copy ⟨srcIdx, .nil⟩)) s.memory body.localDecls body.layouts = .ok valS s.frame.locals s.memory := by
    unfold evalRvalue; dsimp only; rw [evalOperand_copy_nil, hslot_s]; dsimp only; rw [hval_s]
  refine ⟨?_, ?_, ?_⟩
  · intro cDst hslot_d hmls_d hc_d
    obtain ⟨_, htf_sd_d'⟩ := ep2CacheDstSrc_dst_getElem? topFrame (dstLay := translateTy dstDecl.ty body.layouts) (srcLay := translateTy srcDecl.ty body.layouts) hlt_mf_d hlt_mf_s hne_sd hmls_d
    have hget_d := frame_getLocal_of_getElem? tf_sd dstIdx _ htf_sd_d'
    have hm_err : Miri.Interpreter.Step.evalStatement hooks () (translateStmt stmt) { stack := ⟨#[topFrame]⟩, machine := mach } = (st_sd, .error (.undefinedBehavior "write to dead local")) := by
      rw [hev_write .dead cDst hmls_d hc_d]; unfold Miri.Interpreter.runRvalue; rw [annealWriteImmediateLM2_2_dead (topFrame := tf_sd) rfl hget_d]
    have ha_ub : stepMirFn body s = .fail .ub := by rw [stepMirFn_activeMirBody_eq body s (by rw [hact]; exact hphase)]; simp only [hact, hbb, hstmt]; unfold evalStmt; rw [hkind]; dsimp only; rw [hrv]; dsimp only; rw [hslot_d]
    rw [ha_ub, miri_step_at_statement_error _ rfl hbody hloc hbb hstmt hm_err]; exact .ub _ _
  · intro oldVal immDst cDst hslot_d hmls_d hc_d
    obtain ⟨hlt_d_sd, htf_sd_d'⟩ := ep2CacheDstSrc_dst_getElem? topFrame (dstLay := translateTy dstDecl.ty body.layouts) (srcLay := translateTy srcDecl.ty body.layouts) hlt_mf_d hlt_mf_s hne_sd hmls_d
    obtain ⟨tf', hm_step, hloc', hdst_m⟩ := miri_step_write_immediate_root hooks rfl hbody hloc hloc_sd hbb hstmt hlt_d_sd htf_sd_d' (hev_write _ cDst hmls_d hc_d)
    have ha_step : stepMirFn body s = .step (advanceStmt s (s.frame.locals.set dstIdx (.init valS)) s.memory) := by
      rw [stepMirFn_activeMirBody_eq body s (by rw [hact]; exact hphase)]; simp only [hact, hbb, hstmt]; unfold evalStmt; rw [hkind]; dsimp only; rw [hrv]; dsimp only; rw [hslot_d]; dsimp only
      unfold writeProjectedForLocal ensureNestedFieldShells; rw [hno_union]; dsimp only; rw [writeProjectedValue_unwrapUnsafeBinder]; have hw : writeProjectedValue s.frame.locals oldVal .nil valS = .ok valS := by cases oldVal <;> rfl
      rw [hw]; dsimp only; rw [set?_eq_some_set hlt_af_d]; dsimp only
      cases hmem : s.memory; rw [hmem] at hbor_nil hprot_nil; dsimp at hbor_nil hprot_nil
      rw [hbor_nil, hprot_nil]; simp [invalidateConflictingBorrowsAtProj]
    refine ⟨_, tf', ha_step, rfl, rfl, hm_step, hloc', ?_, hdst_m⟩
    dsimp [advanceStmt]; rw [get?_eq_getElem?, List.getElem?_set_self hlt_af_d]
  · intro cDst hslot_d hmls_d hc_d
    obtain ⟨hlt_d_sd, htf_sd_d'⟩ := ep2CacheDstSrc_dst_getElem? topFrame (dstLay := translateTy dstDecl.ty body.layouts) (srcLay := translateTy srcDecl.ty body.layouts) hlt_mf_d hlt_mf_s hne_sd hmls_d
    obtain ⟨tf', hm_step, _, hdst_m⟩ := miri_step_write_immediate_root hooks rfl hbody hloc hloc_sd hbb hstmt hlt_d_sd htf_sd_d' (hev_write _ cDst hmls_d hc_d)
    have ha_ub : stepMirFn body s = .fail .ub := by rw [stepMirFn_activeMirBody_eq body s (by rw [hact]; exact hphase)]; simp only [hact, hbb, hstmt]; unfold evalStmt; rw [hkind]; dsimp only; rw [hrv]; dsimp only; rw [hslot_d]; rfl
    exact ⟨ha_ub, tf', hm_step, hdst_m⟩
private def ep2ExtractOk {ε α : Type} (e : Except ε α) (h : e.isOk = true) : α := match e, h with | .ok a, _ => a
private def c9U32Alloc : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree) := (ep2ExtractOk (Miri.Memory.Allocation.fromBytes (Prov := AnnealProv) #[77, 0, 0, 0] (translateAlignBytes 4) .Mut) rfl).withExtra none
private def c9ArrAlloc : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree) := (ep2ExtractOk (Miri.Memory.Allocation.fromBytes (Prov := AnnealProv) #[1, 0, 0, 0, 2, 0, 0, 0]
    (translateAlignBytes 4) .Mut) rfl).withExtra none
private def mkC9MemMachine (aid : Miri.Memory.AllocId) (alloc : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)) : AnnealMachine :=
  { memory := { AnnealMachine.empty.memory with live := #[(aid, ⟨.stack, alloc⟩)] }, addresses := { AnnealMachine.empty.addresses with baseAddr := #[⟨aid, annealStackBaseAddr aid⟩] }, borrowTracker := none }
private def c9Aid1 : Miri.Memory.AllocId := ⟨1, by decide⟩
private def c9Mp1 : Miri.Interpreter.MemPlace AnnealProv := ⟨⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr c9Aid1), some (.concrete c9Aid1 .one)⟩, .none, none⟩
private def c9LiveSc : Miri.Memory.Scalar AnnealProv := Miri.Memory.Scalar.fromPointer annealTargetDataLayout ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr c9Aid1), .concrete c9Aid1 .one⟩
private def c9MachU32 : AnnealMachine := mkC9MemMachine c9Aid1 c9U32Alloc
private def c9MachArr : AnnealMachine := mkC9MemMachine c9Aid1 c9ArrAlloc
private def c9BCopy : CapturedMir := mkEp2Body "c9_copy" [ep2U32Ty, c9BinderU32Ty] [.assign ⟨0, .nil⟩ (.use (.copy ⟨1, [.unwrapUnsafeBinder ep2U32Ty]⟩))] c9Layouts
private def c9BMove : CapturedMir := mkEp2Body "c9_move" [ep2U32Ty, c9BinderU32Ty] [.assign ⟨0, .nil⟩ (.use (.move ⟨1, [.unwrapUnsafeBinder ep2U32Ty]⟩))] c9Layouts
private def c9BDerefFirst : CapturedMir := mkEp2Body "c9_deref_first" [ep2U32Ty, c9RawU32PtrTy, ep2U32Ty] [.assign ⟨0, .nil⟩ (.use (.copy ⟨1, [.deref, .unwrapUnsafeBinder ep2U32Ty]⟩))] c9Layouts
private def c9PtrDang : Miri.Memory.Scalar AnnealProv := Miri.Memory.Scalar.fromPointer annealTargetDataLayout ⟨Miri.ABI.Size.ofBytes 0x9000, .concrete c8Aid .one⟩
private def c9BDerefAfter : CapturedMir := mkEp2Body "c9_deref_after" [ep2U32Ty, c9BinderPtrTy] [.assign ⟨0, .nil⟩ (.use (.copy ⟨1, [.unwrapUnsafeBinder c9RawU32PtrTy, .deref]⟩))] c9Layouts
private def c9BLen : CapturedMir := mkEp2Body "c9_len" [ep2UsizeTy, c9Arr2U32Ty] [.assign ⟨0, .nil⟩ (.len ⟨1, [.unwrapUnsafeBinder c9Arr2U32Ty]⟩)] c9Layouts
private theorem w_c9_part1 :
    let machU32 := c9MachU32; let bCopy := c9BCopy; let bMove := c9BMove
    let mCopy := mkEp2MiriState bCopy ep2U32Ty #[⟨.live (.immediate .uninit), some (translateTy ep2U32Ty c9Layouts)⟩, ⟨.live (.immediate (.scalar (miriScalarUInt 77 4))), some (translateTy c9BinderU32Ty c9Layouts)⟩]
    let mCopyMem := mkEp2MiriState bCopy ep2U32Ty #[⟨.live (.immediate .uninit), some (translateTy ep2U32Ty c9Layouts)⟩, ⟨.live (.indirect c9Mp1), some (translateTy c9BinderU32Ty c9Layouts)⟩] machU32
    let mMove := mkEp2MiriState bMove ep2U32Ty #[⟨.live (.immediate .uninit), some (translateTy ep2U32Ty c9Layouts)⟩, ⟨.live (.immediate (.scalar (miriScalarUInt 77 4))), some (translateTy c9BinderU32Ty c9Layouts)⟩]
    let mDead := mkEp2MiriState bCopy ep2U32Ty #[⟨.live (.immediate .uninit), some (translateTy ep2U32Ty c9Layouts)⟩, ⟨.dead, some (translateTy c9BinderU32Ty c9Layouts)⟩]
    let mUninitR := mkEp2MiriState bCopy ep2U32Ty #[⟨.live (.immediate .uninit), some (translateTy ep2U32Ty c9Layouts)⟩, ⟨.live (.immediate .uninit), some (translateTy c9BinderU32Ty c9Layouts)⟩]
    let rCopy := Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosure bCopy) () mCopy; let rCopyMem := Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosure bCopy) () mCopyMem
    let rMove := Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosure bMove) () mMove
    rCopy.2 = .ok true ∧ miriLocalVal? rCopy.1 0 = some (.live (.immediate (.scalar (miriScalarUInt 77 4)))) ∧ rCopyMem.2 = .ok true ∧ miriLocalVal? rCopyMem.1 0 = some (.live (.immediate (.scalar (miriScalarUInt 77 4)))) ∧
    rMove.2 = .ok true ∧ miriLocalVal? rMove.1 0 = some (.live (.immediate (.scalar (miriScalarUInt 77 4)))) ∧ (Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosure bCopy) () mDead).2 =
      .error (.undefinedBehavior "read of dead local") ∧
    (∃ msg, (Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosure bCopy) () mUninitR).2 = .error (.undefinedBehavior msg)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | (with_unfolding_all exact ⟨_, rfl⟩) | (with_unfolding_all rfl)
private def c9BWrite : CapturedMir := mkEp2Body "c9_write" [c9BinderU32Ty] [.assign ⟨0, [.unwrapUnsafeBinder ep2U32Ty]⟩ (.use (.constant { ty := ep2U32Ty, val := .scalar (.int ⟨99, 4⟩) }))] c9Layouts
private theorem w_c9_part2a :
    let mWriteInit := mkEp2MiriState c9BWrite c9BinderU32Ty #[⟨.live (.immediate (.scalar (miriScalarUInt 10 4))), some (translateTy c9BinderU32Ty c9Layouts)⟩]
    let mWriteUninit := mkEp2MiriState c9BWrite c9BinderU32Ty #[⟨.live (.immediate .uninit), some (translateTy c9BinderU32Ty c9Layouts)⟩]
    let rWrite := Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosure c9BWrite) () mWriteInit; let rWriteU := Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosure c9BWrite) () mWriteUninit
    rWrite.2 = .ok true ∧ miriLocalVal? rWrite.1 0 = some (.live (.immediate (.scalar (miriScalarUInt 99 4)))) ∧ rWriteU.2 = .ok true ∧ miriLocalVal? rWriteU.1 0 = some (.live (.immediate (.scalar (miriScalarUInt 99 4)))) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (with_unfolding_all rfl)
set_option maxHeartbeats 400000 in
private theorem w_c9_part2a_mem :
    let machU32 := c9MachU32; let mWriteMem := mkEp2MiriState c9BWrite c9BinderU32Ty #[⟨.live (.indirect c9Mp1), some (translateTy c9BinderU32Ty c9Layouts)⟩] machU32
    let rWriteMem := Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosure c9BWrite) () mWriteMem
    rWriteMem.2 = .ok true ∧ (rWriteMem.1.machine.memory.live[0]?.map (fun e => (e.2.allocation.getBytesUnchecked (Miri.Memory.allocRange .ZERO (Miri.ABI.Size.ofBytes 4))).toOption.map Array.toList)) = some (some [99, 0, 0, 0]) := by
  refine ⟨?_, ?_⟩ <;> (with_unfolding_all rfl)
private theorem w_c9_part2b :
    let machU32 := c9MachU32; let machArr := c9MachArr; let bDerefFirst := c9BDerefFirst
    let mDerefLive := mkEp2MiriState bDerefFirst ep2U32Ty #[⟨.live (.immediate .uninit), some (translateTy ep2U32Ty c9Layouts)⟩, ⟨.live (.immediate (.scalar c9LiveSc)), some (translateTy c9RawU32PtrTy c9Layouts)⟩,
        ⟨.live (.indirect c9Mp1), some (translateTy ep2U32Ty c9Layouts)⟩] machU32
    let mPtrDang := c9PtrDang
    let mDerefDang := mkEp2MiriState bDerefFirst ep2U32Ty #[⟨.live (.immediate .uninit), some (translateTy ep2U32Ty c9Layouts)⟩, ⟨.live (.immediate (.scalar mPtrDang)), some (translateTy c9RawU32PtrTy c9Layouts)⟩,
        ⟨.live (.immediate .uninit), some (translateTy ep2U32Ty c9Layouts)⟩] (mkEp2AddrMachine c8Aid c8Base)
    let bDerefAfter := c9BDerefAfter
    let mDerefAfter := mkEp2MiriState bDerefAfter ep2U32Ty #[⟨.live (.immediate .uninit), some (translateTy ep2U32Ty c9Layouts)⟩, ⟨.live (.immediate (.scalar mPtrDang)), some (translateTy c9BinderPtrTy c9Layouts)⟩]; let bLen := c9BLen
    let mLen := mkEp2MiriState bLen ep2UsizeTy #[⟨.live (.immediate .uninit), some (translateTy ep2UsizeTy c9Layouts)⟩, ⟨.live (.indirect c9Mp1), some (translateTy c9Arr2U32Ty c9Layouts)⟩] machArr
    let rDerefLive := Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosure bDerefFirst) () mDerefLive; let rLen := Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosure bLen) () mLen
    rDerefLive.2 = .ok true ∧ miriLocalVal? rDerefLive.1 0 = some (.live (.immediate (.scalar (miriScalarUInt 77 4)))) ∧ (∃ msg, (Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosure bDerefFirst) () mDerefDang).2 =
      .error (.undefinedBehavior msg)) ∧
    (∃ err, (Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosure bDerefAfter) () mDerefAfter).2 = .error err) ∧ rLen.2 = .ok true ∧ miriLocalVal? rLen.1 0 = some (.live (.immediate (.scalar (miriScalarUInt 2 8)))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | (with_unfolding_all exact ⟨_, rfl⟩) | (with_unfolding_all rfl)
/-- **`C9` Comprehensive Step Witness & Explicit Divergences**: covers
immediate and memory-backed (`MemPlace`) `UnwrapUnsafeBinder` reads/writes
(checking exact Miri output values), canonical `.uninit` write divergence
via `Step.step`, live and dangling `.deref` + `.unwrapUnsafeBinder`, post-
projection `.deref`, and both-machine `Rvalue.len` on a memory-backed
`[u32; 2]` array. -/
theorem w_c9_unwrapUnsafeBinder_read_write_deref_len_and_divergences :
    let aid1 : Miri.Memory.AllocId := ⟨1, by decide⟩
    let base1 := annealStackBaseAddr aid1; let mp1 : Miri.Interpreter.MemPlace AnnealProv := ⟨⟨Miri.ABI.Size.ofBytes base1, some (.concrete aid1 .one)⟩, .none, none⟩
    let pLiveSc := Miri.Memory.Scalar.fromPointer annealTargetDataLayout ⟨Miri.ABI.Size.ofBytes base1, .concrete aid1 .one⟩; let machU32 := c9MachU32; let machArr := c9MachArr; let bCopy := c9BCopy; let bMove := c9BMove
    let sLive : MachineState := { frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit, .init (.scalar ⟨77, 4⟩)] }, memory := emptyMemory }
    let mCopy := mkEp2MiriState bCopy ep2U32Ty #[⟨.live (.immediate .uninit), some (translateTy ep2U32Ty c9Layouts)⟩, ⟨.live (.immediate (.scalar (miriScalarUInt 77 4))), some (translateTy c9BinderU32Ty c9Layouts)⟩]
    let mCopyMem := mkEp2MiriState bCopy ep2U32Ty #[⟨.live (.immediate .uninit), some (translateTy ep2U32Ty c9Layouts)⟩, ⟨.live (.indirect mp1), some (translateTy c9BinderU32Ty c9Layouts)⟩] machU32
    let mMove := mkEp2MiriState bMove ep2U32Ty #[⟨.live (.immediate .uninit), some (translateTy ep2U32Ty c9Layouts)⟩, ⟨.live (.immediate (.scalar (miriScalarUInt 77 4))), some (translateTy c9BinderU32Ty c9Layouts)⟩]
    let sDead : MachineState := { sLive with frame := { sLive.frame with locals := [.uninit, .dead] } }
    let mDead := mkEp2MiriState bCopy ep2U32Ty #[⟨.live (.immediate .uninit), some (translateTy ep2U32Ty c9Layouts)⟩, ⟨.dead, some (translateTy c9BinderU32Ty c9Layouts)⟩]
    let sUninitR : MachineState := { sLive with frame := { sLive.frame with locals := [.uninit, .uninit] } }
    let mUninitR := mkEp2MiriState bCopy ep2U32Ty #[⟨.live (.immediate .uninit), some (translateTy ep2U32Ty c9Layouts)⟩, ⟨.live (.immediate .uninit), some (translateTy c9BinderU32Ty c9Layouts)⟩]
    let bWrite := mkEp2Body "c9_write" [c9BinderU32Ty] [.assign ⟨0, [.unwrapUnsafeBinder ep2U32Ty]⟩ (.use (.constant { ty := ep2U32Ty, val := .scalar (.int ⟨99, 4⟩) }))] c9Layouts
    let sWriteInit : MachineState := { frame := { blockIdx := 0, stmtIdx := 0, locals := [.init (.scalar ⟨10, 4⟩)] }, memory := emptyMemory }
    let mWriteInit := mkEp2MiriState bWrite c9BinderU32Ty #[⟨.live (.immediate (.scalar (miriScalarUInt 10 4))), some (translateTy c9BinderU32Ty c9Layouts)⟩]
    let mWriteMem := mkEp2MiriState bWrite c9BinderU32Ty #[⟨.live (.indirect mp1), some (translateTy c9BinderU32Ty c9Layouts)⟩] machU32
    let sWriteUninit : MachineState := { frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit] }, memory := emptyMemory }
    let mWriteUninit := mkEp2MiriState bWrite c9BinderU32Ty #[⟨.live (.immediate .uninit), some (translateTy c9BinderU32Ty c9Layouts)⟩]; let bDerefFirst := c9BDerefFirst
    let borLive : BorrowEntry := { tag := 1, parentTag := none, targetLocal := 2, targetProjection := .nil, perm := .frozen, protector := none, targetFrameDepth := 0 }
    let sDerefLive : MachineState := { frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit, .init (.ptr ⟨1, 0⟩ 8), .init (.scalar ⟨77, 4⟩)] }, memory := { emptyMemory with borrows := [borLive], nextTag := 2, nextAllocId := 2 } }
    let mDerefLive := mkEp2MiriState bDerefFirst ep2U32Ty #[⟨.live (.immediate .uninit), some (translateTy ep2U32Ty c9Layouts)⟩, ⟨.live (.immediate (.scalar pLiveSc)), some (translateTy c9RawU32PtrTy c9Layouts)⟩,
        ⟨.live (.indirect mp1), some (translateTy ep2U32Ty c9Layouts)⟩] machU32
    let sDerefDang : MachineState := { frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit, .init (.ptr ⟨900, 0⟩ 8), .uninit] }, memory := emptyMemory }; let mPtrDang := c9PtrDang
    let mDerefDang := mkEp2MiriState bDerefFirst ep2U32Ty #[⟨.live (.immediate .uninit), some (translateTy ep2U32Ty c9Layouts)⟩, ⟨.live (.immediate (.scalar mPtrDang)), some (translateTy c9RawU32PtrTy c9Layouts)⟩,
        ⟨.live (.immediate .uninit), some (translateTy ep2U32Ty c9Layouts)⟩] (mkEp2AddrMachine c8Aid c8Base)
    let bDerefAfter := c9BDerefAfter
    let mDerefAfter := mkEp2MiriState bDerefAfter ep2U32Ty #[⟨.live (.immediate .uninit), some (translateTy ep2U32Ty c9Layouts)⟩, ⟨.live (.immediate (.scalar mPtrDang)), some (translateTy c9BinderPtrTy c9Layouts)⟩]; let bLen := c9BLen
    let sLen : MachineState := { frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit, .init (.aggregate 0 [.scalar ⟨1, 4⟩, .scalar ⟨2, 4⟩])] }, memory := emptyMemory }
    let mLen := mkEp2MiriState bLen ep2UsizeTy #[⟨.live (.immediate .uninit), some (translateTy ep2UsizeTy c9Layouts)⟩, ⟨.live (.indirect mp1), some (translateTy c9Arr2U32Ty c9Layouts)⟩] machArr
    let rCopy := Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosure bCopy) () mCopy; let rCopyMem := Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosure bCopy) () mCopyMem
    let rMove := Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosure bMove) () mMove; let rWrite := Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosure bWrite) () mWriteInit
    let rWriteMem := Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosure bWrite) () mWriteMem; let rWriteU := Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosure bWrite) () mWriteUninit
    let rDerefLive := Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosure bDerefFirst) () mDerefLive; let rLen := Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosure bLen) () mLen
    (∃ s', stepMirFn bCopy sLive = .step s' ∧ get? s'.frame.locals 0 = some (.init (.scalar ⟨77, 4⟩))) ∧ rCopy.2 = .ok true ∧ miriLocalVal? rCopy.1 0 = some (.live (.immediate (.scalar (miriScalarUInt 77 4)))) ∧
    rCopyMem.2 = .ok true ∧ miriLocalVal? rCopyMem.1 0 = some (.live (.immediate (.scalar (miriScalarUInt 77 4)))) ∧ (∃ s', stepMirFn bMove sLive = .step s' ∧ get? s'.frame.locals 0 = some (.init (.scalar ⟨77, 4⟩))) ∧
    rMove.2 = .ok true ∧ miriLocalVal? rMove.1 0 = some (.live (.immediate (.scalar (miriScalarUInt 77 4)))) ∧ stepMirFn bCopy sDead = .fail .ub ∧ (Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosure bCopy) () mDead).2 =
      .error (.undefinedBehavior "read of dead local") ∧
    stepMirFn bCopy sUninitR = .fail .ub ∧ (∃ msg, (Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosure bCopy) () mUninitR).2 = .error (.undefinedBehavior msg)) ∧
    (∃ s', stepMirFn bWrite sWriteInit = .step s' ∧ get? s'.frame.locals 0 = some (.init (.scalar ⟨99, 4⟩))) ∧ rWrite.2 = .ok true ∧ miriLocalVal? rWrite.1 0 = some (.live (.immediate (.scalar (miriScalarUInt 99 4)))) ∧
    rWriteMem.2 = .ok true ∧ (rWriteMem.1.machine.memory.live[0]?.map (fun e => (e.2.allocation.getBytesUnchecked (Miri.Memory.allocRange .ZERO (Miri.ABI.Size.ofBytes 4))).toOption.map Array.toList)) = some (some [99, 0, 0, 0]) ∧
    stepMirFn bWrite sWriteUninit = .fail .ub ∧ rWriteU.2 = .ok true ∧ miriLocalVal? rWriteU.1 0 = some (.live (.immediate (.scalar (miriScalarUInt 99 4)))) ∧
    (∃ s', stepMirFn bDerefFirst sDerefLive = .step s' ∧ get? s'.frame.locals 0 = some (.init (.scalar ⟨77, 4⟩))) ∧ rDerefLive.2 = .ok true ∧ miriLocalVal? rDerefLive.1 0 = some (.live (.immediate (.scalar (miriScalarUInt 77 4)))) ∧
    stepMirFn bDerefFirst sDerefDang = .fail .ub ∧ (∃ msg, (Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosure bDerefFirst) () mDerefDang).2 = .error (.undefinedBehavior msg)) ∧
    stepMirFn bDerefAfter sDerefDang = .unsupported ∧ (∃ err, (Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosure bDerefAfter) () mDerefAfter).2 = .error err) ∧
    (∃ s', stepMirFn bLen sLen = .step s' ∧ get? s'.frame.locals 0 = some (.init (.scalar ⟨2, 8⟩))) ∧ rLen.2 = .ok true ∧ miriLocalVal? rLen.1 0 = some (.live (.immediate (.scalar (miriScalarUInt 2 8)))) := by
  have h1 := w_c9_part1; have h2a := w_c9_part2a; have h2am := w_c9_part2a_mem; have h2b := w_c9_part2b
  exact ⟨⟨_, rfl, rfl⟩, h1.1, h1.2.1, h1.2.2.1, h1.2.2.2.1, ⟨_, rfl, rfl⟩, h1.2.2.2.2.1, h1.2.2.2.2.2.1, rfl, h1.2.2.2.2.2.2.1, rfl, h1.2.2.2.2.2.2.2, ⟨_, rfl, rfl⟩, h2a.1, h2a.2.1, h2am.1, h2am.2, rfl,
    h2a.2.2.1, h2a.2.2.2, ⟨_, rfl, rfl⟩, h2b.1, h2b.2.1, rfl, h2b.2.2.1, rfl, h2b.2.2.2.1, ⟨_, rfl, rfl⟩, h2b.2.2.2.2.1, h2b.2.2.2.2.2⟩
end C9UnwrapUnsafeBinderSimulations

/-! ## Section 8. `C10` (`AggregateKind.closure`) -/
section C10AggregateClosure
private def c10U32FieldLayout : TypeLayout :=
  { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := .scalar (.initialized (.int 32 false) { start := 0, end_ := 0xFFFFFFFF }), variants := .single 0, fields := .primitive, fieldLayouts := .nil, isUninhabited := false }
private def c10PtrFieldLayout : TypeLayout :=
  { size := { bytes := 8 }, align := { bytes := 8 },
    backendRepr := .scalar (.initialized (.pointer 0) { start := 1, end_ := 0xFFFFFFFFFFFFFFFF }), variants := .single 0, fields := .primitive, fieldLayouts := .nil, isUninhabited := false }
private def c10Clos2Layout : TypeLayout :=
  { size := { bytes := 16 }, align := { bytes := 8 },
    backendRepr := .scalarPair (.initialized (.int 32 false) { start := 0, end_ := 0xFFFFFFFF }) (.initialized (.pointer 0) { start := 1, end_ := 0xFFFFFFFFFFFFFFFF }), variants := .single 0,
    fields := .arbitrary [{ bytes := 0 }, { bytes := 8 }] [0, 1], fieldLayouts := [2, 3], isUninhabited := false }
private def c10Layouts : LayoutTable := { emptyLayoutTable with entries := [c8ZstClosureLayout, c10Clos2Layout, c10U32FieldLayout, c10PtrFieldLayout] }
private def c10ZstClosTy : Ty := { kind := .closure "c10_zst" .nil, layoutIdx := 0 }
private def c10Cap2ClosTy : Ty := { kind := .closure "c10_cap2" [.uint .u32, .ref .not (.uint .u32)], layoutIdx := 1 }
/-- **`C10` Stage-1 `evalRvalue` & Vendored `writeAggregate` Equivalence**:
proves `writeAggregate (.Closure ...)` agrees definitionally with `.Tuple`
and succeeds identically on live 0-capture ZST destinations. -/
theorem c10_closure_rvalue_and_writeAggregate_simulation (locals : List LocalSlot) (defPath : DefPath) (ops : List Operand) (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (defId : Miri.MIR.DefId) (args : Array Miri.MIR.GenericArg) (mops : Array Miri.MIR.Operand) (dest : Miri.Interpreter.RuntimePlace AnnealProv) (st : AnnealStepState) (hfields : dest.layout.layout.fields = .Arbitrary #[] #[])
    (hmem : ∀ f l o id, dest.ref = .local f l o id → ∃ tf ov, st.stack.currentFrame? = some tf ∧ tf.getLocalOperand l = .ok ov) :
    let h := annealAggregateHooksUnwindFnPtrClosure localDecls layouts
    evalRvalue locals (.aggregate (.closure defPath) ops) mem localDecls layouts = (match evalOperands locals ops mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack with
       | .ok vals locals' => .ok (.aggregate 0 vals) locals' mem
       | .ub => .ub
       | .unsupported => .unsupported) ∧
    Miri.Interpreter.writeAggregate h () (.Closure defId args) mops dest = Miri.Interpreter.writeAggregate h () .Tuple mops dest ∧ Miri.Interpreter.writeAggregate h () (.Closure defId args) #[] dest st = .ok () st := by
  intro h; refine ⟨rfl, rfl, ?_⟩
  rcases dest with ⟨dref, ⟨dty, dlay⟩⟩
  rcases dlay with ⟨dfields, dvars, drepr, dniche, duninh, dalign, dsize, dmax, duabi, dreprc, dseed⟩
  dsimp at hfields; subst hfields
  cases dref with
  | memory mp => with_unfolding_all rfl
  | «local» f l o id =>
    obtain ⟨tf, ov, hcf, hget⟩ := hmem f l o id rfl
    with_unfolding_all
      simp only [Miri.Interpreter.writeAggregate, h, annealAggregateHooksUnwindFnPtrClosure, annealAggregateHooksLM2_2, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
        get, getThe, MonadStateOf.get, EStateM.get, Option.isSome, Bool.false_and, Bool.false_eq_true, beq_self_eq_true, ↓reduceIte, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.div_one,
        show (#[] : Array Miri.MIR.Operand).size = 0 from rfl, Nat.zero_add, Nat.sub_self, List.range'_zero, List.forIn_nil, hcf, hget]
/-- **`C10` Universal 0-Capture ZST Closure Step Simulation**: proves both
`.dead`-destination lockstep UB and live-destination lockstep `Step.step`
through vendored `Miri.Interpreter.writeAggregate (.Closure 0 #[]) #[]`. -/
theorem step_aggregate_closure_zst_simulation {body : CapturedMir} {s : MachineState} {m : AnnealStepState} {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {dstIdx : Local} {dstDecl : LocalDecl} {defPath : DefPath} {bb : BasicBlockData} {stmt : Statement} (hframes : m.stack.frames = #[topFrame]) (hbody : topFrame.body = translateBody body)
    (hloc : topFrame.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩) (hphase : ∀ p, body.phase ≠ .other p) (hcal : s.memory.activeCallee = none) (hbor_nil : s.memory.borrows = .nil) (hprot_nil : s.memory.activeProtectors = .nil)
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb) (hstmt : get? bb.statements s.frame.stmtIdx = some stmt) (hkind : stmt.kind = .assign ⟨dstIdx, .nil⟩ (.aggregate (.closure defPath) .nil))
    (hdst_decl : get? body.localDecls dstIdx = some dstDecl) (hdst_ty : dstDecl.ty.kind = .closure defPath .nil) (hdst_fields : (translateTy dstDecl.ty body.layouts).layout.fields = .Arbitrary #[] #[])
    (hlt_af_d : dstIdx < s.frame.locals.length) (hlt_mf_d : dstIdx < topFrame.locals.size) :
    let hooks := annealStepHooksUnwindFnPtrClosure body
    (∀ cDst, get? s.frame.locals dstIdx = some .dead → topFrame.locals[dstIdx]'hlt_mf_d = ⟨.dead, cDst⟩ → (∀ l, cDst = some l → l = translateTy dstDecl.ty body.layouts) →
      StepRel body m (stepMirFn body s) (Miri.Interpreter.Step.step hooks () m)) ∧
    (∀ slot_d immDst cDst, get? s.frame.locals dstIdx = some slot_d → slot_d ≠ .dead → topFrame.locals[dstIdx]'hlt_mf_d = ⟨.live (.immediate immDst), cDst⟩ → (∀ l, cDst = some l → l = translateTy dstDecl.ty body.layouts) → ∃ s' tf',
        stepMirFn body s = .step s' ∧ s'.frame.blockIdx = s.frame.blockIdx ∧ s'.frame.stmtIdx = s.frame.stmtIdx + 1 ∧ Miri.Interpreter.Step.step hooks () m = ({ stack := ⟨#[tf']⟩, machine := m.machine }, .ok true) ∧
        tf'.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx + 1⟩ ∧ get? s'.frame.locals dstIdx = some (.init (.aggregate 0 .nil))) := by
  intro hooks; have hact : activeMirBody body s = body := by simp [activeMirBody, hcal]
  have hno_wide_d : isWideOverlayPlace body.localDecls ⟨dstIdx, #[]⟩ = false := by
    apply isWideOverlayPlace_eq_false_of_decl hdst_decl <;> (cases hmk : dstDecl.ty with | mk k _ => rw [hmk] at hdst_ty; dsimp at hdst_ty; subst hdst_ty; rfl)
  let tf_d := cacheFrameLocalLayout topFrame dstIdx hlt_mf_d (translateTy dstDecl.ty body.layouts); let st_d : AnnealStepState := { stack := ⟨#[tf_d]⟩, machine := m.machine }
  have hov : isUnwindFnPtrClosureAssign body.localDecls ⟨dstIdx, #[]⟩ (.Aggregate (.Closure 0 #[]) #[]) = true := by simp [isUnwindFnPtrClosureAssign]
  have hev_base : ∀ vD cDst, topFrame.locals[dstIdx]'hlt_mf_d = ⟨vD, cDst⟩ → (∀ l, cDst = some l → l = translateTy dstDecl.ty body.layouts) → Miri.Interpreter.Step.evalStatement hooks () (translateStmt stmt) m =
      Miri.Interpreter.runRvalue (Miri.Interpreter.writeAggregate (annealAggregateHooksUnwindFnPtrClosure body.localDecls body.layouts) () (.Closure 0 #[]) #[]
          ⟨.local 0 dstIdx none topFrame.localsIdentity, translateTy dstDecl.ty body.layouts⟩) st_d := by
    intro vD cDst hmls_d hc_d; have heval_dst := annealEvalPlace_unprojected_root hframes hlt_mf_d hdst_decl (by rw [hmls_d]; exact hc_d); dsimp only [hooks]
    unfold Miri.Interpreter.Step.evalStatement annealStepHooksUnwindFnPtrClosure translateStmt; rw [hkind]
    dsimp only [translateStmtKind, translateRvalue, translateAggregateKind, translatePlace, List.map, List.toArray, Miri.Interpreter.evalRvalueIntoPlace, annealRvalueHooksUnwindFnPtrClosure]
    rw [show isUnwindFnPtrClosureAssign body.localDecls ⟨dstIdx, #[]⟩ (.Aggregate (.Closure 0 #[]) #[]) = true from hov]; simp only [↓reduceIte]; unfold Miri.Interpreter.runRvalue
    rw [annealEvalPlaceOverlay_unprojected_nonWide _ _ _ true hno_wide_d, EStateM.bind_eq_ok heval_dst]
  refine ⟨?_, ?_⟩
  · intro cDst hslot_d hmls_d hc_d
    have hget_d : tf_d.getLocalOperand dstIdx = .error (.localExpectedLive dstIdx) := by
      unfold Miri.Interpreter.Frame.getLocalOperand
      have h : tf_d.getLocal dstIdx = .ok ⟨.dead, some (translateTy dstDecl.ty body.layouts)⟩ := by
        apply frame_getLocal_of_getElem?; dsimp [tf_d, cacheFrameLocalLayout]
        rw [Array.getElem?_set_self hlt_mf_d, hmls_d]
      rw [h]; rfl
    have hm_err : Miri.Interpreter.Step.evalStatement hooks () (translateStmt stmt) m = (st_d, .error (.undefinedBehavior "write to dead local")) := by
      rw [hev_base .dead cDst hmls_d hc_d]; unfold Miri.Interpreter.runRvalue
      generalize hlay : translateTy dstDecl.ty body.layouts = dl at hdst_fields ⊢
      rcases dl with ⟨dty, ⟨df, dv, dr, dn, du, da, ds, dm, dua, drc, dsd⟩⟩
      dsimp at hdst_fields; subst hdst_fields; have hcf_d : st_d.stack.currentFrame? = some tf_d := rfl
      with_unfolding_all
        simp only [Miri.Interpreter.writeAggregate, annealAggregateHooksUnwindFnPtrClosure, annealAggregateHooksLM2_2, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
          get, getThe, MonadStateOf.get, EStateM.get, Option.isSome, Bool.false_and, Bool.false_eq_true, beq_self_eq_true, ↓reduceIte, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.div_one,
          show (#[] : Array Miri.MIR.Operand).size = 0 from rfl, Nat.zero_add, Nat.sub_self, List.range'_zero, List.forIn_nil, hcf_d, hget_d]
        rfl
    have ha_ub : stepMirFn body s = .fail .ub := by
      rw [stepMirFn_activeMirBody_eq body s (by rw [hact]; exact hphase)]; simp only [hact, hbb, hstmt]; unfold evalStmt; rw [hkind]; dsimp only; unfold evalRvalue evalOperands; dsimp only; rw [hslot_d]
    rw [ha_ub, miri_step_at_statement_error _ hframes hbody hloc hbb hstmt hm_err]; exact .ub _ _
  · intro slot_d immDst cDst hslot_d hnot_dead hmls_d hc_d
    have hget_d : tf_d.getLocalOperand dstIdx = .ok (.immediate immDst) := by
      unfold Miri.Interpreter.Frame.getLocalOperand
      have h : tf_d.getLocal dstIdx = .ok ⟨.live (.immediate immDst), some (translateTy dstDecl.ty body.layouts)⟩ := by
        apply frame_getLocal_of_getElem?; dsimp [tf_d, cacheFrameLocalLayout]
        rw [Array.getElem?_set_self hlt_mf_d, hmls_d]
      rw [h]; rfl
    have hm_ok : Miri.Interpreter.Step.evalStatement hooks () (translateStmt stmt) m = (st_d, .ok ()) := by
      rw [hev_base _ cDst hmls_d hc_d]; unfold Miri.Interpreter.runRvalue
      have hw := (c10_closure_rvalue_and_writeAggregate_simulation s.frame.locals defPath .nil s.memory body.localDecls body.layouts 0 #[] #[]
        ⟨.local 0 dstIdx none topFrame.localsIdentity, translateTy dstDecl.ty body.layouts⟩ st_d hdst_fields (fun f l o id heq => by
          injection heq with _ hl; subst hl
          exact ⟨tf_d, .immediate immDst, stack_currentFrame?_singleton st_d.stack tf_d rfl, hget_d⟩)).2.2
      rw [hw]
    have hrv : evalRvalue s.frame.locals (.aggregate (.closure defPath) .nil) s.memory body.localDecls body.layouts = .ok (.aggregate 0 .nil) s.frame.locals s.memory := rfl
    obtain ⟨ha_step, hblk', hstmt', hdst_a⟩ := trusted_step_assign_rvalue_ok hphase hcal hbb hstmt hkind hrv hlt_af_d hslot_d hnot_dead hbor_nil hprot_nil
    exact ⟨_, { tf_d with location := .mir ⟨s.frame.blockIdx, s.frame.stmtIdx + 1⟩ }, ha_step, hblk', hstmt', miri_step_at_statement_ok hooks (m' := st_d) hframes hbody hloc hbb hstmt hm_ok rfl hloc, rfl, hdst_a⟩
/-- **`C10` Universal First-Upvar Dead/Uninit UB Simulation**: proves left-to-
right operand evaluation in 2-capture `AggregateKind.closure` raises
lockstep UB on a `.dead` or `.uninit` first upvar before evaluating upvar
1. -/
theorem step_aggregate_closure_firstUpvar_ub_simulation {body : CapturedMir} {s : MachineState} {m : AnnealStepState} {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {dstIdx op0Idx op1Idx : Local} {dstDecl op0Decl : LocalDecl} {defPath : DefPath} {f0Lay : Miri.Interpreter.LocalLayout} {f0Off : Miri.ABI.Size} {bb : BasicBlockData} {stmt : Statement}
    (hframes : m.stack.frames = #[topFrame]) (hbody : topFrame.body = translateBody body) (hloc : topFrame.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩) (hphase : ∀ p, body.phase ≠ .other p) (hcal : s.memory.activeCallee = none)
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb) (hstmt : get? bb.statements s.frame.stmtIdx = some stmt) (hkind : stmt.kind = .assign ⟨dstIdx, .nil⟩
      (.aggregate (.closure defPath) [.move ⟨op0Idx, .nil⟩, .copy ⟨op1Idx, .nil⟩]))
    (hdst_decl : get? body.localDecls dstIdx = some dstDecl) (hop0_decl : get? body.localDecls op0Idx = some op0Decl) (hno_wide_d : isWideOverlayPlace body.localDecls ⟨dstIdx, #[]⟩ = false)
    (hno_wide_0 : isWideOverlayPlace body.localDecls ⟨op0Idx, #[]⟩ = false) (hnot_arr : ∀ s c, (translateTy dstDecl.ty body.layouts).layout.fields ≠ .Array s c) (hproj0 : annealProjectFieldPlace body.layouts none
      ⟨.local 0 dstIdx none topFrame.localsIdentity, translateTy dstDecl.ty body.layouts⟩ 0 = .ok ⟨.local 0 dstIdx (some f0Off) topFrame.localsIdentity, f0Lay⟩)
    (hop0_nz : (translateTy op0Decl.ty body.layouts).layout.size ≠ Miri.ABI.Size.ZERO) (hlt_mf_d : dstIdx < topFrame.locals.size) (hlt_mf_0 : op0Idx < topFrame.locals.size)
    (hc_d : ∀ l, (topFrame.locals[dstIdx]'hlt_mf_d).layout = some l → l = translateTy dstDecl.ty body.layouts) :
    let hooks := annealStepHooksUnwindFnPtrClosure body
    (∀ c0, get? s.frame.locals op0Idx = some .dead → topFrame.locals[op0Idx]'hlt_mf_0 = ⟨.dead, c0⟩ → (∀ l, c0 = some l → l = translateTy op0Decl.ty body.layouts) →
      StepRel body m (stepMirFn body s) (Miri.Interpreter.Step.step hooks () m)) ∧
    (∀ c0, get? s.frame.locals op0Idx = some .uninit → topFrame.locals[op0Idx]'hlt_mf_0 = ⟨.live (.immediate .uninit), c0⟩ → (∀ l, c0 = some l → l = translateTy op0Decl.ty body.layouts) →
      StepRel body m (stepMirFn body s) (Miri.Interpreter.Step.step hooks () m)) := by
  intro hooks; have heval_dst := annealEvalPlace_unprojected_root hframes hlt_mf_d hdst_decl hc_d; let tf_d := cacheFrameLocalLayout topFrame dstIdx hlt_mf_d (translateTy dstDecl.ty body.layouts)
  have hlt_0' : op0Idx < tf_d.locals.size := by rw [cacheFrameLocalLayout_size]; exact hlt_mf_0
  have hproj_hook : (annealAggregateHooksUnwindFnPtrClosure body.localDecls body.layouts).projectField () ⟨.local 0 dstIdx none topFrame.localsIdentity, translateTy dstDecl.ty body.layouts⟩ 0
      { stack := ⟨#[tf_d]⟩, machine := m.machine } = .ok ⟨.local 0 dstIdx (some f0Off) topFrame.localsIdentity, f0Lay⟩ { stack := ⟨#[tf_d]⟩, machine := m.machine } := by
    unfold annealAggregateHooksUnwindFnPtrClosure annealAggregateHooksLM2_2; dsimp only
    cases hf : (translateTy dstDecl.ty body.layouts).layout.fields with
    | Array s c => exact False.elim (hnot_arr s c hf)
    | Primitive | Union _ | Arbitrary _ _ => rw [hproj0]; rfl
  have hov : isUnwindFnPtrClosureAssign body.localDecls ⟨dstIdx, #[]⟩ (.Aggregate (.Closure 0 #[]) #[.Move ⟨op0Idx, #[]⟩, .Copy ⟨op1Idx, #[]⟩]) = true := by simp [isUnwindFnPtrClosureAssign]
  refine ⟨?_, ?_⟩
  · intro c0 hslot0 hmls0 hc0
    have hmls0? : topFrame.locals[op0Idx]? = some ⟨.dead, c0⟩ := by rw [Array.getElem?_eq_getElem hlt_mf_0, hmls0]
    obtain ⟨c0', hmls_d0, hc_d0⟩ := cacheFrameLocalLayout_getElem?_preserve topFrame hdst_decl hop0_decl hlt_mf_d hmls0? hc0
    have hop_dead := annealEvalOperand_move_dead (m := { stack := ⟨#[tf_d]⟩, machine := m.machine }) (known := some f0Lay) rfl hlt_0' hop0_decl (Option.some.inj ((Array.getElem?_eq_getElem hlt_0').symm.trans hmls_d0)) hc_d0
    dsimp only at hop_dead
    have hm_err : Miri.Interpreter.Step.evalStatement hooks () (translateStmt stmt) m =
        ({ stack := ⟨#[cacheFrameLocalLayout tf_d op0Idx hlt_0' (translateTy op0Decl.ty body.layouts)]⟩, machine := m.machine }, .error (.undefinedBehavior "read of dead local")) := by
      dsimp only [hooks]; unfold Miri.Interpreter.Step.evalStatement annealStepHooksUnwindFnPtrClosure translateStmt; rw [hkind]
      dsimp only [translateStmtKind, translateRvalue, translateAggregateKind, translateOperand, translatePlace, List.map, List.toArray, Miri.Interpreter.evalRvalueIntoPlace, annealRvalueHooksUnwindFnPtrClosure]
      rw [show isUnwindFnPtrClosureAssign body.localDecls ⟨dstIdx, #[]⟩ (.Aggregate (.Closure 0 #[]) #[.Move ⟨op0Idx, #[]⟩, .Copy ⟨op1Idx, #[]⟩]) = true from hov]; simp only [↓reduceIte]; unfold Miri.Interpreter.runRvalue
      rw [annealEvalPlaceOverlay_unprojected_nonWide _ _ _ true hno_wide_d, EStateM.bind_eq_ok heval_dst]; unfold Miri.Interpreter.writeAggregate
      have hsz2 : (#[.Move ⟨op0Idx, #[]⟩, .Copy ⟨op1Idx, #[]⟩] : Array Miri.MIR.Operand).size = 2 := rfl; have hrange2 : List.range' 0 2 = [0, 1] := rfl
      have har0 : (#[.Move ⟨op0Idx, #[]⟩, .Copy ⟨op1Idx, #[]⟩] : Array Miri.MIR.Operand)[0]? = some (.Move ⟨op0Idx, #[]⟩) := rfl; have hopt0 : (none : Option Nat).getD 0 = 0 := rfl
      dsimp only [Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, Option.isSome]; simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, hsz2]; rw [Std.Legacy.Range.forIn_eq_forIn_range']
      simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, hrange2, forIn, List.forIn'_cons, har0, Option.getD_none, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]
      rw [hproj_hook]; dsimp only [annealAggregateHooksUnwindFnPtrClosure, annealAggregateHooksLM2_2]; rw [annealEvalOperandOverlay_move_nonWide _ _ _ _ hno_wide_0]; dsimp only [Bind.bind, EStateM.bind]; rw [hop_dead]
    have ha_ub := trusted_step_assign_rvalue_ub hphase hcal hbb hstmt hkind (by unfold evalRvalue evalOperands evalOperand; simp [hslot0]); rw [ha_ub, miri_step_at_statement_error _ hframes hbody hloc hbb hstmt hm_err]; exact .ub _ _
  · intro c0 hslot0 hmls0 hc0
    have hmls0? : topFrame.locals[op0Idx]? = some ⟨.live (.immediate .uninit), c0⟩ := by rw [Array.getElem?_eq_getElem hlt_mf_0, hmls0]
    obtain ⟨c0', hmls_d0, hc_d0⟩ := cacheFrameLocalLayout_getElem?_preserve topFrame hdst_decl hop0_decl hlt_mf_d hmls0? hc0
    have hop_live := annealEvalOperand_move_live (m := { stack := ⟨#[tf_d]⟩, machine := m.machine }) (known := some f0Lay) rfl hlt_0' hop0_decl (Option.some.inj ((Array.getElem?_eq_getElem hlt_0').symm.trans hmls_d0)) hc_d0
    dsimp only at hop_live; let tf_c0 := cacheFrameLocalLayout tf_d op0Idx hlt_0' (translateTy op0Decl.ty body.layouts); have hlt_0c : op0Idx < tf_c0.locals.size := by rw [cacheFrameLocalLayout_size]; exact hlt_0'
    let newLoc0 : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout := { tf_c0.locals[op0Idx]'hlt_0c with value := .live (.immediate .uninit) }
    let tf_0 := { tf_c0 with locals := tf_c0.locals.set op0Idx newLoc0 hlt_0c }
    have hm_err : Miri.Interpreter.Step.evalStatement hooks () (translateStmt stmt) m = ({ stack := ⟨#[tf_0]⟩, machine := m.machine }, .error (.undefinedBehavior "read of uninitialized local")) := by
      dsimp only [hooks]; unfold Miri.Interpreter.Step.evalStatement annealStepHooksUnwindFnPtrClosure translateStmt; rw [hkind]
      dsimp only [translateStmtKind, translateRvalue, translateAggregateKind, translateOperand, translatePlace, List.map, List.toArray, Miri.Interpreter.evalRvalueIntoPlace, annealRvalueHooksUnwindFnPtrClosure]
      rw [show isUnwindFnPtrClosureAssign body.localDecls ⟨dstIdx, #[]⟩ (.Aggregate (.Closure 0 #[]) #[.Move ⟨op0Idx, #[]⟩, .Copy ⟨op1Idx, #[]⟩]) = true from hov]; simp only [↓reduceIte]; unfold Miri.Interpreter.runRvalue
      rw [annealEvalPlaceOverlay_unprojected_nonWide _ _ _ true hno_wide_d, EStateM.bind_eq_ok heval_dst]; unfold Miri.Interpreter.writeAggregate
      have hsz2 : (#[.Move ⟨op0Idx, #[]⟩, .Copy ⟨op1Idx, #[]⟩] : Array Miri.MIR.Operand).size = 2 := rfl; have hrange2 : List.range' 0 2 = [0, 1] := rfl
      have har0 : (#[.Move ⟨op0Idx, #[]⟩, .Copy ⟨op1Idx, #[]⟩] : Array Miri.MIR.Operand)[0]? = some (.Move ⟨op0Idx, #[]⟩) := rfl; have hopt0 : (none : Option Nat).getD 0 = 0 := rfl
      dsimp only [Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, Option.isSome]; simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, hsz2]; rw [Std.Legacy.Range.forIn_eq_forIn_range']
      simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, hrange2, forIn, List.forIn'_cons, har0, Option.getD_none, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]
      rw [hproj_hook]; dsimp only [annealAggregateHooksUnwindFnPtrClosure, annealAggregateHooksLM2_2]; rw [annealEvalOperandOverlay_move_nonWide _ _ _ _ hno_wide_0]; dsimp only [Bind.bind, EStateM.bind]; rw [hop_live]
      dsimp only [Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]; unfold annealReadImmediateOverlay; simp [beq_false_of_ne hop0_nz, throw, throwThe, MonadExceptOf.throw, EStateM.throw, tf_0, deinitFrameLocal, newLoc0, tf_c0]
    have ha_ub := trusted_step_assign_rvalue_ub hphase hcal hbb hstmt hkind (by unfold evalRvalue evalOperands evalOperand; simp [hslot0]); rw [ha_ub, miri_step_at_statement_error _ hframes hbody hloc hbb hstmt hm_err]; exact .ub _ _
/-- **`C10` Witness**: 0-capture ZST closure (live & `.dead`-destination UB
equivalence), Trusted 3-step multi-capture `[u32, &u32]` closure
construction + `.Move` deinit + `.Field` read-back, and dead/uninit upvar
UB equivalence. -/
theorem w_c10_closure_zst_multiCapture_move_and_upvar_ub :
    let mach := mkEp2AddrMachine c8Aid c8Base; let refMsc := Miri.Memory.Scalar.fromPointer annealTargetDataLayout ⟨Miri.ABI.Size.ofBytes c8Base, .concrete c8Aid .one⟩
    let bZst := mkEp2Body "c10_zst_w" [c10ZstClosTy] [.assign ⟨0, .nil⟩ (.aggregate (.closure "c10_zst") .nil)] c10Layouts
    let sZst : MachineState := { frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit] }, memory := emptyMemory }
    let mZst := mkEp2MiriState bZst c10ZstClosTy #[⟨.live (.immediate .uninit), some (translateTy c10ZstClosTy c10Layouts)⟩]
    let sZstDead : MachineState := { frame := { blockIdx := 0, stmtIdx := 0, locals := [.dead] }, memory := emptyMemory }; let mZstDead := mkEp2MiriState bZst c10ZstClosTy #[⟨.dead, some (translateTy c10ZstClosTy c10Layouts)⟩]
    let bCap2 := mkEp2Body "c10_cap2_w" [ep2U32Ty, ep2RefU32Ty, c10Cap2ClosTy, ep2U32Ty, ep2RefU32Ty] [.assign ⟨2, .nil⟩ (.aggregate (.closure "c10_cap2") [.move ⟨3, .nil⟩, .copy ⟨4, .nil⟩]),
       .assign ⟨0, .nil⟩ (.use (.copy ⟨2, [.field 0 ep2U32Ty]⟩)), .assign ⟨1, .nil⟩ (.use (.copy ⟨2, [.field 1 ep2RefU32Ty]⟩))] c10Layouts
    let sCap0 : MachineState :=
      { frame := { blockIdx := 0, stmtIdx := 0,
                   locals := [.uninit, .uninit, .uninit, .init (.scalar ⟨42, 4⟩), .init (.ptr ⟨65536, 0⟩ 8)] },
        memory := emptyMemory }
    let mCapDead := mkEp2MiriState bCap2 ep2U32Ty #[⟨.live (.immediate .uninit), some (translateTy ep2U32Ty c10Layouts)⟩, ⟨.live (.immediate .uninit), some (translateTy ep2RefU32Ty c10Layouts)⟩,
        ⟨.live (.immediate .uninit), some (translateTy c10Cap2ClosTy c10Layouts)⟩, ⟨.dead, some (translateTy ep2U32Ty c10Layouts)⟩, ⟨.live (.immediate (.scalar refMsc)), some (translateTy ep2RefU32Ty c10Layouts)⟩] mach
    let sCapDead : MachineState := { sCap0 with frame := { sCap0.frame with locals := [.uninit, .uninit, .uninit, .dead, .init (.ptr ⟨65536, 0⟩ 8)] } }
    let mCapUninit := mkEp2MiriState bCap2 ep2U32Ty #[⟨.live (.immediate .uninit), some (translateTy ep2U32Ty c10Layouts)⟩, ⟨.live (.immediate .uninit), some (translateTy ep2RefU32Ty c10Layouts)⟩,
        ⟨.live (.immediate .uninit), some (translateTy c10Cap2ClosTy c10Layouts)⟩, ⟨.live (.immediate .uninit), some (translateTy ep2U32Ty c10Layouts)⟩,
        ⟨.live (.immediate (.scalar refMsc)), some (translateTy ep2RefU32Ty c10Layouts)⟩] mach
    let sCapUninit : MachineState := { sCap0 with frame := { sCap0.frame with locals := [.uninit, .uninit, .uninit, .uninit, .init (.ptr ⟨65536, 0⟩ 8)] } }
    (∃ s', stepMirFn bZst sZst = .step s' ∧ get? s'.frame.locals 0 = some (.init (.aggregate 0 .nil))) ∧ (Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosure bZst) () mZst).2 = .ok true ∧ stepMirFn bZst sZstDead = .fail .ub ∧
    (Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosure bZst) () mZstDead).2 = .error (.undefinedBehavior "write to dead local") ∧ (∃ s1 s2 s3, stepMirFn bCap2 sCap0 = .step s1 ∧ get? s1.frame.locals 3 = some .uninit ∧
      get? s1.frame.locals 4 = some (.init (.ptr ⟨65536, 0⟩ 8)) ∧ stepMirFn bCap2 s1 = .step s2 ∧ stepMirFn bCap2 s2 = .step s3 ∧ get? s3.frame.locals 0 = some (.init (.scalar ⟨42, 4⟩)) ∧
      get? s3.frame.locals 1 = some (.init (.ptr ⟨65536, 0⟩ 8))) ∧
    stepMirFn bCap2 sCapDead = .fail .ub ∧ (Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosure bCap2) () mCapDead).2 = .error (.undefinedBehavior "read of dead local") ∧ stepMirFn bCap2 sCapUninit = .fail .ub ∧
    (Miri.Interpreter.Step.step (annealStepHooksUnwindFnPtrClosure bCap2) () mCapUninit).2 = .error (.undefinedBehavior "read of uninitialized local") := by
  refine ⟨⟨_, rfl, rfl⟩, ?_, rfl, ?_, ⟨_, _, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, ?_, rfl, ?_⟩
  · with_unfolding_all rfl
  · with_unfolding_all rfl
  · with_unfolding_all rfl
  · with_unfolding_all rfl
end C10AggregateClosure

/-! ## Section 9. Module Axiom & Soundness Audit -/
section AxiomAudit
open Lean Elab Command
/-- Walk every declaration elaborated in
`LeanMiriSpec.UnwindSetDiscrAndFnPtrLM` and assert that only standard Lean
axioms are used. -/
elab "#assert_unwind_setdiscr_lm_standard_axioms" : command => do
  let env ← getEnv
  let mut checked : Nat := 0
  for (c, _) in env.constants.map₂.toList do
    let axs ← liftCoreM <| Lean.collectAxioms c
    for a in axs do
      unless a == ``propext || a == ``Quot.sound || a == ``Classical.choice do
        throwError "{c} depends on non-standard axiom {a}"
    checked := checked + 1
  if checked == 0 then
    throwError "LeanMiriSpec.UnwindSetDiscrAndFnPtrLM: found 0 module declarations"
  logInfo m!"LeanMiriSpec.UnwindSetDiscrAndFnPtrLM: verified standard axioms for {checked} declarations (0 sorryAx, 0 ofReduceBool)"
#assert_unwind_setdiscr_lm_standard_axioms
end AxiomAudit
end LeanMiriSpec.UnwindSetDiscrAndFnPtrLM
