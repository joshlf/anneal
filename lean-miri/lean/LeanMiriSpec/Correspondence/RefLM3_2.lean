/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import LeanMiriSpec.Correspondence.SimLM3_1

/-!
# Safe References & Validity for `LM-3.2`

Relates Anneal's safe references (`&T` / `&mut T` in
`Trusted.Rustc.V2026_06_01.MirSemantics`) to `lean-miri` references and to the
vendored validity visitor `Miri.Interpreter.ValidityVisitor`.

* `LocalRelLM3_2`, `FrameRelLM3_2`, `StateRelLM3_2`, `StepRelLM3_2`: the
  `LM-3.1` relations (`PtrLM3_1`) extended with locals of safe-reference type.
  Anneal and `lean-miri` represent a reference exactly as they represent a raw
  pointer (`.ptr p 8` and `Scalar.fromPointer annealTargetDataLayout mptr`,
  related by `PtrRel`); only the declared type, and with it the cached layout
  (`TyId 41`, non-null `pointerLayoutData true`), differs.
  `StateRelLM3_1.toLM3_2` embeds every `LM-3.1` state.
* `annealValidityHooks`: the vendored `ValidityVisitor.Hooks` instantiated for
  Anneal's single-threaded machine, so that `ValidityVisitor.validatePlace`
  checks `bool`, `char`, integer, `!`, raw-pointer, function-pointer, and
  safe-reference values exactly as `lean-miri`'s validity pass does
  (`validity.rs::check_safe_pointer` for references). Its context is the
  Anneal type of the validated place, because `encodeTyId` maps every reference
  to `TyId 41` and so drops the pointee and the mutability that validity needs.
* Exact characterizations of `annealSafeRefDerefCheck`, the eager checks that
  `Translate.lean`'s safe-reference dereference performs
  (`PointerPlaceMachine.dereference` on `Kind.reference`).
-/

namespace LeanMiriSpec.Correspondence

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

/-! ## 1. Reference-Aware Local, Frame, and State Relations -/

/-- `LocalRelLM3_1` extended with safe-reference locals.

An initialized local of type `&T` or `&mut T` holds `.ptr p 8` in Anneal and
the immediate scalar `Scalar.fromPointer annealTargetDataLayout mptr` in
`lean-miri`, with `PtrRel allocMap p mptr`: the same representation as a raw
pointer, at the reference's own declared type. Every other local is related by
`LocalRelLM3_1`, so all `LM-3.1` facts about it carry over. -/
inductive LocalRelLM3_2
    (mach : AnnealMachine) (allocMap : List AllocMapEntry)
    (decl : LocalDecl) (layouts : LayoutTable) :
    LocalSlot → Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout → Prop where
  /-- A local related by `LocalRelLM3_1`. -/
  | lm3_1 {slot : LocalSlot}
      {mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout} :
      LocalRelLM3_1 mach allocMap decl layouts slot mls →
      LocalRelLM3_2 mach allocMap decl layouts slot mls
  /-- An immediate safe-reference local. -/
  | ref (p : ProvenancePtr) (mptr : Miri.Memory.Pointer AnnealProv)
      (cachedLayout : Option Miri.Interpreter.LocalLayout)
      (mutability : Mutability) (pointeeKind : RigidTy) :
      (∀ l ∈ cachedLayout, l = translateTy decl.ty layouts) →
      decl.ty.kind = .ref mutability pointeeKind →
      PtrRel allocMap p mptr →
      LocalRelLM3_2 mach allocMap decl layouts (.init (.ptr p 8))
        ⟨.live (.immediate
            (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))),
          cachedLayout⟩

namespace LocalRelLM3_2

/-- Cached layout membership version of `LocalRelLM3_1.cachedLayout_eq`. -/
theorem cachedLayout_eq {mach : AnnealMachine} {allocMap : List AllocMapEntry}
    {decl : LocalDecl} {layouts : LayoutTable} {slot : LocalSlot}
    {mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout}
    (h : LocalRelLM3_2 mach allocMap decl layouts slot mls) :
    ∀ l ∈ mls.layout, l = translateTy decl.ty layouts := by
  cases h with
  | lm3_1 h => exact h.cachedLayout_eq
  | ref _ _ _ _ _ hc _ _ => exact hc

/-- `LocalRelLM3_2` survives extending `allocMap` with another entry. -/
theorem mono_cons {mach : AnnealMachine} {allocMap : List AllocMapEntry}
    (e : AllocMapEntry) {decl : LocalDecl} {layouts : LayoutTable} {slot : LocalSlot}
    {mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout}
    (h : LocalRelLM3_2 mach allocMap decl layouts slot mls) :
    LocalRelLM3_2 mach (e :: allocMap) decl layouts slot mls := by
  cases h with
  | lm3_1 h => exact .lm3_1 (h.mono_cons e)
  | ref p mptr cl mutability pointeeKind hc hty hptr =>
    exact .ref p mptr cl mutability pointeeKind hc hty (hptr.mono_cons e)

/-- `LocalRelLM3_2` survives any `allocMap` map that preserves `.tag` and
`.allocId`. -/
theorem map_preserve {mach : AnnealMachine} {allocMap : List AllocMapEntry}
    (f : AllocMapEntry → AllocMapEntry)
    (htag : ∀ e, (f e).tag = e.tag)
    (halloc : ∀ e, (f e).allocId = e.allocId)
    {decl : LocalDecl} {layouts : LayoutTable} {slot : LocalSlot}
    {mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout}
    (h : LocalRelLM3_2 mach allocMap decl layouts slot mls) :
    LocalRelLM3_2 mach (allocMap.map f) decl layouts slot mls := by
  cases h with
  | lm3_1 h => exact .lm3_1 (h.map_preserve f htag halloc)
  | ref p mptr cl mutability pointeeKind hc hty hptr =>
    exact .ref p mptr cl mutability pointeeKind hc hty (hptr.map_preserve f htag halloc)

/-- `LocalRelLM3_2` survives growing the live allocations while keeping every
existing base address. -/
theorem of_live_base
    {mach mach' : AnnealMachine} {allocMap : List AllocMapEntry}
    {decl : LocalDecl} {layouts : LayoutTable} {slot : LocalSlot}
    {mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout}
    (hlive : ∀ e, e ∈ mach.memory.live.toList → e ∈ mach'.memory.live.toList)
    (hbase : ∀ a la, (a, la) ∈ mach.memory.live.toList →
      mach'.lookupBaseAddr a = mach.lookupBaseAddr a)
    (h : LocalRelLM3_2 mach allocMap decl layouts slot mls) :
    LocalRelLM3_2 mach' allocMap decl layouts slot mls := by
  cases h with
  | lm3_1 h => exact .lm3_1 (h.of_live_base hlive hbase)
  | ref p mptr cl mutability pointeeKind hc hty hptr =>
    exact .ref p mptr cl mutability pointeeKind hc hty hptr

/-- A memory-backed local related by `LocalRelLM3_2` is related by `LocalRel`
(safe-reference locals are immediate). -/
theorem indirect_base {mach : AnnealMachine} {allocMap : List AllocMapEntry}
    {decl : LocalDecl} {layouts : LayoutTable} {slot : LocalSlot}
    {mp : Miri.Interpreter.MemPlace AnnealProv} {lay : Option Miri.Interpreter.LocalLayout}
    (h : LocalRelLM3_2 mach allocMap decl layouts slot ⟨.live (.indirect mp), lay⟩) :
    LocalRelLM3_1 mach allocMap decl layouts slot ⟨.live (.indirect mp), lay⟩ := by
  cases h with
  | lm3_1 h => exact h

end LocalRelLM3_2

/-- `FrameRelLM3_1` with locals related by `LocalRelLM3_2`. -/
structure FrameRelLM3_2
    (body : CapturedMir) (mach : AnnealMachine) (allocMap : List AllocMapEntry)
    (af : StackFrame)
    (mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit) : Prop where
  /-- `mf.body` is the translation of `body`. -/
  body_eq : mf.body = translateBody body
  /-- `mf.location` is `.mir ⟨af.blockIdx, af.stmtIdx⟩`. -/
  location_eq : mf.location = .mir ⟨af.blockIdx, af.stmtIdx⟩
  /-- `af.locals` has one slot per declared local. -/
  af_locals_len : af.locals.length = body.localDecls.length
  /-- `mf.locals` has one state per declared local. -/
  mf_locals_size : mf.locals.size = body.localDecls.length
  /-- Pointwise correspondence of every local via `LocalRelLM3_2`. -/
  locals_rel :
    ∀ (i : Nat) (decl : LocalDecl) (slot : LocalSlot)
      (mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout),
      get? body.localDecls i = some decl →
      get? af.locals i = some slot →
      mf.locals[i]? = some mls →
      LocalRelLM3_2 mach allocMap decl body.layouts slot mls

/-- Simulation relation between an Anneal `MachineState` and a single-frame
`AnnealStepState` in which locals may hold raw pointers and safe references to
address-taken locals: `StateRelLM3_1` with `FrameRelLM3_2` in place of
`FrameRelLM3_1`. Every borrow entry is still the root borrow of an `allocMap`
entry (`borrows_eq`) that `AllocMapRel` ties to its `lean-miri` stack
allocation, so `StateRelLM3_1.toLM3_2` embeds every `LM-3.1` state. -/
inductive StateRelLM3_2
    (body : CapturedMir) (s : MachineState) (m : AnnealStepState)
    (allocMap : List AllocMapEntry) : Prop where
  | mk
      (topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
      (frames_eq : m.stack.frames = #[topFrame])
      (returnContinuation_eq : topFrame.returnContinuation = .stop false)
      (returnPlace_eq :
        ∃ retLay,
          topFrame.returnPlace =
            .frameLocal 0 0 none retLay topFrame.localsIdentity)
      (frame_rel : FrameRelLM3_2 body m.machine allocMap s.frame topFrame)
      (activeCallee_none : s.memory.activeCallee = none)
      (callStack_nil : s.memory.callStack = .nil)
      (activeProtectors_nil : s.memory.activeProtectors = .nil)
      (callerLocals_nil : s.memory.callerLocals = .nil)
      (borrows_eq : s.memory.borrows = allocMap.map AllocMapEntry.toBorrowEntry)
      (alloc_rel : AllocMapRel body s m allocMap)
      (memoryAllocDisjoint : MemoryAllocDisjoint topFrame) :
      StateRelLM3_2 body s m allocMap

/-- `ImmediateRelLM3_1` extended with safe-reference immediates related by
`PtrRel allocMap`. -/
inductive ImmediateRelLM3_2
    (allocMap : List AllocMapEntry) (ty : Ty) (layouts : LayoutTable) :
    Value → Miri.Interpreter.Immediate AnnealProv → Prop where
  /-- Any value related by `ImmediateRelLM3_1`. -/
  | lm3_1 {v : Value} {imm : Miri.Interpreter.Immediate AnnealProv} :
      ImmediateRelLM3_1 allocMap ty layouts v imm →
      ImmediateRelLM3_2 allocMap ty layouts v imm
  /-- A safe reference `.ptr p 8` at type `.ref mutability pointeeKind`. -/
  | ref (mutability : Mutability) (pointeeKind : RigidTy)
      (p : ProvenancePtr) (mptr : Miri.Memory.Pointer AnnealProv) :
      ty.kind = .ref mutability pointeeKind →
      PtrRel allocMap p mptr →
      ImmediateRelLM3_2 allocMap ty layouts
        (.ptr p 8)
        (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))

/-- Outcome correspondence for one step between `StateRelLM3_2`-related states,
mirroring `StepRelLM3_1`: both machines take a normal step to states related
under `allocMap`, both return from the root frame with related return values,
or both report undefined behavior. -/
inductive StepRelLM3_2 (body : CapturedMir) (m : AnnealStepState)
    (allocMap : List AllocMapEntry) :
    MirStepNode → Miri.Interpreter.StepResult AnnealStepState Bool → Prop where
  /-- Normal intra-frame step to `StateRelLM3_2`-related states. -/
  | step (s' : MachineState) (m' : AnnealStepState) :
      StateRelLM3_2 body s' m' allocMap →
      StepRelLM3_2 body m allocMap (MirStepNode.step s') (m', .ok true)
  /-- Normal root-frame return with `ImmediateRelLM3_2`-related return values. -/
  | retRoot (decl0 : LocalDecl) (retVal : Value)
      (imm0 : Miri.Interpreter.Immediate AnnealProv)
      (mem' : Memory) (m' : AnnealStepState) :
      get? body.localDecls 0 = some decl0 →
      annealControlHooks.returnOperand () m = (m, .ok (.immediate imm0)) →
      ImmediateRelLM3_2 allocMap decl0.ty body.layouts retVal imm0 →
      m' = { m with stack := ⟨#[]⟩ } →
      StepRelLM3_2 body m allocMap (MirStepNode.retNormal retVal mem') (m', .ok true)
  /-- Both machines report undefined behavior. -/
  | ub (m' : AnnealStepState) (msg : String) :
      StepRelLM3_2 body m allocMap (MirStepNode.fail .ub)
        (m', .error (.undefinedBehavior msg))

/-! ### Embedding `LM-3.1` into `LM-3.2` -/

/-- Every `FrameRelLM3_1` is a `FrameRelLM3_2`. -/
theorem FrameRelLM3_1.toLM3_2 {body : CapturedMir} {mach : AnnealMachine}
    {allocMap : List AllocMapEntry} {af : StackFrame}
    {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (h : FrameRelLM3_1 body mach allocMap af mf) :
    FrameRelLM3_2 body mach allocMap af mf where
  body_eq := h.body_eq
  location_eq := h.location_eq
  af_locals_len := h.af_locals_len
  mf_locals_size := h.mf_locals_size
  locals_rel i decl slot mls hdecl hslot hmls :=
    .lm3_1 (h.locals_rel i decl slot mls hdecl hslot hmls)

/-- Every `StateRelLM3_1` state is a `StateRelLM3_2` state. -/
theorem StateRelLM3_1.toLM3_2 {body : CapturedMir} {s : MachineState}
    {m : AnnealStepState} {allocMap : List AllocMapEntry}
    (h : StateRelLM3_1 body s m allocMap) : StateRelLM3_2 body s m allocMap := by
  rcases h with ⟨tf, hframes, hretCont, hretPlace, hfr, hcal, hstack, hprot, hcaller, hbor,
    halloc, hdisj⟩
  exact .mk tf hframes hretCont hretPlace hfr.toLM3_2 hcal hstack hprot hcaller hbor halloc
    hdisj

/-- Every `StepRelLM3_1` outcome is a `StepRelLM3_2` outcome. -/
theorem StepRelLM3_1.toLM3_2 {body : CapturedMir} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    {aRes : MirStepNode} {mRes : Miri.Interpreter.StepResult AnnealStepState Bool}
    (h : StepRelLM3_1 body m allocMap aRes mRes) : StepRelLM3_2 body m allocMap aRes mRes := by
  cases h with
  | step s' m' hrel => exact .step s' m' hrel.toLM3_2
  | retRoot decl0 retVal imm0 mem' m' hdecl hret himm hm =>
    exact .retRoot decl0 retVal imm0 mem' m' hdecl hret
      (.lm3_1 (.of_immediateRel himm)) hm
  | ub m' msg => exact .ub m' msg

/-- A `FrameRelLM3_2` in which no local holds a safe reference is a
`FrameRelLM3_1`. -/
theorem FrameRelLM3_2.toLM3_1 {body : CapturedMir} {mach : AnnealMachine}
    {allocMap : List AllocMapEntry} {af : StackFrame}
    {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (h : FrameRelLM3_2 body mach allocMap af mf)
    (hnoref : ∀ i decl, get? body.localDecls i = some decl →
      ∀ mutability pointeeKind, decl.ty.kind ≠ .ref mutability pointeeKind) :
    FrameRelLM3_1 body mach allocMap af mf where
  body_eq := h.body_eq
  location_eq := h.location_eq
  af_locals_len := h.af_locals_len
  mf_locals_size := h.mf_locals_size
  locals_rel i decl slot mls hdecl hslot hmls := by
    cases h.locals_rel i decl slot mls hdecl hslot hmls with
    | lm3_1 h' => exact h'
    | ref _ _ _ mutability pointeeKind _ hty _ =>
      exact absurd hty (hnoref i decl hdecl mutability pointeeKind)

/-- A `StateRelLM3_2` state of a body without safe-reference locals is a
`StateRelLM3_1` state, so every `LM-3.1` step theorem applies to it. -/
theorem StateRelLM3_2.toLM3_1 {body : CapturedMir} {s : MachineState}
    {m : AnnealStepState} {allocMap : List AllocMapEntry}
    (h : StateRelLM3_2 body s m allocMap)
    (hnoref : ∀ i decl, get? body.localDecls i = some decl →
      ∀ mutability pointeeKind, decl.ty.kind ≠ .ref mutability pointeeKind) :
    StateRelLM3_1 body s m allocMap := by
  rcases h with ⟨tf, hframes, hretCont, hretPlace, hfr, hcal, hstack, hprot, hcaller, hbor,
    halloc, hdisj⟩
  exact .mk tf hframes hretCont hretPlace (hfr.toLM3_1 hnoref) hcal hstack hprot hcaller hbor
    halloc hdisj

/-! ### Frame and state lemmas -/

namespace FrameRelLM3_2

/-- Look up a declared local in `FrameRelLM3_2`-related frames. -/
theorem lookup_local
    {body : CapturedMir} {mach : AnnealMachine} {allocMap : List AllocMapEntry}
    {af : StackFrame} {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hfr : FrameRelLM3_2 body mach allocMap af mf)
    {idx : Nat} {decl : LocalDecl}
    (hdecl : get? body.localDecls idx = some decl) :
    ∃ (slot : LocalSlot) (mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout)
      (_ : idx < af.locals.length) (hlt_mf : idx < mf.locals.size),
      get? af.locals idx = some slot ∧
      mf.locals[idx]? = some mls ∧
      mf.locals[idx]'hlt_mf = mls ∧
      LocalRelLM3_2 mach allocMap decl body.layouts slot mls := by
  have hlt_body : idx < body.localDecls.length := by
    rw [get?_eq_getElem?] at hdecl
    exact (List.getElem?_eq_some_iff.mp hdecl).1
  have hlt_af : idx < af.locals.length := by
    rw [hfr.af_locals_len]; exact hlt_body
  have hlt_mf : idx < mf.locals.size := by
    rw [hfr.mf_locals_size]; exact hlt_body
  have hslot : get? af.locals idx = some (af.locals[idx]'hlt_af) := by
    rw [get?_eq_getElem?, List.getElem?_eq_getElem hlt_af]
  have hmls : mf.locals[idx]? = some (mf.locals[idx]'hlt_mf) :=
    Array.getElem?_eq_getElem hlt_mf
  exact ⟨af.locals[idx]'hlt_af, mf.locals[idx]'hlt_mf, hlt_af, hlt_mf, hslot, hmls, rfl,
    hfr.locals_rel idx decl _ _ hdecl hslot hmls⟩

/-- Memoizing a local's layout preserves `FrameRelLM3_2`. -/
theorem cache_local_layout
    {body : CapturedMir} {mach : AnnealMachine} {allocMap : List AllocMapEntry}
    {af : StackFrame} {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hfr : FrameRelLM3_2 body mach allocMap af mf)
    {idx : Nat} {decl : LocalDecl}
    (hdecl : get? body.localDecls idx = some decl)
    (hlt : idx < mf.locals.size) :
    FrameRelLM3_2 body mach allocMap af
      (cacheFrameLocalLayout mf idx hlt (translateTy decl.ty body.layouts)) where
  body_eq := hfr.body_eq
  location_eq := hfr.location_eq
  af_locals_len := hfr.af_locals_len
  mf_locals_size := by rw [cacheFrameLocalLayout_size, hfr.mf_locals_size]
  locals_rel i decl_i slot_i mls_i hdecl_i hslot_i hmls_i := by
    dsimp only [cacheFrameLocalLayout] at hmls_i
    rw [Array.getElem?_set] at hmls_i
    by_cases h_eq : idx = i
    · subst h_eq
      simp only [↓reduceIte, Option.some.injEq] at hmls_i
      have hdecl_eq : decl = decl_i := by
        rw [hdecl] at hdecl_i; exact Option.some.inj hdecl_i
      subst hdecl_eq hmls_i
      generalize hls0 : (mf.locals[idx]'hlt) = mls0
      have hmls0 : mf.locals[idx]? = some mls0 := by
        rw [← hls0]; exact Array.getElem?_eq_getElem hlt
      have hrel0 := hfr.locals_rel idx decl slot_i mls0 hdecl hslot_i hmls0
      cases hrel0 with
      | lm3_1 h1 =>
        cases h1 with
        | base hb =>
          cases hb with
          | dead _ _ =>
            exact .lm3_1 (.base (.dead _ (fun _ hl => (Option.some.inj hl).symm)))
          | immediate _ imm _ _ hv =>
            exact .lm3_1
              (.base (.immediate slot_i imm _ (fun _ hl => (Option.some.inj hl).symm) hv))
          | indirect _ mp _ _ hne hmp =>
            exact .lm3_1
              (.base (.indirect slot_i mp _ (fun _ hl => (Option.some.inj hl).symm) hne hmp))
        | rawPtr p mptr _ mutability pointeeKind _ hty hptr =>
          exact .lm3_1 (.rawPtr p mptr _ mutability pointeeKind
            (fun _ hl => (Option.some.inj hl).symm) hty hptr)
      | ref p mptr _ mutability pointeeKind _ hty hptr =>
        exact .ref p mptr _ mutability pointeeKind
          (fun _ hl => (Option.some.inj hl).symm) hty hptr
    · simp only [h_eq, ↓reduceIte] at hmls_i
      exact hfr.locals_rel i decl_i slot_i mls_i hdecl_i hslot_i hmls_i

/-- `FrameRelLM3_2` survives extending `allocMap` with another entry. -/
theorem mono_cons
    {body : CapturedMir} {mach : AnnealMachine} {allocMap : List AllocMapEntry}
    (e : AllocMapEntry)
    {af : StackFrame} {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hfr : FrameRelLM3_2 body mach allocMap af mf) :
    FrameRelLM3_2 body mach (e :: allocMap) af mf where
  body_eq := hfr.body_eq
  location_eq := hfr.location_eq
  af_locals_len := hfr.af_locals_len
  mf_locals_size := hfr.mf_locals_size
  locals_rel i decl slot mls hdecl hslot hmls :=
    (hfr.locals_rel i decl slot mls hdecl hslot hmls).mono_cons e

/-- `FrameRelLM3_2` survives growing the live allocations while keeping every
existing base address. -/
theorem of_live_base
    {body : CapturedMir} {mach mach' : AnnealMachine} {allocMap : List AllocMapEntry}
    {af : StackFrame} {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hlive : ∀ e, e ∈ mach.memory.live.toList → e ∈ mach'.memory.live.toList)
    (hbase : ∀ a la, (a, la) ∈ mach.memory.live.toList →
      mach'.lookupBaseAddr a = mach.lookupBaseAddr a)
    (h : FrameRelLM3_2 body mach allocMap af mf) :
    FrameRelLM3_2 body mach' allocMap af mf where
  body_eq := h.body_eq
  location_eq := h.location_eq
  af_locals_len := h.af_locals_len
  mf_locals_size := h.mf_locals_size
  locals_rel i decl slot mls hdecl hslot hmls :=
    (h.locals_rel i decl slot mls hdecl hslot hmls).of_live_base hlive hbase

/-- Replace one local of `FrameRelLM3_2`-related frames by `LocalRelLM3_2`-related
values. -/
theorem update_local
    {body : CapturedMir} {mach : AnnealMachine} {allocMap : List AllocMapEntry}
    {af : StackFrame} {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hrel : FrameRelLM3_2 body mach allocMap af mf)
    {idx : Nat} {decl : LocalDecl}
    (hdecl : get? body.localDecls idx = some decl)
    {hlt_mf : idx < mf.locals.size}
    (newSlot : LocalSlot) (newVal : Miri.Interpreter.LocalValue AnnealProv)
    (hnew : LocalRelLM3_2 mach allocMap decl body.layouts newSlot
      { mf.locals[idx]'hlt_mf with value := newVal }) :
    FrameRelLM3_2 body mach allocMap
      { af with locals := af.locals.set idx newSlot }
      { mf with locals := mf.locals.set idx { mf.locals[idx]'hlt_mf with value := newVal } hlt_mf } where
  body_eq := hrel.body_eq
  location_eq := hrel.location_eq
  af_locals_len := by rw [List.length_set, hrel.af_locals_len]
  mf_locals_size := by rw [Array.size_set, hrel.mf_locals_size]
  locals_rel i decl_i slot_i mls_i hdecl_i hslot_i hmls_i := by
    have hlt_af : idx < af.locals.length := by
      rw [hrel.af_locals_len, ← hrel.mf_locals_size]; exact hlt_mf
    rw [get?_eq_getElem?, List.getElem?_set] at hslot_i
    rw [Array.getElem?_set] at hmls_i
    by_cases h_eq : idx = i
    · subst h_eq
      simp only [↓reduceIte, hlt_af, Option.some.injEq] at hslot_i hmls_i
      have hdecl_eq : decl_i = decl := by
        rw [hdecl] at hdecl_i; exact Option.some.inj hdecl_i.symm
      subst hdecl_eq hslot_i hmls_i
      exact hnew
    · simp only [h_eq, ↓reduceIte] at hslot_i hmls_i
      exact hrel.locals_rel i decl_i slot_i mls_i hdecl_i hslot_i hmls_i

/-- Every memory-backed local of `FrameRelLM3_2`-related frames owns a live
allocation. -/
theorem indirect_allocId
    {body : CapturedMir} {mach : AnnealMachine} {allocMap : List AllocMapEntry}
    {af : StackFrame} {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hfr : FrameRelLM3_2 body mach allocMap af mf)
    {j : Nat} {mp : Miri.Interpreter.MemPlace AnnealProv}
    {lay : Option Miri.Interpreter.LocalLayout}
    (hj : mf.locals[j]? = some ⟨.live (.indirect mp), lay⟩) :
    ∃ a la, mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId = some a ∧
      (a, la) ∈ mach.memory.live.toList := by
  obtain ⟨hlt_j, _⟩ := Array.getElem?_eq_some_iff.mp hj
  have hlt_d : j < body.localDecls.length := by rw [← hfr.mf_locals_size]; exact hlt_j
  have hdecl : get? body.localDecls j = some (body.localDecls[j]'hlt_d) :=
    List.getElem?_eq_getElem hlt_d
  obtain ⟨_, mls, _, _, _, hmls, _, hloc⟩ := hfr.lookup_local hdecl
  rw [hj] at hmls
  cases hmls
  cases hloc.indirect_base with
  | base hb =>
    cases hb with
    | indirect _ _ _ _ _ hmp =>
      obtain ⟨allocId, tag, _, _, localAlloc, hprov, _, _, hl, _⟩ := hmp
      exact ⟨allocId, localAlloc, by rw [hprov]; rfl, hl⟩

/-- Advancing the statement index preserves `FrameRelLM3_2`. -/
theorem advance
    {body : CapturedMir} {mach : AnnealMachine} {allocMap : List AllocMapEntry}
    {af : StackFrame} {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (h : FrameRelLM3_2 body mach allocMap af mf) :
    FrameRelLM3_2 body mach allocMap
      { af with stmtIdx := Nat.add af.stmtIdx 1 }
      { mf with location := .mir ⟨af.blockIdx, af.stmtIdx + 1⟩ } where
  body_eq := h.body_eq
  location_eq := rfl
  af_locals_len := h.af_locals_len
  mf_locals_size := h.mf_locals_size
  locals_rel := h.locals_rel

end FrameRelLM3_2

namespace StateRelLM3_2

/-- The root frame of a `StateRelLM3_2` state is `FrameRelLM3_2`-related. -/
theorem frame_rel_singleton
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf]) :
    FrameRelLM3_2 body m.machine allocMap s.frame tf := by
  obtain ⟨tf', hframes', _, _, hfr, _, _, _, _, _, _, _⟩ := id hstate
  rw [hframes] at hframes'
  injection hframes' with h1
  injection h1 with h2
  subst h2
  exact hfr

/-- `StateRelLM3_2` survives memoizing a local's declared layout in the root
frame, as `annealEvalPlace` and `annealEvalOperand` do. -/
theorem cache_layout
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf])
    {idx : Nat} {decl : LocalDecl} (hdecl : get? body.localDecls idx = some decl)
    (hlt : idx < tf.locals.size) :
    StateRelLM3_2 body s
      { m with stack := ⟨#[cacheFrameLocalLayout tf idx hlt
          (translateTy decl.ty body.layouts)]⟩ }
      allocMap := by
  rcases hstate with
    ⟨tf₀, hframes₀, hretCont, hretPlace, hfr, hcal, hstack, hprot, hcaller, hbor, halloc, hdisj⟩
  rw [hframes] at hframes₀
  injection hframes₀ with h₀
  injection h₀ with htf
  subst htf
  refine .mk _ rfl hretCont hretPlace (hfr.cache_local_layout hdecl hlt) hcal hstack hprot
    hcaller hbor ?_ ?_
  · refine ⟨halloc.tags_nodup, halloc.local_to_alloc_unique, halloc.alloc_to_local_injective,
      halloc.target_decl, halloc.base_addr_valid, halloc.borrow_sync, halloc.live_key_unique, ?_⟩
    intro topFrame htop e he
    injection htop with h₁
    injection h₁ with h₂
    subst h₂
    obtain ⟨hlive_e, hdead_e⟩ := halloc.local_alloc_sync tf hframes e he
    refine ⟨fun slot hslot hne => ?_, hdead_e⟩
    obtain ⟨⟨lay, hlay⟩, hshape⟩ := hlive_e slot hslot hne
    refine ⟨?_, hshape⟩
    by_cases hk : idx = e.localIdx
    · subst hk
      refine ⟨some (translateTy decl.ty body.layouts), ?_⟩
      dsimp only [cacheFrameLocalLayout]
      rw [Array.getElem?_set_self]
      have hget : tf.locals[e.localIdx]? = some (tf.locals[e.localIdx]'hlt) :=
        Array.getElem?_eq_getElem hlt
      rw [hget] at hlay
      injection hlay with hls
      rw [hls]
    · refine ⟨lay, ?_⟩
      dsimp only [cacheFrameLocalLayout]
      rw [Array.getElem?_set_ne _ hk]
      exact hlay
  · apply MemoryAllocDisjoint.mono_layout hdisj
    intro k
    by_cases hk : k = idx
    · subst hk
      refine ⟨translateTy decl.ty body.layouts, ?_⟩
      dsimp only [cacheFrameLocalLayout]
      rw [Array.getElem?_set_self, Array.getElem?_eq_getElem hlt]
      rfl
    · refine ⟨(tf.locals[k]?).bind (fun x => x.layout), ?_⟩
      dsimp only [cacheFrameLocalLayout]
      rw [Array.getElem?_set_ne _ (Ne.symm hk)]
      cases tf.locals[k]? <;> rfl

/-- Any live immediate local in a `StateRelLM3_2`-related frame is absent from
`allocMap`: every live mapped local is memory-backed (`local_alloc_sync`). -/
theorem immediate_not_in_allocMap
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf])
    {idx : Local} {slot : LocalSlot}
    (hslot : get? s.frame.locals idx = some slot)
    (hne_dead : slot ≠ .dead)
    (himm : IsImmediateFrameLocal tf idx) :
    ∀ e ∈ allocMap, e.localIdx ≠ idx := by
  rcases hstate with ⟨_, _, _, _, _, _, _, _, _, _, halloc, _⟩
  intro e he heq
  subst heq
  obtain ⟨⟨lay, hlay⟩, _⟩ := (halloc.local_alloc_sync tf hframes e he).1
    slot hslot hne_dead
  exact himm _ hlay (stackAllocPlace e.allocId) rfl

end StateRelLM3_2

/-! ## 2. Eager Safe-Reference Dereference Checks (`annealSafeRefDerefCheck`) -/

/-- A stack address `annealStackBaseAddr id + offsetBytes` is never null: the
allocation id is non-zero, so the base address is at least `2 ^ 32`. -/
theorem annealStackBaseAddr_add_ne_zero (id : Miri.Memory.AllocId) (offsetBytes : Nat)
    (hid : id.value.toNat < 2 ^ 32) (hoff : offsetBytes < 2 ^ 32) :
    (annealStackBaseAddr id + UInt64.ofNat offsetBytes == 0) = false := by
  have hno := PtrRel.base_add_offset_lt_u64 id offsetBytes hid hoff
  have hbase : (annealStackBaseAddr id).toNat = id.value.toNat * 2 ^ 32 := by
    unfold annealStackBaseAddr
    rw [UInt64.toNat_shiftLeft]
    have hlt64 : id.value.toNat * 2 ^ 32 < 2 ^ 64 := by omega
    simp [Nat.shiftLeft_eq, Nat.mod_eq_of_lt hlt64]
  have hpos : 0 < id.value.toNat := by
    have hne := id.nonzero
    have : id.value.toNat ≠ 0 := fun h => hne (UInt64.toNat_inj.mp (by simpa using h))
    omega
  have hoff64 : offsetBytes < 2 ^ 64 := by omega
  have hu64 : (UInt64.ofNat offsetBytes).toNat = offsetBytes := UInt64.toNat_ofNat_of_lt hoff64
  have hsum : (annealStackBaseAddr id + UInt64.ofNat offsetBytes).toNat =
      (annealStackBaseAddr id).toNat + offsetBytes := by
    rw [UInt64.toNat_add, hu64, Nat.mod_eq_of_lt hno]
  cases h : (annealStackBaseAddr id + UInt64.ofNat offsetBytes == 0) with
  | false => rfl
  | true =>
    have h0 := (beq_iff_eq.mp h)
    have : (annealStackBaseAddr id + UInt64.ofNat offsetBytes).toNat = 0 := by rw [h0]; rfl
    omega

/-- **Live, in-bounds, aligned safe reference**: the eager checks of
`annealSafeRefDerefCheck` accept a reference into a live stack allocation whose
pointee of `sizeBytes > 0` bytes fits at `offsetBytes` and whose address is
aligned to the pointee's ABI alignment, yielding the uncached-misalignment
memory place at that address. -/
theorem annealSafeRefDerefCheck_live_ok
    {mach : AnnealMachine} (id : Miri.Memory.AllocId) (borTag : Miri.Memory.BorTag)
    (offsetBytes : Nat) (pointeeLay : Miri.Interpreter.LocalLayout)
    (localAlloc :
      Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind)
    (hid : id.value.toNat < 2 ^ 32) (hoff : offsetBytes < 2 ^ 32)
    (hbase : mach.lookupBaseAddr id = some (annealStackBaseAddr id))
    (hlive : mach.memory.live.find? (fun entry => entry.1 == id) = some (id, localAlloc))
    (hsz : Miri.Memory.sizeAsI64 pointeeLay.layout.size =
      .ok (pointeeLay.layout.size.bytes.toNat : Int))
    (hpos : 0 < pointeeLay.layout.size.bytes.toNat)
    (hfit : (pointeeLay.layout.size.bytes.toNat : Int) < 2 ^ 63)
    (hinbounds : offsetBytes + pointeeLay.layout.size.bytes.toNat ≤
      localAlloc.allocation.byteSize.bytes.toNat)
    (haligned : annealOffsetMisalignment
      (Miri.ABI.Size.ofBytes (annealStackBaseAddr id + UInt64.ofNat offsetBytes))
      pointeeLay.layout.align.abi = .ok none) :
    annealSafeRefDerefCheck mach
        (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
          ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr id + UInt64.ofNat offsetBytes),
            .concrete id borTag⟩))
        pointeeLay =
      .ok ⟨⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr id + UInt64.ofNat offsetBytes),
        some (.concrete id borTag)⟩, .none, none⟩ := by
  have hnn := annealStackBaseAddr_add_ne_zero id offsetBytes hid hoff
  have hck := checkAndDerefPtr_live_inbounds_ok (mach := mach) id borTag offsetBytes
    pointeeLay.layout.size.bytes.toNat localAlloc (.dereferenceable "pointer") hid hoff hbase
    hlive hpos hfit hinbounds
  unfold annealSafeRefDerefCheck
  simp only [Miri.Interpreter.Immediate.toScalar, scalar_fromPointer_toPointer_eq,
    Miri.Memory.Pointer.withOptionalProvenance]
  rw [show (Miri.ABI.Size.ofBytes (annealStackBaseAddr id + UInt64.ofNat offsetBytes)).bytes =
    annealStackBaseAddr id + UInt64.ofNat offsetBytes from rfl]
  rw [hnn]
  simp only [Bool.false_eq_true, ↓reduceIte]
  split
  · rename_i heq
    rw [hsz] at heq
    cases heq
  · rename_i signedSize heq
    rw [hsz] at heq
    cases heq
    rw [hck]
    dsimp only
    rw [haligned]

/-- **Dangling safe reference (dead allocation)**: the eager checks of
`annealSafeRefDerefCheck` reject a reference into a deallocated stack
allocation (for example after `StorageDead`) with undefined behavior. -/
theorem annealSafeRefDerefCheck_dead_err
    {mach : AnnealMachine} (id : Miri.Memory.AllocId) (borTag : Miri.Memory.BorTag)
    (offsetBytes : Nat) (pointeeLay : Miri.Interpreter.LocalLayout)
    (hid : id.value.toNat < 2 ^ 32) (hoff : offsetBytes < 2 ^ 32)
    (hbase : mach.lookupBaseAddr id = some (annealStackBaseAddr id))
    (hdead : mach.memory.live.find? (fun entry => entry.1 == id) = none)
    (hsz : Miri.Memory.sizeAsI64 pointeeLay.layout.size =
      .ok (pointeeLay.layout.size.bytes.toNat : Int))
    (hpos : 0 < pointeeLay.layout.size.bytes.toNat)
    (hfit : (pointeeLay.layout.size.bytes.toNat : Int) < 2 ^ 63) :
    annealSafeRefDerefCheck mach
        (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
          ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr id + UInt64.ofNat offsetBytes),
            .concrete id borTag⟩))
        pointeeLay =
      .error (.undefinedBehavior "dereferencing a dangling reference") := by
  have hnn := annealStackBaseAddr_add_ne_zero id offsetBytes hid hoff
  have hck := checkAndDerefPtr_deadAlloc_err (mach := mach) id borTag offsetBytes
    (pointeeLay.layout.size.bytes.toNat : Int) (.dereferenceable "pointer") hid hoff hbase hdead
    (by exact_mod_cast hpos) hfit
  unfold annealSafeRefDerefCheck
  simp only [Miri.Interpreter.Immediate.toScalar, scalar_fromPointer_toPointer_eq,
    Miri.Memory.Pointer.withOptionalProvenance]
  rw [show (Miri.ABI.Size.ofBytes (annealStackBaseAddr id + UInt64.ofNat offsetBytes)).bytes =
    annealStackBaseAddr id + UInt64.ofNat offsetBytes from rfl]
  rw [hnn]
  simp only [Bool.false_eq_true, ↓reduceIte]
  split
  · rename_i heq
    rw [hsz] at heq
    cases heq
  · rename_i signedSize heq
    rw [hsz] at heq
    cases heq
    rw [hck]

/-- **Dangling safe reference (out of bounds)**: the eager checks of
`annealSafeRefDerefCheck` reject a reference whose pointee extends past the end
of its live stack allocation with undefined behavior. -/
theorem annealSafeRefDerefCheck_oob_err
    {mach : AnnealMachine} (id : Miri.Memory.AllocId) (borTag : Miri.Memory.BorTag)
    (offsetBytes : Nat) (pointeeLay : Miri.Interpreter.LocalLayout)
    (localAlloc :
      Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind)
    (hid : id.value.toNat < 2 ^ 32) (hoff : offsetBytes < 2 ^ 32)
    (hbase : mach.lookupBaseAddr id = some (annealStackBaseAddr id))
    (hlive : mach.memory.live.find? (fun entry => entry.1 == id) = some (id, localAlloc))
    (hsz : Miri.Memory.sizeAsI64 pointeeLay.layout.size =
      .ok (pointeeLay.layout.size.bytes.toNat : Int))
    (hpos : 0 < pointeeLay.layout.size.bytes.toNat)
    (hfit : (pointeeLay.layout.size.bytes.toNat : Int) < 2 ^ 63)
    (hoob : localAlloc.allocation.byteSize.bytes.toNat <
      offsetBytes + pointeeLay.layout.size.bytes.toNat) :
    annealSafeRefDerefCheck mach
        (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
          ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr id + UInt64.ofNat offsetBytes),
            .concrete id borTag⟩))
        pointeeLay =
      .error (.undefinedBehavior "dereferencing a dangling reference") := by
  have hnn := annealStackBaseAddr_add_ne_zero id offsetBytes hid hoff
  have hck := checkAndDerefPtr_live_oob_err (mach := mach) id borTag offsetBytes
    pointeeLay.layout.size.bytes.toNat localAlloc (.dereferenceable "pointer") hid hoff hbase
    hlive hpos hfit hoob
  unfold annealSafeRefDerefCheck
  simp only [Miri.Interpreter.Immediate.toScalar, scalar_fromPointer_toPointer_eq,
    Miri.Memory.Pointer.withOptionalProvenance]
  rw [show (Miri.ABI.Size.ofBytes (annealStackBaseAddr id + UInt64.ofNat offsetBytes)).bytes =
    annealStackBaseAddr id + UInt64.ofNat offsetBytes from rfl]
  rw [hnn]
  simp only [Bool.false_eq_true, ↓reduceIte]
  split
  · rename_i heq
    rw [hsz] at heq
    cases heq
  · rename_i signedSize heq
    rw [hsz] at heq
    cases heq
    rw [hck]

/-- **Unaligned safe reference**: the eager checks of `annealSafeRefDerefCheck`
reject an in-bounds reference into a live stack allocation whose address is
not aligned to the pointee's ABI alignment with undefined behavior. -/
theorem annealSafeRefDerefCheck_misaligned_err
    {mach : AnnealMachine} (id : Miri.Memory.AllocId) (borTag : Miri.Memory.BorTag)
    (offsetBytes : Nat) (pointeeLay : Miri.Interpreter.LocalLayout)
    (localAlloc :
      Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind)
    (hid : id.value.toNat < 2 ^ 32) (hoff : offsetBytes < 2 ^ 32)
    (hbase : mach.lookupBaseAddr id = some (annealStackBaseAddr id))
    (hlive : mach.memory.live.find? (fun entry => entry.1 == id) = some (id, localAlloc))
    (hsz : Miri.Memory.sizeAsI64 pointeeLay.layout.size =
      .ok (pointeeLay.layout.size.bytes.toNat : Int))
    (hpos : 0 < pointeeLay.layout.size.bytes.toNat)
    (hfit : (pointeeLay.layout.size.bytes.toNat : Int) < 2 ^ 63)
    (hinbounds : offsetBytes + pointeeLay.layout.size.bytes.toNat ≤
      localAlloc.allocation.byteSize.bytes.toNat)
    {mis : Miri.Memory.Misalignment}
    (hmis : annealOffsetMisalignment
      (Miri.ABI.Size.ofBytes (annealStackBaseAddr id + UInt64.ofNat offsetBytes))
      pointeeLay.layout.align.abi = .ok (some mis)) :
    annealSafeRefDerefCheck mach
        (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
          ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr id + UInt64.ofNat offsetBytes),
            .concrete id borTag⟩))
        pointeeLay =
      .error (.undefinedBehavior "dereferencing an unaligned reference") := by
  have hnn := annealStackBaseAddr_add_ne_zero id offsetBytes hid hoff
  have hck := checkAndDerefPtr_live_inbounds_ok (mach := mach) id borTag offsetBytes
    pointeeLay.layout.size.bytes.toNat localAlloc (.dereferenceable "pointer") hid hoff hbase
    hlive hpos hfit hinbounds
  unfold annealSafeRefDerefCheck
  simp only [Miri.Interpreter.Immediate.toScalar, scalar_fromPointer_toPointer_eq,
    Miri.Memory.Pointer.withOptionalProvenance]
  rw [show (Miri.ABI.Size.ofBytes (annealStackBaseAddr id + UInt64.ofNat offsetBytes)).bytes =
    annealStackBaseAddr id + UInt64.ofNat offsetBytes from rfl]
  rw [hnn]
  simp only [Bool.false_eq_true, ↓reduceIte]
  split
  · rename_i heq
    rw [hsz] at heq
    cases heq
  · rename_i signedSize heq
    rw [hsz] at heq
    cases heq
    rw [hck]
    dsimp only
    rw [hmis]

/-- **Null safe reference**: the eager checks of `annealSafeRefDerefCheck`
reject an integer reference with address `0` with undefined behavior before any
access check. -/
theorem annealSafeRefDerefCheck_int_null_err
    (mach : AnnealMachine) (pointeeLay : Miri.Interpreter.LocalLayout)
    {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    (hrel : ScalarRel sc msc) (hsz8 : sc.sizeBytes = 8) (h0 : sc.bits = 0) :
    annealSafeRefDerefCheck mach (.scalar (Miri.Memory.Scalar.fromScalarInt msc)) pointeeLay =
      .error (.undefinedBehavior "dereferencing a null reference") := by
  unfold annealSafeRefDerefCheck
  simp only [Miri.Interpreter.Immediate.toScalar, scalar_fromScalarInt_toPointer_eq hrel hsz8, h0]
  rfl

/-- **Dangling integer safe reference**: the eager checks of
`annealSafeRefDerefCheck` reject a provenance-free integer reference with a
non-zero address and a pointee of positive size with undefined behavior. -/
theorem annealSafeRefDerefCheck_int_dangling_err
    (mach : AnnealMachine) (pointeeLay : Miri.Interpreter.LocalLayout)
    {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    (hrel : ScalarRel sc msc) (hsz8 : sc.sizeBytes = 8) (hne : sc.bits ≠ 0)
    (hsz : Miri.Memory.sizeAsI64 pointeeLay.layout.size =
      .ok (pointeeLay.layout.size.bytes.toNat : Int))
    (hpos : 0 < pointeeLay.layout.size.bytes.toNat)
    (hfit : (pointeeLay.layout.size.bytes.toNat : Int) < 2 ^ 63) :
    annealSafeRefDerefCheck mach (.scalar (Miri.Memory.Scalar.fromScalarInt msc)) pointeeLay =
      .error (.undefinedBehavior "dereferencing a dangling reference") := by
  have hcan := hrel.canonical
  rw [hsz8] at hcan
  have hlt : sc.bits < 2 ^ 64 := by
    have : scalarModulus 8 = 2 ^ 64 := by decide
    omega
  have hnn : (UInt64.ofNat sc.bits == 0) = false := by
    cases h : (UInt64.ofNat sc.bits == 0) with
    | false => rfl
    | true =>
      have h0 := beq_iff_eq.mp h
      have hu : (UInt64.ofNat sc.bits).toNat = sc.bits := UInt64.toNat_ofNat_of_lt hlt
      have h00 : (UInt64.ofNat sc.bits).toNat = 0 := by rw [h0]; rfl
      rw [hu] at h00
      exact absurd h00 hne
  have hck := checkAndDerefPtr_withoutProvenance_err mach (UInt64.ofNat sc.bits)
    (pointeeLay.layout.size.bytes.toNat : Int) (.dereferenceable "pointer")
    (by exact_mod_cast hpos) hfit
  unfold annealSafeRefDerefCheck
  simp only [Miri.Interpreter.Immediate.toScalar, scalar_fromScalarInt_toPointer_eq hrel hsz8]
  rw [show (Miri.Memory.Pointer.withoutProvenance (Prov := AnnealProv)
      (UInt64.ofNat sc.bits)).offset.bytes = UInt64.ofNat sc.bits from rfl]
  rw [hnn]
  simp only [Bool.false_eq_true, ↓reduceIte]
  split
  · rename_i heq
    rw [hsz] at heq
    cases heq
  · rename_i signedSize heq
    rw [hsz] at heq
    cases heq
    rw [hck]

/-! ## 3. The Vendored Validity Visitor for Anneal (`annealValidityHooks`) -/

/-- Fail-closed `PlaceHooks` for the validity visitor's projection dictionary.
The scalar and reference fragment never projects, re-borrows, or allocates
during validation, so every operation reports `StepError.unsupported`. -/
def annealValidityPlaceHooks :
    Miri.Interpreter.PlaceHooks AnnealProv AnnealStepState Ty Unit where
  getFrame := throw (.unsupported "validity place: getFrame")
  setFrame := fun _ => throw (.unsupported "validity place: setFrame")
  debugAssertions := false
  frameIndex := throw (.unsupported "validity place: frameIndex")
  resolveLayout := fun _ _ => throw (.unsupported "validity place: resolveLayout")
  localToOp := fun _ _ => throw (.unsupported "validity place: localToOp")
  projection := fun _ => throw (.unsupported "validity place: projection")
  deref := fun _ _ _ => throw (.unsupported "validity place: deref")
  checkPlaceType := fun _ _ _ => throw (.unsupported "validity place: checkPlaceType")
  allocateStack := fun _ _ => throw (.unsupported "validity place: allocateStack")
  writeMemoryNoValidate := fun _ _ _ =>
    throw (.unsupported "validity place: writeMemoryNoValidate")
  afterLocalMovedToMemory := fun _ _ _ =>
    throw (.unsupported "validity place: afterLocalMovedToMemory")
  memoryOffset := fun _ _ _ _ _ => throw (.unsupported "validity place: memoryOffset")
  writeLocalImmediate := fun _ _ _ _ =>
    throw (.unsupported "validity place: writeLocalImmediate")
  enforceValidity := fun _ _ => throw (.unsupported "validity place: enforceValidity")
  validate := fun _ _ => throw (.unsupported "validity place: validate")

/-- Fail-closed projection dictionary for the validity visitor: aggregates,
arrays, slices, and enum variants are outside the scalar and reference
fragment, so every projection reports `StepError.unsupported`. -/
def annealValidityProjectionHooks :
    Miri.Interpreter.PlaceProjectionHooks AnnealProv AnnealStepState Ty Unit where
  place := annealValidityPlaceHooks
  target := annealTargetDataLayout
  maxSizeOfVal := Miri.ABI.Size.ofBytes 0x7fffffffffffffff
  dynamic :=
    { target := annealTargetDataLayout
      maxSizeOfVal := Miri.ABI.Size.ofBytes 0x7fffffffffffffff
      classify := fun _ _ => throw (.unsupported "validity dynamic layout: classify")
      field := fun _ _ _ => throw (.unsupported "validity dynamic layout: field")
      packedAlign := fun _ _ => throw (.unsupported "validity dynamic layout: packedAlign")
      vtableSizeAndAlign := fun _ _ _ =>
        throw (.unsupported "validity dynamic layout: vtableSizeAndAlign") }
  dynamicFuel := 0
  isSliceOrStr := fun _ _ => throw (.unsupported "validity projection: isSliceOrStr")
  field := fun _ _ _ => throw (.unsupported "validity projection: field")
  variant := fun _ _ _ => throw (.unsupported "validity projection: variant")
  packedAlign := fun _ _ => throw (.unsupported "validity projection: packedAlign")
  subsliceLayout := fun _ _ _ => throw (.unsupported "validity projection: subsliceLayout")
  layoutOf := fun _ _ => throw (.unsupported "validity projection: layoutOf")
  localIndex := fun _ _ => throw (.unsupported "validity projection: localIndex")

/-- Classify an encoded `TyId` for the validity visitor. The context `c` is
the Anneal type of the validated place: `encodeTyId` maps every reference to
`TyId 41`, so only `c` records whether a reference is mutable. Aggregates and
every other type outside the scalar and reference fragment fail closed with
`StepError.unsupported`, never with a verdict. -/
def annealValidityClassify (c : Ty) (tyId : Miri.MIR.TyId) :
    EStateM Miri.Interpreter.StepError AnnealStepState
      Miri.Interpreter.ValidityVisitor.TypeKind :=
  match tyId with
  | 1 => pure .boolean
  | 2 => pure .character
  | 10 | 11 | 12 | 13 | 14 | 15 | 20 | 21 | 22 | 23 | 24 | 25 => pure .integer
  | 30 | 31 | 32 | 33 => pure .float
  | 41 =>
    match c.kind with
    | .ref .mut _ => pure (.reference true)
    | .ref .not _ => pure (.reference false)
    | _ => throw (.invalidProgram "reference TyId at a non-reference type")
  | 42 => pure .functionPointer
  | 50 => pure .never
  | 60 | 61 | 62 | 63 | 64 | 65 | 66 | 67 | 68 | 69
  | 70 | 71 | 72 | 73 | 74 | 75 | 76 | 77 | 78 | 79 | 80 | 81 | 82 =>
    pure (.rawPointer tyId true)
  | _ => throw (.unsupported "validity of a type outside the scalar and reference fragment")

/-- The pointee layout of a safe reference of Anneal type `c`, for the pointees
whose layout `translateTy` gives exactly (`derefPointeeKindHasExactLayout`). -/
def annealValidityPointeeLayout (layouts : LayoutTable) (c : Ty) :
    Option Miri.Interpreter.LocalLayout :=
  match c.kind with
  | .ref _ pointeeKind =>
    if derefPointeeKindHasExactLayout pointeeKind then
      some (translateTy { kind := pointeeKind, layoutIdx := 0 } layouts)
    else
      none
  | _ => none

/-- The operand that a validated place denotes in the current frame: an
unprojected local's value or a memory place. Dead locals are undefined behavior;
projected local places fail closed. -/
@[irreducible]
def annealValidityPlaceOperand (place : Miri.Interpreter.RuntimePlace AnnealProv) :
    EStateM Miri.Interpreter.StepError AnnealStepState
      (Miri.Interpreter.Operand AnnealProv) := do
  let st ← get
  let some frame := st.stack.currentFrame?
    | throw (.stack .emptyStack)
  match place.ref with
  | .local _ localId none _ =>
    match frame.getLocalOperand localId with
    | .ok op => pure op
    | .error (.localExpectedLive _) => throw (.undefinedBehavior "validation of a dead local")
    | .error e => throw (.stack e)
  | .memory mplace => pure (.indirect mplace)
  | _ => throw (.unsupported "validation of a projected local place")

/-- The dereferenceability check of `ValidityMachine.checkPointerAccessResult`
against the cached base addresses: an access of `size` bytes at `ptr` must lie
in bounds of a live allocation (`Miri.Memory.checkAndDerefPtr` with
`annealResolvePtr`); zero-sized accesses always succeed. -/
def annealValidityAccessCheck (mach : AnnealMachine)
    (ptr : Miri.Memory.Pointer (Option AnnealProv)) (size : Miri.ABI.Size) :
    Except Miri.Memory.AccessError Unit :=
  match Miri.Memory.sizeAsI64 size with
  | .error err => .error err
  | .ok signedSize =>
    match Miri.Memory.checkAndDerefPtr annealPointerArithmetic ptr signedSize
        (.dereferenceable "pointer") (annealResolvePtr mach) (annealLookupAlloc mach) with
    | .ok _ => .ok ()
    | .error err => .error err

/-- The vendored validity visitor's `Hooks` instantiated for Anneal's
single-threaded machine, with the Anneal type of the validated place as
context (`annealValidityClassify`, `annealValidityPointeeLayout`).

* `readImmediate` reads through `annealReadImmediate`, so uninitialized
  values are undefined behavior.
* `ptrToPlace` turns a reference into its pointee place, caching numeric
  misalignment like `PointerPlaceMachine.fromImmediate`.
* `checkPointerAccess`, `checkPointerAlignResult`, and `scalarMayBeNull`
  are the address-based checks of `ValidityMachine` against the cached base
  addresses (`annealResolvePtr`, `annealLookupAlloc`, `annealOffsetMisalignment`).
* Retagging (`retagPointer`), provenance and padding resets, and ghost
  validation are no-ops: Tree Borrows retags are `LM-3.3`'s subject, and the
  scalar and reference fragment has neither provenance-carrying integers nor
  padding.
* Everything else that only aggregates, slices, trait objects, boxes, or
  constant evaluation reach fails closed with `StepError.unsupported`. -/
def annealValidityHooks (layouts : LayoutTable) :
    Miri.Interpreter.ValidityVisitor.Hooks AnnealProv AnnealStepState Ty Unit Unit Unit Unit where
  target := annealRuntimeDataLayout
  projection := annealValidityProjectionHooks
  vtable :=
    { target := annealTargetDataLayout
      isDynamic := fun _ _ => throw (.unsupported "validity vtable: isDynamic")
      memoryOffset := fun _ _ _ _ _ => throw (.unsupported "validity vtable: memoryOffset")
      resolvePointer := fun _ _ => throw (.unsupported "validity vtable: resolvePointer")
      globalVTable := fun _ _ => throw (.unsupported "validity vtable: globalVTable")
      globalFunction := fun _ _ => throw (.unsupported "validity vtable: globalFunction")
      predicates := fun _ _ => throw (.unsupported "validity vtable: predicates")
      normalizePredicate := fun _ _ => throw (.unsupported "validity vtable: normalizePredicate")
      layoutOf := fun _ _ => throw (.unsupported "validity vtable: layoutOf")
      eraseAndAnonymize := fun _ _ _ => throw (.unsupported "validity vtable: eraseAndAnonymize")
      ensureMonomorphicType := fun _ _ =>
        throw (.unsupported "validity vtable: ensureMonomorphicType")
      ensureMonomorphicDyn := fun _ _ =>
        throw (.unsupported "validity vtable: ensureMonomorphicDyn")
      globalSalt := fun _ => throw (.unsupported "validity vtable: globalSalt")
      reserveVTable := fun _ _ _ _ => throw (.unsupported "validity vtable: reserveVTable")
      globalRootPointer := fun _ _ => throw (.unsupported "validity vtable: globalRootPointer")
      entries := fun _ _ _ => throw (.unsupported "validity vtable: entries")
      assertVirtualInstanceMatches := fun _ _ _ _ _ =>
        throw (.unsupported "validity vtable: assertVirtualInstanceMatches") }
  discriminant :=
    { runtimeTarget := annealRuntimeDataLayout
      discriminantLayout := fun _ _ => throw (.unsupported "validity discriminant: layout")
      tagLayout := fun _ _ => throw (.unsupported "validity discriminant: tagLayout")
      discriminantValue := fun _ _ _ => throw (.unsupported "validity discriminant: value")
      variantForDiscriminant := fun _ _ _ =>
        throw (.unsupported "validity discriminant: variantForDiscriminant")
      adtVariantCount := fun _ _ => throw (.unsupported "validity discriminant: adtVariantCount")
      projectRead := fun _ _ _ => throw (.unsupported "validity discriminant: projectRead")
      readImmediate := fun _ _ => throw (.unsupported "validity discriminant: readImmediate")
      destLayout := fun v => v.layout
      projectWrite := fun _ _ _ => throw (.unsupported "validity discriminant: projectWrite")
      writeScalar := fun _ _ _ => throw (.unsupported "validity discriminant: writeScalar")
      toOp := fun _ _ => throw (.unsupported "validity discriminant: toOp")
      scalarMayBeNull := fun _ _ => throw (.unsupported "validity discriminant: scalarMayBeNull") }
  debugAssertions := false
  classify := annealValidityClassify
  unitLayout := fun _ => pure (translateTy { kind := .tuple .nil, layoutIdx := 0 })
  typeName := fun _ _ => pure ""
  opsemInhabited := fun _ tyId => pure (tyId != 50)
  isFreeze := fun _ _ => pure true
  fieldPath := fun _ _ _ _ => throw (.unsupported "validity fieldPath")
  variantPath := fun _ _ _ => throw (.unsupported "validity variantPath")
  projectBox := fun _ _ => throw (.unsupported "validity projectBox")
  toOp := fun _ place => do
    let op ← annealValidityPlaceOperand place
    pure ⟨op, place.layout⟩
  readImmediate := fun _ place _ => do
    let op ← annealValidityPlaceOperand place
    annealReadImmediate ⟨op, place.layout⟩
  clearProvenance := fun _ _ => pure ()
  writeNoValidate := fun _ _ _ => throw (.unsupported "validity writeNoValidate")
  sizeAndAlign := fun _ place =>
    if place.layout.layout.isSized then
      pure (some (place.layout.layout.size, place.layout.layout.align.abi))
    else
      throw (.unsupported "validity of an unsized pointee")
  ptrToPlace := fun c value => do
    let some pointeeLay := annealValidityPointeeLayout layouts c
      | throw (.unsupported "validity pointee without an exact layout")
    let sc ←
      match value.imm.toScalar with
      | .ok s => pure s
      | .error err => throw (Miri.Interpreter.ScalarOps.immediateError err)
    let ptr ←
      match sc.toPointer annealTargetDataLayout with
      | .ok p => pure p
      | .error err => throw (Miri.Interpreter.ScalarOps.scalarError err)
    let mismatch ←
      match annealOffsetMisalignment ptr.offset pointeeLay.layout.align.abi with
      | .ok m => pure m
      | .error err => throw (.invalidProgram (toString err))
    pure ⟨⟨ptr, .none, mismatch⟩, pointeeLay⟩
  metadataTail := fun _ _ => throw (.unsupported "validity metadataTail")
  checkPointerAccess := fun _ ptr size => do
    let st ← get
    pure (annealValidityAccessCheck st.machine ptr size)
  checkPointerAlign := fun _ ptr align =>
    match annealOffsetMisalignment ptr.offset align with
    | .ok none => pure ()
    | .ok (some _) => throw (.undefinedBehavior "misaligned pointer")
    | .error err => throw (.invalidProgram (toString err))
  checkPointerAlignResult := fun _ ptr align =>
    match annealOffsetMisalignment ptr.offset align with
    | .ok none => pure (.ok ())
    | .ok (some mis) => pure (.error mis)
    | .error err => throw (.invalidProgram (toString err))
  scalarMayBeNull := fun _ sc =>
    match sc.tryToScalarInt with
    | .ok (.integer integer) => pure integer.isNull
    | .ok _ => throw (.invalidProgram "absolute Miri pointer erased its address")
    | .error err => throw (Miri.Interpreter.ScalarOps.scalarError err)
  retagPointer := fun _ _ _ => pure none
  ctfePointerLookup := fun _ _ _ => throw (.unsupported "validity ctfePointerLookup")
  inMutableMemory := fun _ _ => pure true
  readBytes := fun _ _ _ _ => throw (.unsupported "validity readBytes")
  clearBytesProvenance := fun _ _ _ => throw (.unsupported "validity clearBytesProvenance")
  beginPadding := fun _ _ _ => pure none
  writePadding := fun _ _ _ => throw (.unsupported "validity writePadding")
  cachedUnionRanges := fun _ _ compute => compute
  withGhostValidation := fun action => action

/-! ## 4. Validity Visitor Correspondence -/

/-- Reading an immediate local through the validity hooks yields its immediate,
unless it is uninitialized. -/
theorem annealValidityPlaceOperand_local
    {m : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf]) {idx : Nat} (hlt : idx < tf.locals.size)
    {imm : Miri.Interpreter.Immediate AnnealProv}
    (hval : (tf.locals[idx]'hlt).value = .live (.immediate imm))
    (lay : Miri.Interpreter.LocalLayout) :
    annealValidityPlaceOperand ⟨.local 0 idx none tf.localsIdentity, lay⟩ m =
      .ok (.immediate imm) m := by
  have hget : tf.getLocal idx = .ok (tf.locals[idx]'hlt) := by
    unfold Miri.Interpreter.Frame.getLocal
    simp [hlt]
    rfl
  have hget' : tf.getLocal idx = .ok ⟨.live (.immediate imm), (tf.locals[idx]'hlt).layout⟩ := by
    rw [hget]; rcases h : tf.locals[idx]'hlt with ⟨v, l⟩; rw [h] at hval; simp at hval; subst hval; rfl
  have hgop := frame_getLocalOperand_live tf hget'
  unfold annealValidityPlaceOperand
  simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind,
    stack_currentFrame?_singleton m.stack tf hframes, hgop, pure, EStateM.pure]

/-- Anneal's validity invariant for a primitive scalar at type `ty`: the
`bool` and `char` clauses that `ImmediateRel.scalar` requires of every typed
scalar and that `decodeValueFromBytes` checks on every typed byte decode. -/
def AnnealScalarValid (ty : Ty) (sc : MirAst.ScalarInt) : Prop :=
  (ty.kind = .bool → sc.bits = 0 ∨ sc.bits = 1) ∧
  (ty.kind = .char → isValidCharCode sc.bits = true)

/-- The validity visitor classifies every primitive scalar type by its encoded
`TyId` alone: `bool` as `.boolean`, `char` as `.character`, and the integer
types as `.integer`; the uninhabited `!` is `.never`. -/
theorem annealValidityClassify_prim (layouts : LayoutTable) (c : Ty) {ty : Ty}
    (st : AnnealStepState) :
    (ty.kind = .bool →
      annealValidityClassify c (translateTy ty layouts).ty st = .ok .boolean st) ∧
    (ty.kind = .char →
      annealValidityClassify c (translateTy ty layouts).ty st = .ok .character st) ∧
    (∀ it, ty.kind = .int it →
      annealValidityClassify c (translateTy ty layouts).ty st = .ok .integer st) ∧
    (∀ ut, ty.kind = .uint ut →
      annealValidityClassify c (translateTy ty layouts).ty st = .ok .integer st) ∧
    (ty.kind = .never →
      annealValidityClassify c (translateTy ty layouts).ty st = .ok .never st) := by
  refine ⟨fun hk => ?_, fun hk => ?_, fun it hk => ?_, fun ut hk => ?_, fun hk => ?_⟩
  · simp only [translateTy, encodeTyId, hk]; rfl
  · simp only [translateTy, encodeTyId, hk]; rfl
  · cases it <;> (simp only [translateTy, encodeTyId, hk]; rfl)
  · cases ut <;> (simp only [translateTy, encodeTyId, hk]; rfl)
  · simp only [translateTy, encodeTyId, hk]; rfl

/-- The `bool` check of the validity visitor (`Scalar.toBool`) on a one-byte
scalar accepts exactly the bit patterns `0` and `1` that Anneal's `bool`
invariant allows. -/
theorem fromScalarInt_toBool_ok_iff {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    (hrel : ScalarRel sc msc) (hsz1 : sc.sizeBytes = 1) :
    (∃ b, (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) msc).toBool = .ok b) ↔
      (sc.bits = 0 ∨ sc.bits = 1) := by
  have htb : msc.toBits (Miri.ABI.Size.ofBytes 1) = .ok (BitVec.ofNat 128 sc.bits) := by
    have hb := hrel.toBits_eq
    rw [hsz1] at hb
    exact hb
  have hcan := hrel.canonical
  rw [hsz1] at hcan
  have hlt : sc.bits < 256 := by
    have : scalarModulus 1 = 256 := by decide
    omega
  have hnat : (BitVec.ofNat 128 sc.bits).toNat = sc.bits := by
    rw [BitVec.toNat_ofNat]; omega
  have hu8 : (UInt8.ofNat sc.bits).toNat = sc.bits := UInt8.toNat_ofNat_of_lt (by omega)
  have heq : (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) msc).toBool =
      (if UInt8.ofNat (BitVec.ofNat 128 sc.bits).toNat == 0 then .ok false
       else if UInt8.ofNat (BitVec.ofNat 128 sc.bits).toNat == 1 then .ok true
       else .error (.scalarInt (.invalidBool (UInt8.ofNat (BitVec.ofNat 128 sc.bits).toNat)))) := by
    unfold Miri.Memory.Scalar.toBool Miri.Memory.Scalar.toUInt8
      Miri.Memory.Scalar.toUInt
      Miri.Memory.Scalar.toBits Miri.Memory.Scalar.toScalarInt
      Miri.Memory.Scalar.tryToScalarInt Miri.Memory.Scalar.fromScalarInt
    dsimp only [bind, Except.bind, Except.mapError, pure, Except.pure]
    rw [htb]
    rfl
  rw [heq, hnat]
  constructor
  · rintro ⟨b, hb⟩
    by_cases h0 : sc.bits = 0
    · exact Or.inl h0
    · by_cases h1 : sc.bits = 1
      · exact Or.inr h1
      · exfalso
        have hn0 : (UInt8.ofNat sc.bits == 0) = false := by
          cases h : (UInt8.ofNat sc.bits == 0) with
          | false => rfl
          | true =>
            have := congrArg UInt8.toNat (beq_iff_eq.mp h)
            rw [hu8] at this
            exact absurd this h0
        have hn1 : (UInt8.ofNat sc.bits == 1) = false := by
          cases h : (UInt8.ofNat sc.bits == 1) with
          | false => rfl
          | true =>
            have := congrArg UInt8.toNat (beq_iff_eq.mp h)
            rw [hu8] at this
            exact absurd this h1
        rw [hn0, hn1] at hb
        cases hb
  · rintro (h0 | h1)
    · rw [h0]; exact ⟨false, rfl⟩
    · rw [h1]; exact ⟨true, rfl⟩

/-- The validity visitor reads an immediate scalar local unchanged
(`readImmediate`, through `annealReadImmediate`). -/
theorem annealValidityHooks_readImmediate_local (layouts : LayoutTable) (c : Ty)
    {m : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf]) {idx : Nat} (hlt : idx < tf.locals.size)
    {sc : Miri.Memory.Scalar AnnealProv}
    (hval : (tf.locals[idx]'hlt).value = .live (.immediate (.scalar sc)))
    (lay : Miri.Interpreter.LocalLayout) (ev : Miri.Memory.ExpectedValue) :
    (annealValidityHooks layouts).readImmediate c ⟨.local 0 idx none tf.localsIdentity, lay⟩ ev m =
      .ok ⟨.scalar sc, lay⟩ m := by
  have hop := annealValidityPlaceOperand_local hframes hlt hval lay
  show (annealValidityPlaceOperand ⟨.local 0 idx none tf.localsIdentity, lay⟩ >>= fun op =>
    annealReadImmediate ⟨op, lay⟩) m = _
  simp only [bind, EStateM.bind, hop]
  rfl

/-- **`validityVisitor_scalar_bool_simulation` (`LM-3.2`)**: the vendored
validity visitor (`ValidityVisitor.visit`, `primitive`) checks an immediate
local of primitive scalar type exactly as Anneal's scalar invariant does.
Its leaves, as instantiated by `annealValidityHooks`, behave as follows on a
local holding the `ScalarRel`-related scalar `.fromScalarInt msc`:

1. `readImmediate` yields the local's scalar unchanged;
2. a `bool` is classified `.boolean`, and the visitor's `Scalar.toBool` check
   succeeds exactly when Anneal's `bool` invariant (`AnnealScalarValid`: bit
   pattern `0` or `1`) holds, failing otherwise;
3. a `char` is classified `.character` and an integer `.integer` (integers
   carry no value check, matching Anneal, where every integer is valid);
4. `!` is classified `.never`, which the visitor always rejects. -/
theorem validityVisitor_scalar_bool_simulation
    (layouts : LayoutTable) (c : Ty) {ty : Ty}
    {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt} (hrel : ScalarRel sc msc)
    (hsz : (translateTy ty layouts).layout.size = translateSizeBytes sc.sizeBytes)
    {m : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf]) {idx : Nat} (hlt : idx < tf.locals.size)
    (hval : (tf.locals[idx]'hlt).value = .live (.immediate (.scalar (.fromScalarInt msc))))
    (ev : Miri.Memory.ExpectedValue) :
    (annealValidityHooks layouts).readImmediate c
        ⟨.local 0 idx none tf.localsIdentity, translateTy ty layouts⟩ ev m =
      .ok ⟨.scalar (.fromScalarInt msc), translateTy ty layouts⟩ m ∧
    (ty.kind = .bool →
      annealValidityClassify c (translateTy ty layouts).ty m = .ok .boolean m ∧
      ((∃ b, (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) msc).toBool = .ok b) ↔
        AnnealScalarValid ty sc)) ∧
    (ty.kind = .char →
      annealValidityClassify c (translateTy ty layouts).ty m = .ok .character m) ∧
    ((∃ it, ty.kind = .int it) ∨ (∃ ut, ty.kind = .uint ut) →
      annealValidityClassify c (translateTy ty layouts).ty m = .ok .integer m ∧
      AnnealScalarValid ty sc) ∧
    (ty.kind = .never →
      annealValidityClassify c (translateTy ty layouts).ty m = .ok .never m) := by
  obtain ⟨hcb, hcc, hci, hcu, hcn⟩ := annealValidityClassify_prim layouts c (ty := ty) m
  refine ⟨annealValidityHooks_readImmediate_local layouts c hframes hlt hval _ ev,
    fun hk => ⟨hcb hk, ?_⟩, hcc, fun hint => ?_, hcn⟩
  · obtain ⟨hsz1, _⟩ := sizeBytes_eq_of_translateTy (Or.inl hk) hrel.validBytes hsz
    have hsz1' : sc.sizeBytes = 1 := by rw [hsz1]; simp [boolOrIntByteWidth, hk]
    rw [fromScalarInt_toBool_ok_iff hrel hsz1']
    constructor
    · intro hb
      exact ⟨fun _ => hb, fun hc => absurd (hk.symm.trans hc) (by intro h; cases h)⟩
    · intro hv
      exact hv.1 hk
  · rcases hint with ⟨it, hk⟩ | ⟨ut, hk⟩
    · refine ⟨hci it hk, fun hb => ?_, fun hc => ?_⟩
      · rw [hk] at hb; cases hb
      · rw [hk] at hc; cases hc
    · refine ⟨hcu ut hk, fun hb => ?_, fun hc => ?_⟩
      · rw [hk] at hb; cases hb
      · rw [hk] at hc; cases hc

/-- Two members of a list whose images under `f` are pairwise distinct are
equal when their images are. -/
theorem mem_eq_of_map_nodup {α β : Type} {f : α → β} :
    ∀ {l : List α}, (l.map f).Nodup → ∀ {a b : α}, a ∈ l → b ∈ l → f a = f b → a = b
  | [], _, _, _, ha, _, _ => by cases ha
  | x :: xs, hnd, a, b, ha, hb, hf => by
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨hnotin, hnd'⟩ := hnd
    rcases List.mem_cons.mp ha with rfl | ha' <;> rcases List.mem_cons.mp hb with rfl | hb'
    · rfl
    · exact absurd (hf ▸ List.mem_map_of_mem hb') hnotin
    · exact absurd (hf.symm ▸ List.mem_map_of_mem ha') hnotin
    · exact mem_eq_of_map_nodup hnd' ha' hb' hf

/-- `PtrRel` names the allocation of the unique `allocMap` entry with the
pointer's tag. -/
theorem PtrRel.allocId_of_entry {body : CapturedMir} {s : MachineState}
    {m : AnnealStepState} {allocMap : List AllocMapEntry}
    (halloc : AllocMapRel body s m allocMap)
    {p : ProvenancePtr} {mptr : Miri.Memory.Pointer AnnealProv}
    (hptr : PtrRel allocMap p mptr) {e : AllocMapEntry} (he : e ∈ allocMap)
    (htag : e.tag = p.tag) :
    ∃ borTag, mptr =
      ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId + UInt64.ofNat p.offsetBytes),
        .concrete e.allocId borTag⟩ ∧ p.offsetBytes < 2 ^ 32 := by
  rcases hptr with ⟨allocId, borTag, hprov, _, hoff, haddr, e', he', htag', halloc'⟩
  have heq : e' = e := by
    have hnodup := halloc.tags_nodup
    have hmem' : e' ∈ allocMap := he'
    exact mem_eq_of_map_nodup hnodup hmem' he (htag'.trans htag.symm)
  subst heq
  subst halloc'
  refine ⟨borTag, ?_, hoff⟩
  rcases mptr with ⟨off, prov⟩
  dsimp only at hprov haddr
  subst hprov haddr
  rfl

/-- The validity visitor's dereferenceability leaf (`checkPointerAccess`)
reports `annealValidityAccessCheck` without changing the state. -/
theorem annealValidityHooks_checkPointerAccess_eq (layouts : LayoutTable) (c : Ty)
    (m : AnnealStepState) (ptr : Miri.Memory.Pointer (Option AnnealProv))
    (size : Miri.ABI.Size) :
    (annealValidityHooks layouts).checkPointerAccess c ptr size m =
      .ok (annealValidityAccessCheck m.machine ptr size) m := rfl

/-- `annealValidityAccessCheck` on a stack pointer accepts exactly the
in-bounds accesses to a live allocation. -/
theorem annealValidityAccessCheck_stack
    (mach : AnnealMachine)
    (id : Miri.Memory.AllocId) (borTag : Miri.Memory.BorTag) (offsetBytes : Nat)
    (size : Miri.ABI.Size)
    (hid : id.value.toNat < 2 ^ 32) (hoff : offsetBytes < 2 ^ 32)
    (hbase : mach.lookupBaseAddr id = some (annealStackBaseAddr id))
    (hsz : Miri.Memory.sizeAsI64 size = .ok (size.bytes.toNat : Int))
    (hpos : 0 < size.bytes.toNat) (hfit : (size.bytes.toNat : Int) < 2 ^ 63) :
    (∀ localAlloc, mach.memory.live.find? (fun entry => entry.1 == id) =
        some (id, localAlloc) →
      offsetBytes + size.bytes.toNat ≤ localAlloc.allocation.byteSize.bytes.toNat →
      annealValidityAccessCheck mach
          ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr id + UInt64.ofNat offsetBytes),
            some (.concrete id borTag)⟩ size = .ok ()) ∧
    (∀ localAlloc, mach.memory.live.find? (fun entry => entry.1 == id) =
        some (id, localAlloc) →
      localAlloc.allocation.byteSize.bytes.toNat < offsetBytes + size.bytes.toNat →
      ∃ err, annealValidityAccessCheck mach
          ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr id + UInt64.ofNat offsetBytes),
            some (.concrete id borTag)⟩ size = .error err) ∧
    (mach.memory.live.find? (fun entry => entry.1 == id) = none →
      ∃ err, annealValidityAccessCheck mach
          ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr id + UInt64.ofNat offsetBytes),
            some (.concrete id borTag)⟩ size = .error err) := by
  refine ⟨fun la hlive hin => ?_, fun la hlive hoob => ?_, fun hdead => ?_⟩
  · have hck := checkAndDerefPtr_live_inbounds_ok (mach := mach) id borTag offsetBytes
      size.bytes.toNat la (.dereferenceable "pointer") hid hoff hbase hlive hpos hfit hin
    unfold annealValidityAccessCheck
    split
    · rename_i heq; rw [hsz] at heq; cases heq
    · rename_i n heq
      rw [hsz] at heq
      cases heq
      rw [hck]
  · have hck := checkAndDerefPtr_live_oob_err (mach := mach) id borTag offsetBytes
      size.bytes.toNat la (.dereferenceable "pointer") hid hoff hbase hlive hpos hfit hoob
    refine ⟨.pointerOutOfBounds id la.allocation.byteSize (offsetBytes : Int)
      (size.bytes.toNat : Int) (.dereferenceable "pointer"), ?_⟩
    unfold annealValidityAccessCheck
    split
    · rename_i heq; rw [hsz] at heq; cases heq
    · rename_i n heq
      rw [hsz] at heq
      cases heq
      rw [hck]
  · have hck := checkAndDerefPtr_deadAlloc_err (mach := mach) id borTag offsetBytes
      (size.bytes.toNat : Int) (.dereferenceable "pointer") hid hoff hbase hdead
      (by exact_mod_cast hpos) hfit
    refine ⟨.allocationLookup (.deadAllocation id), ?_⟩
    unfold annealValidityAccessCheck
    split
    · rename_i heq; rw [hsz] at heq; cases heq
    · rename_i n heq
      rw [hsz] at heq
      cases heq
      rw [hck]

/-- **`validityVisitor_ref_dereferenceable_simulation` (`LM-3.2`)**: in a
`StateRelLM3_2` state, a safe reference of type `&T` / `&mut T` that holds the
offset-`0` pointer `p` (related to the `lean-miri` pointer `mptr` by `PtrRel`)
into the address-taken primitive-scalar local `e.localIdx` (`e ∈ allocMap`,
`e.tag = p.tag`) is valid exactly when that local is live:

1. **Live pointee**: every leaf that `ValidityVisitor.checkSafe` consults
   accepts the reference: the pointee place has the target's exact layout
   (`annealValidityPointeeLayout`), the access of `size_of::<T>()` bytes is in
   bounds of a live allocation (`checkPointerAccess`), and the address is
   aligned (`checkPointerAlignResult`). The eager safe-reference dereference
   (`annealSafeRefDerefCheck`, `PointerPlaceMachine.dereference`) accepts it
   as well, yielding the pointee place.
2. **Dangling pointee (after `StorageDead`)**: `checkPointerAccess` reports a
   dangling access, the eager dereference is undefined behavior, and so is
   Anneal's read `copy *_r` through the reference. -/
theorem validityVisitor_ref_dereferenceable_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    {p : ProvenancePtr} {mptr : Miri.Memory.Pointer AnnealProv}
    (hptr : PtrRel allocMap p mptr) (hoff0 : p.offsetBytes = 0)
    {e : AllocMapEntry} (he : e ∈ allocMap) (htag : e.tag = p.tag)
    {targetDecl : LocalDecl} (hdecl_t : get? body.localDecls e.localIdx = some targetDecl)
    {refTy : Ty} {refMut : Mutability}
    (hrefTy : refTy.kind = .ref refMut targetDecl.ty.kind) :
    (∀ slot, get? s.frame.locals e.localIdx = some slot → slot ≠ .dead →
      annealValidityPointeeLayout body.layouts refTy =
        some (translateTy targetDecl.ty body.layouts) ∧
      (annealValidityHooks body.layouts).checkPointerAccess refTy mptr.withOptionalProvenance
          (translateTy targetDecl.ty body.layouts).layout.size m = .ok (.ok ()) m ∧
      (annealValidityHooks body.layouts).checkPointerAlignResult refTy
          mptr.withOptionalProvenance
          (translateTy targetDecl.ty body.layouts).layout.align.abi m = .ok (.ok ()) m ∧
      annealSafeRefDerefCheck m.machine
          (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))
          (translateTy targetDecl.ty body.layouts) =
        .ok ⟨mptr.withOptionalProvenance, .none, none⟩) ∧
    (get? s.frame.locals e.localIdx = some .dead →
      (∃ err, (annealValidityHooks body.layouts).checkPointerAccess refTy
          mptr.withOptionalProvenance
          (translateTy targetDecl.ty body.layouts).layout.size m = .ok (.error err) m) ∧
      annealSafeRefDerefCheck m.machine
          (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))
          (translateTy targetDecl.ty body.layouts) =
        .error (.undefinedBehavior "dereferencing a dangling reference") ∧
      ∀ refIdx, get? s.frame.locals refIdx = some (.init (.ptr p 8)) →
        evalOperand s.frame.locals (.copy ⟨refIdx, .cons .deref .nil⟩) s.memory.borrows
          s.memory.globals body.layouts s.memory.callerLocals = .ub) := by
  obtain ⟨tf, hframes, _, _, _, _, _, _, hcaller, hbor, halloc, _⟩ := id hstate
  obtain ⟨borTag, hmptr, _⟩ := PtrRel.allocId_of_entry halloc hptr he htag
  obtain ⟨_, hprim⟩ : ∃ d, get? body.localDecls e.localIdx = some d ∧ IsPrimScalarTy d.ty :=
    halloc.target_decl e he
  obtain ⟨d, hd, hprim⟩ := halloc.target_decl e he
  rw [hdecl_t] at hd
  cases hd
  obtain ⟨hsize, hpos, hfit, _, hpow, _⟩ := hprim.size_align_ok body.layouts
  obtain ⟨hid, _, hbase⟩ := halloc.base_addr_valid e he
  have hm : mptr.withOptionalProvenance =
      ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId + UInt64.ofNat 0),
        some (.concrete e.allocId borTag)⟩ := by
    rw [hmptr, hoff0]; rfl
  have hpos' : 0 < (translateTy targetDecl.ty body.layouts).layout.size.bytes.toNat := by
    exact_mod_cast hpos
  have hacc := annealValidityAccessCheck_stack m.machine e.allocId
    borTag 0 (translateTy targetDecl.ty body.layouts).layout.size hid (by decide) hbase hsize
    hpos' hfit
  have haligned : annealOffsetMisalignment
      (Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId + UInt64.ofNat 0))
      (translateTy targetDecl.ty body.layouts).layout.align.abi = .ok none := by
    have h0 : annealStackBaseAddr e.allocId + UInt64.ofNat 0 = annealStackBaseAddr e.allocId := by
      simp
    rw [h0]
    exact annealOffsetMisalignment_stackBase_eq_none e.allocId _ hpow
  have hmval : Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr =
      Miri.Memory.Scalar.fromPointer annealTargetDataLayout
        ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId + UInt64.ofNat 0),
          .concrete e.allocId borTag⟩ := by
    rw [hmptr, hoff0]
  obtain ⟨hlive_e, hdead_e⟩ := halloc.local_alloc_sync tf hframes e he
  refine ⟨fun slot hslot hne => ?_, fun hdead => ?_⟩
  · obtain ⟨_, _, hshape⟩ := hlive_e slot hslot hne
    obtain ⟨la, hfind, _, _, hsh⟩ := hshape targetDecl hdecl_t
    have hin : 0 + (translateTy targetDecl.ty body.layouts).layout.size.bytes.toNat ≤
        la.allocation.byteSize.bytes.toNat := by
      rw [hsh.byteSize_eq]; omega
    refine ⟨?_, ?_, ?_, ?_⟩
    · have hexact : derefPointeeKindHasExactLayout targetDecl.ty.kind = true := by
        rcases hprim with h | h | ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h] <;> rfl
      unfold annealValidityPointeeLayout
      rw [hrefTy]
      dsimp only
      rw [hexact]
      simp only [↓reduceIte, Option.some.injEq]
      exact hprim.translateTy_layoutIdx body.layouts
    · rw [hm, annealValidityHooks_checkPointerAccess_eq, hacc.1 la hfind hin]
    · rw [hm]
      simp only [annealValidityHooks]
      rw [haligned]
      rfl
    · rw [hmval, hm]
      exact annealSafeRefDerefCheck_live_ok e.allocId borTag 0 _ la hid (by decide) hbase hfind
        hsize hpos' hfit hin haligned
  · have hfind := hdead_e hdead
    refine ⟨?_, ?_, fun refIdx hslot_r => ?_⟩
    · obtain ⟨err, herr⟩ := hacc.2.2 hfind
      exact ⟨err, by rw [hm, annealValidityHooks_checkPointerAccess_eq, herr]⟩
    · rw [hmval]
      exact annealSafeRefDerefCheck_dead_err e.allocId borTag 0 _ hid (by decide) hbase hfind
        hsize hpos' hfit
    · have hlook := lookupBorrow_map_toBorrowEntry_of_nodup halloc.tags_nodup he
      rw [← hbor, htag] at hlook
      unfold evalOperand
      dsimp only []
      rw [hslot_r]
      dsimp only []
      rw [hlook]
      dsimp only [AllocMapEntry.toBorrowEntry]
      cases e.perm <;> (dsimp only []; try rw [hdead])

end LeanMiriSpec.Correspondence
