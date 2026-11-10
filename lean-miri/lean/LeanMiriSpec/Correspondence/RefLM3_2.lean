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
  memoryOffset := fun _ mplace amount _ metaVal =>
    if amount == Miri.ABI.Size.ZERO then
      pure { mplace with metadata := metaVal }
    else
      throw (.unsupported "validity place: nonzero memoryOffset")
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

/-- Encoded integer `TyId` (`10..14` signed, `20..24` unsigned) for an enum tag
primitive of `widthBytes` bytes (`1, 2, 4, 8, 16`) and signedness `signed`. -/
def annealTagIntTyId (widthBytes : Nat) (signed : Bool) : Option Miri.MIR.TyId :=
  match widthBytes, signed with
  | 1, false => some 20
  | 2, false => some 21
  | 4, false => some 22
  | 8, false => some 23
  | 16, false => some 24
  | 1, true => some 10
  | 2, true => some 11
  | 4, true => some 12
  | 8, true => some 13
  | 16, true => some 14
  | _, _ => none

/-- Full-range integer `LocalLayout` for an enum discriminant tag scalar `tag`
(`Miri.ABI.Scalar`), preserving its byte width and signedness so
`annealReadImmediate` reads raw initialized tag bytes without prematurely
clipping to `validRange` before `Discriminant.readDiscriminant` checks
`validRange` and `variantForDiscriminant`. -/
def annealAbiTagRawIntLayout (tag : Miri.ABI.Scalar) :
    Option Miri.Interpreter.LocalLayout :=
  match tag.primitive with
  | .Int intKind signed =>
    let w : Nat :=
      match intKind with
      | .I8 => 1
      | .I16 => 2
      | .I32 => 4
      | .I64 => 8
      | .I128 => 16
    match annealTagIntTyId w signed with
    | some tyId => some { ty := tyId, layout := scalarLayoutData w signed }
    | none => none
  | _ => none

/-- Classify an aggregate `TyId` (`100 + layoutIdx`, `100 ≤ tyId < 900`) against
`layouts`: zero-variant (`VariantsShape.empty`) and multi-variant
(`VariantsShape.multiple`) enums classify as `.aggregate false false true`;
all other aggregates fail closed with `StepError.unsupported`. -/
def annealValidityClassifyAdt (layouts : LayoutTable) (tyId : Miri.MIR.TyId) :
    EStateM Miri.Interpreter.StepError AnnealStepState
      Miri.Interpreter.ValidityVisitor.TypeKind :=
  if 100 ≤ tyId ∧ tyId < 900 then
    match LayoutTable.lookup layouts (tyId - 100) with
    | some tl =>
      match tl.variants with
      | .empty | .multiple .. => pure (.aggregate false false true)
      | .single _ => throw (.unsupported "validity of a non-enum aggregate")
    | none => throw (.unsupported "validity of an aggregate without layout")
  else
    throw (.unsupported "validity of a type outside the scalar, reference, and enum fragment")

/-- Classify an encoded `TyId` for the validity visitor. The context `c` is
the Anneal type of the validated place: `encodeTyId` maps every reference to
`TyId 41`, so only `c` records whether a reference is mutable. Aggregates and
every other type outside the scalar and reference fragment fail closed with
`StepError.unsupported`, never with a verdict. -/
def annealValidityClassify (layouts : LayoutTable) (c : Ty) (tyId : Miri.MIR.TyId) :
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
  | id => if 100 ≤ id then annealValidityClassifyAdt layouts id else throw (.unsupported "validity of a type outside the scalar and reference fragment")

/-- Operational inhabitedness of an encoded `TyId` (`100 ≤ tyId < 900`) against
`layouts`: `false` when `tl.isUninhabited` or `tl.variants = .empty`, and `true`
otherwise. -/
def annealAdtTyIdInhabited (layouts : LayoutTable) (tyId : Miri.MIR.TyId) : Bool :=
  if 100 ≤ tyId ∧ tyId < 900 then
    match LayoutTable.lookup layouts (tyId - 100) with
    | some tl =>
      !tl.isUninhabited &&
        match tl.variants with
        | .empty => false
        | _ => true
    | none => true
  else
    true

/-- Projection dictionary for `annealValidityHooks` supporting offset-`0` enum
discriminant tag field projection and fieldless enum variant downcasts to unit
layout `{ ty := 51, layout := zstLayoutData }`. -/
def annealValidityProjectionHooksWithLayouts (layouts : LayoutTable) :
    Miri.Interpreter.PlaceProjectionHooks AnnealProv AnnealStepState Ty Unit :=
  { annealValidityProjectionHooks with
    field := fun _ baseLay index =>
      match baseLay.layout.fields.offset index, baseLay.layout.variants with
      | .ok off, .Multiple tag _ tagField _ =>
        if off == Miri.ABI.Size.ZERO && index == tagField then
          match annealAbiTagRawIntLayout tag with
          | some tagLay => pure tagLay
          | none => throw (.unsupported "validity projection: non-integer enum tag")
        else
          throw (.unsupported "validity projection: nonzero or non-tag enum field")
      | _, _ => throw (.unsupported "validity projection: field")
    variant := fun _ baseLay variant =>
      if 100 ≤ baseLay.ty ∧ baseLay.ty < 900 then
        match LayoutTable.lookup layouts (baseLay.ty - 100) with
        | some tl =>
          match tl.variants with
          | .multiple _ _ variantShapes =>
            match get? variantShapes variant with
            | some (.arbitrary .nil .nil) =>
              pure { ty := 51, layout := zstLayoutData }
            | _ => throw (.unsupported "validity projection: payload enum variant")
          | _ => throw (.unsupported "validity projection: non-multiple variant")
        | none => throw (.unsupported "validity projection: unknown enum layout")
      else
        throw (.unsupported "validity projection: variant") }

/-- Resolve the pointee layout of a safe reference `&MyEnum` / `&mut MyEnum`
(`c.kind = .ref _ (.adt defPath args)`), consulting `refTl.fieldLayouts` from
`rustc-capture` when available and falling back to `layoutIdx = 0`
(`MirSemantics.pointeeTyOf`). -/
def annealRefEnumPointeeLayout (layouts : LayoutTable) (c : Ty) :
    Option Miri.Interpreter.LocalLayout :=
  match c.kind with
  | .ref _ (.adt defPath args) =>
    let candidateIdx : Nat :=
      match LayoutTable.lookup layouts c.layoutIdx with
      | some refTl =>
        match refTl.fieldLayouts with
        | ptIdx :: _ => ptIdx
        | .nil => 0
      | none => 0
    match LayoutTable.lookup layouts candidateIdx with
    | some ptTl =>
      match ptTl.variants with
      | .empty | .multiple .. =>
        some (translateTy { kind := .adt defPath args, layoutIdx := candidateIdx } layouts)
      | .single _ => none
    | none => none
  | _ => none

/-- The pointee layout of a safe reference of Anneal type `c`, for the pointees
whose layout `translateTy` gives exactly (`derefPointeeKindHasExactLayout` and
`!`) as well as zero-variant and multi-variant enum pointees
(`annealRefEnumPointeeLayout`). -/
def annealValidityPointeeLayout (layouts : LayoutTable) (c : Ty) :
    Option Miri.Interpreter.LocalLayout :=
  match c.kind with
  | .ref _ pointeeKind =>
    if derefPointeeKindHasExactLayout pointeeKind then
      some (translateTy { kind := pointeeKind, layoutIdx := 0 } layouts)
    else
      match pointeeKind with
      | .never => some (translateTy { kind := .never, layoutIdx := 0 } layouts)
      | _ => annealRefEnumPointeeLayout layouts c
  | _ => none

/-- The operand that a validated place denotes in the current frame: an
unprojected (or offset-`0` projected) local's value or a memory place. Dead
locals are undefined behavior; nonzero-offset projected local places fail closed. -/
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
  | .local _ localId (some off) _ =>
    if off == Miri.ABI.Size.ZERO then
      match frame.getLocalOperand localId with
      | .ok op => pure op
      | .error (.localExpectedLive _) => throw (.undefinedBehavior "validation of a dead local")
      | .error e => throw (.stack e)
    else
      throw (.unsupported "validation of a projected local place")

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
* `discriminant` and `projection` validate zero-variant (`VariantsShape.empty`)
  and scalar-tagged multi-variant (`VariantsShape.multiple`) enums against
  `layouts`.
* Retagging (`retagPointer`), provenance and padding resets, and ghost
  validation are no-ops: Tree Borrows retags are `LM-3.3`'s subject, and the
  scalar and reference fragment has neither provenance-carrying integers nor
  padding.
* Everything else that only general structs, slices, trait objects, boxes, or
  constant evaluation reach fails closed with `StepError.unsupported`. -/
def annealValidityHooks (layouts : LayoutTable) :
    Miri.Interpreter.ValidityVisitor.Hooks AnnealProv AnnealStepState Ty Unit Unit Unit Unit where
  target := annealRuntimeDataLayout
  projection := annealValidityProjectionHooksWithLayouts layouts
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
      discriminantLayout := fun _ _ =>
        pure { ty := 23, layout := scalarLayoutData 8 false }
      tagLayout := fun _ tag =>
        match annealAbiTagRawIntLayout tag with
        | some tagLay => pure tagLay
        | none => throw (.unsupported "validity discriminant: non-integer tagLayout")
      discriminantValue := fun _ _ variant =>
        pure (some (23, BitVec.ofNat 128 variant))
      variantForDiscriminant := fun _ tyId discrBits =>
        if 100 ≤ tyId ∧ tyId < 900 then
          match LayoutTable.lookup layouts (tyId - 100) with
          | some tl =>
            match tl.variants with
            | .multiple _ _ variantShapes =>
              if discrBits.toNat < variantShapes.length then
                pure (some discrBits.toNat)
              else
                pure none
            | _ => throw (.unsupported "validity discriminant: non-multiple enum")
          | none => throw (.unsupported "validity discriminant: unknown enum layout")
        else
          throw (.unsupported "validity discriminant: non-ADT tyId")
      adtVariantCount := fun _ tyId =>
        if 100 ≤ tyId ∧ tyId < 900 then
          match LayoutTable.lookup layouts (tyId - 100) with
          | some tl =>
            match tl.variants with
            | .multiple _ _ variantShapes => pure variantShapes.length
            | .empty => pure 0
            | .single _ => pure 1
          | none => throw (.unsupported "validity discriminant: unknown ADT layout")
        else
          throw (.unsupported "validity discriminant: non-ADT tyId")
      projectRead := fun _ op fieldIdx =>
        match op.layout.layout.fields.offset fieldIdx, op.layout.layout.variants with
        | .ok off, .Multiple tag _ tagField _ =>
          if off == Miri.ABI.Size.ZERO && fieldIdx == tagField then
            match annealAbiTagRawIntLayout tag with
            | some tagLay => pure ⟨op.op, tagLay⟩
            | none => throw (.unsupported "validity discriminant: non-integer tag")
          else
            throw (.unsupported "validity discriminant: nonzero or non-tag field")
        | _, _ => throw (.unsupported "validity discriminant: projectRead")
      readImmediate := fun _ op => annealReadImmediate op
      destLayout := fun v => v.layout
      projectWrite := fun _ _ _ => throw (.unsupported "validity discriminant: projectWrite")
      writeScalar := fun _ _ _ => throw (.unsupported "validity discriminant: writeScalar")
      toOp := fun _ place => do
        let op ← annealValidityPlaceOperand place
        pure ⟨op, place.layout⟩
      scalarMayBeNull := fun _ sc =>
        match sc.tryToScalarInt with
        | .ok (.integer integer) => pure integer.isNull
        | .ok _ => throw (.invalidProgram "absolute Miri pointer erased its address")
        | .error err => throw (Miri.Interpreter.ScalarOps.scalarError err) }
  debugAssertions := false
  classify := fun c tyId =>
    if tyId < 100 then
      if tyId == 51 then pure (.aggregate false false false) else annealValidityClassify layouts c tyId
    else
      annealValidityClassifyAdt layouts tyId
  unitLayout := fun _ => pure (translateTy { kind := .tuple .nil, layoutIdx := 0 })
  typeName := fun _ _ => pure ""
  opsemInhabited := fun _ tyId =>
    if tyId < 100 then
      pure (tyId != 50)
    else
      pure (annealAdtTyIdInhabited layouts tyId)
  isFreeze := fun _ _ => pure true
  fieldPath := fun _ _ _ _ => pure .enumTag
  variantPath := fun _ _ variant => pure (.variant (toString variant))
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
      annealValidityClassify layouts c (translateTy ty layouts).ty st = .ok .boolean st) ∧
    (ty.kind = .char →
      annealValidityClassify layouts c (translateTy ty layouts).ty st = .ok .character st) ∧
    (∀ it, ty.kind = .int it →
      annealValidityClassify layouts c (translateTy ty layouts).ty st = .ok .integer st) ∧
    (∀ ut, ty.kind = .uint ut →
      annealValidityClassify layouts c (translateTy ty layouts).ty st = .ok .integer st) ∧
    (ty.kind = .never →
      annealValidityClassify layouts c (translateTy ty layouts).ty st = .ok .never st) := by
  refine ⟨fun hk => ?_, fun hk => ?_, fun it hk => ?_, fun ut hk => ?_, fun hk => ?_⟩
  · simp only [translateTy, encodeTyId, hk]; rfl
  · simp only [translateTy, encodeTyId, hk]; rfl
  · cases it <;> (simp only [translateTy, encodeTyId, hk]; rfl)
  · cases ut <;> (simp only [translateTy, encodeTyId, hk]; rfl)
  · simp only [translateTy, encodeTyId, hk]; rfl

private theorem annealValidityHooks_classify_prim (layouts : LayoutTable) (c : Ty) {ty : Ty}
    (st : AnnealStepState) :
    (ty.kind = .bool →
      (annealValidityHooks layouts).classify c (translateTy ty layouts).ty st = .ok .boolean st) ∧
    (ty.kind = .char →
      (annealValidityHooks layouts).classify c (translateTy ty layouts).ty st = .ok .character st) ∧
    (∀ it, ty.kind = .int it →
      (annealValidityHooks layouts).classify c (translateTy ty layouts).ty st = .ok .integer st) ∧
    (∀ ut, ty.kind = .uint ut →
      (annealValidityHooks layouts).classify c (translateTy ty layouts).ty st = .ok .integer st) ∧
    (ty.kind = .never →
      (annealValidityHooks layouts).classify c (translateTy ty layouts).ty st = .ok .never st) := by
  refine ⟨fun hk => ?_, fun hk => ?_, fun it hk => ?_, fun ut hk => ?_, fun hk => ?_⟩
  · simp only [annealValidityHooks, translateTy, encodeTyId, hk]; rfl
  · simp only [annealValidityHooks, translateTy, encodeTyId, hk]; rfl
  · cases it <;> (simp only [annealValidityHooks, translateTy, encodeTyId, hk]; rfl)
  · cases ut <;> (simp only [annealValidityHooks, translateTy, encodeTyId, hk]; rfl)
  · simp only [annealValidityHooks, translateTy, encodeTyId, hk]; rfl

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

/-- The `char` check of the validity visitor (`Scalar.toChar`) on a four-byte
scalar accepts exactly the Unicode scalar values (`isValidCharCode`) that
Anneal's `char` invariant allows. -/
theorem fromScalarInt_toChar_ok_iff {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    (hrel : ScalarRel sc msc) (hsz4 : sc.sizeBytes = 4) :
    (∃ c, (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) msc).toChar = .ok c) ↔
      isValidCharCode sc.bits = true := by
  have htb : msc.toBits (Miri.ABI.Size.ofBytes 4) = .ok (BitVec.ofNat 128 sc.bits) := by
    have hb := hrel.toBits_eq
    rw [hsz4] at hb
    exact hb
  have hcan := hrel.canonical
  rw [hsz4] at hcan
  have hlt : sc.bits < 2 ^ 32 := by
    have : scalarModulus 4 = 2 ^ 32 := by decide
    omega
  have hnat : (BitVec.ofNat 128 sc.bits).toNat = sc.bits := by
    rw [BitVec.toNat_ofNat]; omega
  have hu32 : (UInt32.ofNat sc.bits).toNat = sc.bits := UInt32.toNat_ofNat_of_lt (by omega)
  have hu32_eq : msc.toUInt32 = .ok (UInt32.ofNat sc.bits) := by
    unfold Miri.Memory.ScalarInt.toUInt32 Miri.Memory.ScalarInt.toUInt
    dsimp only [bind, Except.bind, pure, Except.pure]
    rw [htb]
    dsimp only []
    rw [hnat]
  have htoChar : msc.toChar =
      (if !(decide (sc.bits ≤ 0x10ffff) &&
            !(decide (0xd800 ≤ sc.bits) && decide (sc.bits ≤ 0xdfff))) then
         .error (.invalidChar (UInt32.ofNat sc.bits))
       else
         .ok (Char.ofNat sc.bits)) := by
    unfold Miri.Memory.ScalarInt.toChar
    dsimp only [bind, Except.bind, pure, Except.pure]
    rw [hu32_eq]
    dsimp only []
    rw [hu32]
    with_unfolding_all rfl
  have hble1 : Nat.ble 55296 sc.bits = decide (55296 ≤ sc.bits) := by
    rw [Bool.eq_iff_iff, Nat.ble_eq, decide_eq_true_eq]
  have hble2 : Nat.ble 57344 sc.bits = decide (57344 ≤ sc.bits) := by
    rw [Bool.eq_iff_iff, Nat.ble_eq, decide_eq_true_eq]
  have hble3 : Nat.ble sc.bits 1114111 = decide (sc.bits ≤ 1114111) := by
    rw [Bool.eq_iff_iff, Nat.ble_eq, decide_eq_true_eq]
  unfold isValidCharCode Miri.Memory.Scalar.toChar
  dsimp only [Miri.Memory.Scalar.toScalarInt, Miri.Memory.Scalar.tryToScalarInt,
    Miri.Memory.Scalar.fromScalarInt, bind, Except.bind, pure, Except.pure]
  rw [htoChar, hble1, hble2, hble3]
  constructor
  · rintro ⟨c, hc⟩
    split at hc
    · cases hc
    · rename_i hcond
      simp only [Bool.not_eq_false', Bool.and_eq_true, decide_eq_true_eq,
        Bool.not_eq_true', Bool.and_eq_false_imp] at hcond
      simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
        Bool.and_eq_true, decide_eq_true_eq]
      omega
  · intro hv
    simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
      Bool.and_eq_true, decide_eq_true_eq] at hv
    have hcond : (decide (sc.bits ≤ 0x10ffff) &&
        !(decide (0xd800 ≤ sc.bits) && decide (sc.bits ≤ 0xdfff))) = true := by
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
        Bool.and_eq_false_imp, decide_eq_false_iff_not]
      omega
    rw [hcond]
    exact ⟨Char.ofNat sc.bits, rfl⟩

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
      annealValidityClassify layouts c (translateTy ty layouts).ty m = .ok .boolean m ∧
      ((∃ b, (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) msc).toBool = .ok b) ↔
        AnnealScalarValid ty sc)) ∧
    (ty.kind = .char →
      annealValidityClassify layouts c (translateTy ty layouts).ty m = .ok .character m) ∧
    ((∃ it, ty.kind = .int it) ∨ (∃ ut, ty.kind = .uint ut) →
      annealValidityClassify layouts c (translateTy ty layouts).ty m = .ok .integer m ∧
      AnnealScalarValid ty sc) ∧
    (ty.kind = .never →
      annealValidityClassify layouts c (translateTy ty layouts).ty m = .ok .never m) := by
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

/-- Reading a dead local through `annealValidityPlaceOperand` raises undefined
behavior (`"validation of a dead local"`). -/
theorem annealValidityPlaceOperand_dead_local
    {m : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf]) {idx : Nat} (hlt : idx < tf.locals.size)
    (hdead : (tf.locals[idx]'hlt).value = .dead)
    (lay : Miri.Interpreter.LocalLayout) :
    annealValidityPlaceOperand ⟨.local 0 idx none tf.localsIdentity, lay⟩ m =
      .error (.undefinedBehavior "validation of a dead local") m := by
  have hget : tf.getLocal idx = .ok (tf.locals[idx]'hlt) := by
    unfold Miri.Interpreter.Frame.getLocal
    simp [hlt]
    rfl
  have hget' : tf.getLocal idx = .ok ⟨.dead, (tf.locals[idx]'hlt).layout⟩ := by
    rw [hget]; rcases h : tf.locals[idx]'hlt with ⟨v, l⟩; rw [h] at hdead; simp at hdead; subst hdead; rfl
  have hgop : tf.getLocalOperand idx = .error (.localExpectedLive idx) := by
    unfold Miri.Interpreter.Frame.getLocalOperand
    rw [hget']
    rfl
  unfold annealValidityPlaceOperand
  simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind,
    stack_currentFrame?_singleton m.stack tf hframes, hgop, throw]
  rfl

/-- Reading a memory place through `annealValidityPlaceOperand` yields its
`.indirect` operand unchanged. -/
theorem annealValidityPlaceOperand_memory
    {m : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf])
    (mp : Miri.Interpreter.MemPlace AnnealProv)
    (lay : Miri.Interpreter.LocalLayout) :
    annealValidityPlaceOperand ⟨.memory mp, lay⟩ m =
      .ok (.indirect mp) m := by
  unfold annealValidityPlaceOperand
  simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind,
    stack_currentFrame?_singleton m.stack tf hframes, pure, EStateM.pure]

/-- `annealValidityHooks.readImmediate` on an uninitialized local raises
undefined behavior (`"read of uninitialized local"`). -/
theorem annealValidityHooks_readImmediate_uninit_local (layouts : LayoutTable) (c : Ty)
    {m : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf]) {idx : Nat} (hlt : idx < tf.locals.size)
    (hval : (tf.locals[idx]'hlt).value = .live (.immediate .uninit))
    (lay : Miri.Interpreter.LocalLayout) (ev : Miri.Memory.ExpectedValue) :
    (annealValidityHooks layouts).readImmediate c ⟨.local 0 idx none tf.localsIdentity, lay⟩ ev m =
      .error (.undefinedBehavior "read of uninitialized local") m := by
  have hop := annealValidityPlaceOperand_local hframes hlt hval lay
  show (annealValidityPlaceOperand ⟨.local 0 idx none tf.localsIdentity, lay⟩ >>= fun op =>
    annealReadImmediate ⟨op, lay⟩) m = _
  simp only [bind, EStateM.bind, hop]
  rfl

/-- `annealValidityHooks.readImmediate` on a dead local raises undefined
behavior (`"validation of a dead local"`). -/
theorem annealValidityHooks_readImmediate_dead_local (layouts : LayoutTable) (c : Ty)
    {m : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf]) {idx : Nat} (hlt : idx < tf.locals.size)
    (hdead : (tf.locals[idx]'hlt).value = .dead)
    (lay : Miri.Interpreter.LocalLayout) (ev : Miri.Memory.ExpectedValue) :
    (annealValidityHooks layouts).readImmediate c ⟨.local 0 idx none tf.localsIdentity, lay⟩ ev m =
      .error (.undefinedBehavior "validation of a dead local") m := by
  have hop := annealValidityPlaceOperand_dead_local hframes hlt hdead lay
  show (annealValidityPlaceOperand ⟨.local 0 idx none tf.localsIdentity, lay⟩ >>= fun op =>
    annealReadImmediate ⟨op, lay⟩) m = _
  simp only [bind, EStateM.bind, hop]

/-- `annealValidityHooks.readImmediate` on a primitive-layout `.memory` place
delegates to `annealReadMemoryPlace`. -/
theorem annealValidityHooks_readImmediate_memory (layouts : LayoutTable) (c : Ty)
    {m : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf])
    (mp : Miri.Interpreter.MemPlace AnnealProv)
    (lay : Miri.Interpreter.LocalLayout)
    (hfields : lay.layout.fields = .Primitive)
    (ev : Miri.Memory.ExpectedValue) :
    (annealValidityHooks layouts).readImmediate c ⟨.memory mp, lay⟩ ev m =
      annealReadMemoryPlace mp lay m := by
  have hop := annealValidityPlaceOperand_memory hframes mp lay
  show (annealValidityPlaceOperand ⟨.memory mp, lay⟩ >>= fun op =>
    annealReadImmediate ⟨op, lay⟩) m = _
  simp only [bind, EStateM.bind, hop, annealReadImmediate, hfields]

/-- `annealValidityHooks.withGhostValidation` is the identity on `EStateM`
computations. -/
@[simp]
theorem annealValidityHooks_withGhostValidation_eq (layouts : LayoutTable)
    {A : Type} (action : Miri.Interpreter.ValidityVisitor.M AnnealStepState A) :
    (annealValidityHooks layouts).withGhostValidation action = action := rfl

/-- `annealValidityHooks.typeName` returns the empty string without changing
the state. -/
@[simp]
theorem annealValidityHooks_typeName_eq (layouts : LayoutTable) (c : Ty)
    (tyId : Miri.MIR.TyId) :
    (annealValidityHooks layouts).typeName c tyId = pure "" := rfl

/-- Non-recursive, non-reset `ValidityVisitor.validatePlace` under
`annealValidityHooks` reduces to `ValidityVisitor.visit` from the empty root
session. -/
theorem validatePlace_annealValidityHooks_nonrecursive_eq
    (layouts : LayoutTable) (c : Ty) (fuel : Nat)
    (place : Miri.Interpreter.RuntimePlace AnnealProv) (m : AnnealStepState) :
    let initSession : Miri.Interpreter.ValidityVisitor.Session AnnealProv :=
      { path := ⟨"", #[]⟩
        flags := ⟨false, false⟩
        ctfeMode := none
        refTracking := none
        dataBytes := none }
    (∀ session' m',
      Miri.Interpreter.ValidityVisitor.visit (annealValidityHooks layouts) c fuel initSession place m =
        .ok session' m' →
      session'.dataBytes = none →
      Miri.Interpreter.ValidityVisitor.validatePlace (annealValidityHooks layouts) c fuel place
          false false m =
        .ok () m') ∧
    (∀ err m',
      Miri.Interpreter.ValidityVisitor.visit (annealValidityHooks layouts) c fuel initSession place m =
        .error err m' →
      Miri.Interpreter.ValidityVisitor.validatePlace (annealValidityHooks layouts) c fuel place
          false false m =
        .error err m') := by
  intro initSession
  refine ⟨fun session' m' hvisit hdb => ?_, fun err m' hvisit => ?_⟩
  · unfold Miri.Interpreter.ValidityVisitor.validatePlace
    simp only [annealValidityHooks_typeName_eq, annealValidityHooks_withGhostValidation_eq,
      Bool.false_eq_true, ↓reduceIte, bind, Bind.bind, EStateM.bind,
      pure, Pure.pure, EStateM.pure]
    rw [hvisit]
    dsimp only []
    rw [Miri.Interpreter.ValidityVisitor.resetPadding_no_ranges _ _ _ _ hdb]
    rfl
  · unfold Miri.Interpreter.ValidityVisitor.validatePlace
    simp only [annealValidityHooks_typeName_eq, annealValidityHooks_withGhostValidation_eq,
      Bool.false_eq_true, ↓reduceIte, bind, Bind.bind, EStateM.bind,
      pure, Pure.pure, EStateM.pure]
    rw [hvisit]

private theorem estate_bind_ok {ε σ α β : Type} (x : EStateM ε σ α) (f : α → EStateM ε σ β)
    (s s' : σ) (a : α) (hx : x s = .ok a s') :
    (x >>= f) s = f a s' := by
  show EStateM.bind x f s = f a s'
  simp [EStateM.bind, hx]

private theorem estate_bind_err {ε σ α β : Type} (x : EStateM ε σ α) (f : α → EStateM ε σ β)
    (s s' : σ) (e : ε) (hx : x s = .error e s') :
    (x >>= f) s = .error e s' := by
  show EStateM.bind x f s = .error e s'
  simp [EStateM.bind, hx]

private theorem ite_false_eq {c : Prop} [Decidable c] {α : Type} {t e : α} (h : ¬ c) :
    (if c then t else e) = e := by
  cases ‹Decidable c› with
  | isTrue hc => exact absurd hc h
  | isFalse _ => rfl

private theorem ite_true_eq {c : Prop} [Decidable c] {α : Type} {t e : α} (h : c) :
    (if c then t else e) = t := by
  cases ‹Decidable c› with
  | isTrue _ => rfl
  | isFalse hnc => exact absurd h hnc

/-- Reduction of `ValidityVisitor.visit` on primitive scalar `TypeKind`s
(`.never`, `.boolean`, `.character`, `.integer`) when `resetProvenanceAndPadding`
is disabled. -/
theorem visit_primitive_cases
    (h : Miri.Interpreter.ValidityVisitor.Hooks AnnealProv AnnealStepState Ty Unit Unit Unit Unit)
    (c : Ty) (fuel : Nat) (session : Miri.Interpreter.ValidityVisitor.Session AnnealProv)
    (place : Miri.Interpreter.RuntimePlace AnnealProv) (m : AnnealStepState)
    (hreset : session.flags.resetProvenanceAndPadding = false) :
    (h.classify c place.layout.ty m = .ok .never m →
      Miri.Interpreter.ValidityVisitor.visit h c (fuel + 1) session place m =
        .error (.undefinedBehavior s!"validation{session.path.render}: {"never value"}") m) ∧
    (∀ kind, (kind = .boolean ∨ kind = .character ∨ kind = .integer) →
      h.classify c place.layout.ty m = .ok kind m →
      ∀ err,
        h.readImmediate c place
            (match kind with | .boolean => .boolean | .character => .character | _ => .integer) m =
          .error err m →
        Miri.Interpreter.ValidityVisitor.visit h c (fuel + 1) session place m =
          .error err m) ∧
    (h.classify c place.layout.ty m = .ok .integer m →
      ∀ sc, h.readImmediate c place .integer m = .ok ⟨.scalar sc, place.layout⟩ m →
      Miri.Interpreter.ValidityVisitor.visit h c (fuel + 1) session place m =
        .ok session m) ∧
    (h.classify c place.layout.ty m = .ok .boolean m →
      ∀ sc, h.readImmediate c place .boolean m = .ok ⟨.scalar sc, place.layout⟩ m →
      (∀ b, sc.toBool = .ok b →
        Miri.Interpreter.ValidityVisitor.visit h c (fuel + 1) session place m =
          .ok session m) ∧
      (∀ err, sc.toBool = .error err →
        Miri.Interpreter.ValidityVisitor.visit h c (fuel + 1) session place m =
          .error (.undefinedBehavior s!"validation{session.path.render}: {repr err}") m)) ∧
    (h.classify c place.layout.ty m = .ok .character m →
      ∀ sc, h.readImmediate c place .character m = .ok ⟨.scalar sc, place.layout⟩ m →
      (∀ ch, sc.toChar = .ok ch →
        Miri.Interpreter.ValidityVisitor.visit h c (fuel + 1) session place m =
          .ok session m) ∧
      (∀ err, sc.toChar = .error err →
        Miri.Interpreter.ValidityVisitor.visit h c (fuel + 1) session place m =
          .error (.undefinedBehavior s!"validation{session.path.render}: {repr err}") m)) := by
  refine ⟨fun hcl => ?_, fun kind hk hcl err hrd => ?_, fun hcl sc hrd => ?_,
    fun hcl sc hrd => ⟨fun b hok => ?_, fun err herr => ?_⟩,
    fun hcl sc hrd => ⟨fun ch hok => ?_, fun err herr => ?_⟩⟩
  · unfold Miri.Interpreter.ValidityVisitor.visit
    rw [estate_bind_ok _ _ _ _ _ hcl]
    refine estate_bind_err _ _ _ _ _ ?_
    with_unfolding_all rfl
  · rcases hk with rfl | rfl | rfl <;>
    · unfold Miri.Interpreter.ValidityVisitor.visit
      rw [estate_bind_ok _ _ _ _ _ hcl]
      refine estate_bind_err _ _ _ _ _ ?_
      with_unfolding_all
        exact estate_bind_err _ _ _ _ _ hrd
  · unfold Miri.Interpreter.ValidityVisitor.visit
    rw [estate_bind_ok _ _ _ _ _ hcl]
    refine (estate_bind_ok _ _ _ _ (some session) ?_).trans rfl
    with_unfolding_all
      refine (estate_bind_ok _ _ _ _ _ hrd).trans ?_
      rw [hreset]
      rfl
  · unfold Miri.Interpreter.ValidityVisitor.visit
    rw [estate_bind_ok _ _ _ _ _ hcl]
    refine (estate_bind_ok _ _ _ _ (some session) ?_).trans rfl
    with_unfolding_all
      refine (estate_bind_ok _ _ _ _ _ hrd).trans ?_
      refine (estate_bind_ok _ _ _ _ sc rfl).trans ?_
      rw [hok, hreset]
      rfl
  · unfold Miri.Interpreter.ValidityVisitor.visit
    rw [estate_bind_ok _ _ _ _ _ hcl]
    refine estate_bind_err _ _ _ _ _ ?_
    with_unfolding_all
      refine (estate_bind_ok _ _ _ _ _ hrd).trans ?_
      refine (estate_bind_ok _ _ _ _ sc rfl).trans ?_
      rw [herr]
      rfl
  · unfold Miri.Interpreter.ValidityVisitor.visit
    rw [estate_bind_ok _ _ _ _ _ hcl]
    refine (estate_bind_ok _ _ _ _ (some session) ?_).trans rfl
    with_unfolding_all
      refine (estate_bind_ok _ _ _ _ _ hrd).trans ?_
      refine (estate_bind_ok _ _ _ _ sc rfl).trans ?_
      rw [hok, hreset]
      rfl
  · unfold Miri.Interpreter.ValidityVisitor.visit
    rw [estate_bind_ok _ _ _ _ _ hcl]
    refine estate_bind_err _ _ _ _ _ ?_
    with_unfolding_all
      refine (estate_bind_ok _ _ _ _ _ hrd).trans ?_
      refine (estate_bind_ok _ _ _ _ sc rfl).trans ?_
      rw [herr]
      rfl

/-- Reduction of `ValidityVisitor.visit` on safe reference `TypeKind.reference`
(`checkSafe`) when `resetProvenanceAndPadding = false`, `mayDangle = false`,
and `ctfeMode = none`, covering `readImmediate` failures, `checkPointerAccess`
failures (null, provenance-free integer, dead allocation, out-of-bounds),
`scalarMayBeNull` failures (e.g. ZST at address `0`), uninhabited pointees,
misalignment failures, and valid references (both non-recursive and with
`RefTracking` pointee queueing). -/
theorem visit_reference_cases
    (h : Miri.Interpreter.ValidityVisitor.Hooks AnnealProv AnnealStepState Ty Unit Unit Unit Unit)
    (c : Ty) (fuel : Nat) (session : Miri.Interpreter.ValidityVisitor.Session AnnealProv)
    (place : Miri.Interpreter.RuntimePlace AnnealProv) (m : AnnealStepState)
    (mutBool : Bool)
    (hcl : h.classify c place.layout.ty m = .ok (.reference mutBool) m)
    (hreset : session.flags.resetProvenanceAndPadding = false)
    (hmd : session.flags.mayDangle = false)
    (hctfe : session.ctfeMode = none) :
    (∀ err, h.readImmediate c place .reference m = .error err m →
      Miri.Interpreter.ValidityVisitor.visit h c (fuel + 1) session place m =
        .error err m) ∧
    (∀ ptrImm ptPlace,
      h.readImmediate c place .reference m = .ok ptrImm m →
      h.ptrToPlace c ptrImm m = .ok ptPlace m →
      ptPlace.layout.layout.isSized = true →
      h.sizeAndAlign c ptPlace m =
        .ok (some (ptPlace.layout.layout.size, ptPlace.layout.layout.align.abi)) m →
      (∀ accErr,
        h.checkPointerAccess c ptPlace.mplace.ptr ptPlace.layout.layout.size m =
          .ok (.error accErr) m →
        Miri.Interpreter.ValidityVisitor.visit h c (fuel + 1) session place m =
          .error (Miri.Interpreter.ValidityVisitor.classifyPointerAccessError
            session.path (.reference mutBool) accErr) m) ∧
      (∀ sc,
        h.checkPointerAccess c ptPlace.mplace.ptr ptPlace.layout.layout.size m =
          .ok (.ok ()) m →
        Miri.Memory.Scalar.fromMaybePointer h.target.base ptPlace.mplace.ptr = .ok sc →
        (h.scalarMayBeNull c sc m = .ok true m →
          Miri.Interpreter.ValidityVisitor.visit h c (fuel + 1) session place m =
            .error (.undefinedBehavior
              s!"validation{session.path.render}: {"null or maybe-null safe pointer"}") m) ∧
        (h.scalarMayBeNull c sc m = .ok false m →
          (h.opsemInhabited c ptPlace.layout.ty m = .ok false m →
            Miri.Interpreter.ValidityVisitor.visit h c (fuel + 1) session place m =
              .error (.undefinedBehavior
                s!"validation{session.path.render}: {"safe pointer to uninhabited type"}") m) ∧
          (h.opsemInhabited c ptPlace.layout.ty m = .ok true m →
            (∀ mis,
              h.checkPointerAlignResult c ptPlace.mplace.ptr
                  ptPlace.layout.layout.align.abi m = .ok (.error mis) m →
              Miri.Interpreter.ValidityVisitor.visit h c (fuel + 1) session place m =
                .error (Miri.Interpreter.ValidityVisitor.classifyPointerAlignmentError
                  session.path (.reference mutBool) mis) m) ∧
            (h.checkPointerAlignResult c ptPlace.mplace.ptr
                ptPlace.layout.layout.align.abi m = .ok (.ok ()) m →
              Miri.Interpreter.ValidityVisitor.visit h c (fuel + 1) session place m =
                .ok { session with
                  refTracking := session.refTracking.map fun tracker =>
                    tracker.track ⟨ptPlace.mplace, ptPlace.layout⟩
                      (fun _ => session.path.push .deref) } m))))) := by
  refine ⟨fun err hrd => ?_, fun ptrImm ptPlace hrd hptr hsized hdyn =>
    ⟨fun accErr hacc => ?_, fun sc hacc hsc =>
      ⟨fun hnull => ?_, fun hnull =>
        ⟨fun hinh => ?_, fun hinh => ⟨fun mis hal => ?_, fun hal => ?_⟩⟩⟩⟩⟩
  · unfold Miri.Interpreter.ValidityVisitor.visit
    rw [estate_bind_ok _ _ _ _ _ hcl]
    refine estate_bind_err _ _ _ _ _ ?_
    with_unfolding_all
      refine estate_bind_err _ _ _ _ _ ?_
      exact estate_bind_err _ _ _ _ _ hrd
  · unfold Miri.Interpreter.ValidityVisitor.visit
    rw [estate_bind_ok _ _ _ _ _ hcl]
    refine estate_bind_err _ _ _ _ _ ?_
    with_unfolding_all
      refine estate_bind_err _ _ _ _ _ ?_
      refine (estate_bind_ok _ _ _ _ _ hrd).trans ?_
      rw [hreset, ite_false_eq (by decide)]
      refine (estate_bind_ok _ _ _ _ _ hptr).trans ?_
      rw [hsized, ite_false_eq (by decide)]
      refine (estate_bind_ok _ _ _ _ _ hdyn).trans ?_
      rw [Option.getD_some, hmd]; dsimp only []; rw [ite_true_eq (by decide)]
      exact (estate_bind_ok _ _ _ _ _ hacc).trans rfl
  · unfold Miri.Interpreter.ValidityVisitor.visit
    rw [estate_bind_ok _ _ _ _ _ hcl]
    refine estate_bind_err _ _ _ _ _ ?_
    with_unfolding_all
      refine estate_bind_err _ _ _ _ _ ?_
      refine (estate_bind_ok _ _ _ _ _ hrd).trans ?_
      rw [hreset, ite_false_eq (by decide)]
      refine (estate_bind_ok _ _ _ _ _ hptr).trans ?_
      rw [hsized, ite_false_eq (by decide)]
      refine (estate_bind_ok _ _ _ _ _ hdyn).trans ?_
      rw [Option.getD_some, hmd]; dsimp only []; rw [ite_true_eq (by decide)]
      refine (estate_bind_ok _ _ _ _ _ hacc).trans ?_
      dsimp only []
      rw [hreset, ite_false_eq (by decide)]
      refine (estate_bind_ok _ _ _ _ none rfl).trans ?_
      dsimp only []
      rw [ite_false_eq (by decide)]
      refine (estate_bind_ok _ _ _ _ sc (by rw [hsc]; rfl)).trans ?_
      refine (estate_bind_ok _ _ _ _ _ hnull).trans rfl
  · unfold Miri.Interpreter.ValidityVisitor.visit
    rw [estate_bind_ok _ _ _ _ _ hcl]
    refine estate_bind_err _ _ _ _ _ ?_
    with_unfolding_all
      refine estate_bind_err _ _ _ _ _ ?_
      refine (estate_bind_ok _ _ _ _ _ hrd).trans ?_
      rw [hreset, ite_false_eq (by decide)]
      refine (estate_bind_ok _ _ _ _ _ hptr).trans ?_
      rw [hsized, ite_false_eq (by decide)]
      refine (estate_bind_ok _ _ _ _ _ hdyn).trans ?_
      rw [Option.getD_some, hmd]; dsimp only []; rw [ite_true_eq (by decide)]
      refine (estate_bind_ok _ _ _ _ _ hacc).trans ?_
      dsimp only []
      rw [hreset, ite_false_eq (by decide)]
      refine (estate_bind_ok _ _ _ _ none rfl).trans ?_
      dsimp only []
      rw [ite_false_eq (by decide)]
      refine (estate_bind_ok _ _ _ _ sc (by rw [hsc]; rfl)).trans ?_
      refine (estate_bind_ok _ _ _ _ _ hnull).trans ?_
      rw [ite_false_eq (by decide)]
      refine (estate_bind_ok _ _ _ _ _ hinh).trans rfl
  · unfold Miri.Interpreter.ValidityVisitor.visit
    rw [estate_bind_ok _ _ _ _ _ hcl]
    refine estate_bind_err _ _ _ _ _ ?_
    with_unfolding_all
      refine estate_bind_err _ _ _ _ _ ?_
      refine (estate_bind_ok _ _ _ _ _ hrd).trans ?_
      rw [hreset, ite_false_eq (by decide)]
      refine (estate_bind_ok _ _ _ _ _ hptr).trans ?_
      rw [hsized, ite_false_eq (by decide)]
      refine (estate_bind_ok _ _ _ _ _ hdyn).trans ?_
      rw [Option.getD_some, hmd]; dsimp only []; rw [ite_true_eq (by decide)]
      refine (estate_bind_ok _ _ _ _ _ hacc).trans ?_
      dsimp only []
      rw [hreset, ite_false_eq (by decide)]
      refine (estate_bind_ok _ _ _ _ none rfl).trans ?_
      dsimp only []
      rw [ite_false_eq (by decide)]
      refine (estate_bind_ok _ _ _ _ sc (by rw [hsc]; rfl)).trans ?_
      refine (estate_bind_ok _ _ _ _ _ hnull).trans ?_
      rw [ite_false_eq (by decide)]
      refine (estate_bind_ok _ _ _ _ _ hinh).trans ?_
      rw [ite_true_eq (by decide)]
      refine estate_bind_err _ _ _ _ _ ?_
      unfold Miri.Interpreter.ValidityVisitor.mapPointerAlignmentOutcome
      rw [hal]
  · let session' : Miri.Interpreter.ValidityVisitor.Session AnnealProv :=
      { session with
        refTracking := session.refTracking.map fun tracker =>
          tracker.track ⟨ptPlace.mplace, ptPlace.layout⟩
            (fun _ => session.path.push .deref) }
    unfold Miri.Interpreter.ValidityVisitor.visit
    rw [estate_bind_ok _ _ _ _ _ hcl]
    refine (estate_bind_ok _ _ _ _ (some session') ?_).trans rfl
    with_unfolding_all
      refine (estate_bind_ok _ _ _ _ session' ?_).trans rfl
      refine (estate_bind_ok _ _ _ _ _ hrd).trans ?_
      rw [hreset, ite_false_eq (by decide)]
      refine (estate_bind_ok _ _ _ _ _ hptr).trans ?_
      rw [hsized, ite_false_eq (by decide)]
      refine (estate_bind_ok _ _ _ _ _ hdyn).trans ?_
      rw [Option.getD_some, hmd]; dsimp only []; rw [ite_true_eq (by decide)]
      refine (estate_bind_ok _ _ _ _ _ hacc).trans ?_
      dsimp only []
      rw [hreset, ite_false_eq (by decide)]
      refine (estate_bind_ok _ _ _ _ none rfl).trans ?_
      dsimp only []
      rw [ite_false_eq (by decide)]
      refine (estate_bind_ok _ _ _ _ sc (by rw [hsc]; rfl)).trans ?_
      refine (estate_bind_ok _ _ _ _ _ hnull).trans ?_
      rw [ite_false_eq (by decide)]
      refine (estate_bind_ok _ _ _ _ _ hinh).trans ?_
      rw [ite_true_eq (by decide)]
      have hal' : Miri.Interpreter.ValidityVisitor.mapPointerAlignmentOutcome
          session.path (.reference mutBool)
          (h.checkPointerAlignResult c ptPlace.mplace.ptr ptPlace.layout.layout.align.abi) m =
          .ok () m := by
        unfold Miri.Interpreter.ValidityVisitor.mapPointerAlignmentOutcome
        rw [hal]
      refine (estate_bind_ok _ _ _ _ PUnit.unit hal').trans ?_
      show _ = EStateM.Result.ok session' m
      cases session with | mk path flags ctfe refTr db =>
      dsimp only [session'] at hmd hctfe ⊢
      subst hctfe
      cases refTr with
      | none => rfl
      | some tr => rfl

private theorem tryFromUInt_8_of_u64 (addr : UInt64) :
    Miri.Memory.ScalarInt.tryFromUInt (BitVec.ofNat 128 addr.toNat) (Miri.ABI.Size.ofBytes 8) =
      .ok (some (.ofUInt64 addr)) := by
  have hbv : BitVec.zeroExtend 128
      (BitVec.extractLsb (((Miri.ABI.Size.ofBytes 8).bytes * 8).toNat - 1) 0
        (BitVec.ofNat 128 addr.toNat)) =
      BitVec.ofNat 128 addr.toNat := by
    have hlt64 : addr.toNat < 2 ^ 64 := addr.toNat_lt
    have hlt128 : addr.toNat < 2 ^ 128 := by omega
    apply BitVec.eq_of_toNat_eq
    change (BitVec.zeroExtend 128 (BitVec.extractLsb 63 0 (BitVec.ofNat 128 addr.toNat))).toNat =
      (BitVec.ofNat 128 addr.toNat).toNat
    simp [BitVec.extractLsb, BitVec.extractLsb', Nat.mod_eq_of_lt hlt128]
  with_unfolding_all
    conv => lhs; whnf
    rw [hbv, bne_self_eq_false]
    rfl

private theorem fromPointer_tryToScalarInt_eq (addr : UInt64) (prov : AnnealProv) :
    (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
      ⟨Miri.ABI.Size.ofBytes addr, prov⟩).tryToScalarInt =
      .ok (.integer (.ofUInt64 addr)) := by
  with_unfolding_all
    change ((do
        let scalar ← (Miri.Memory.ScalarInt.tryFromUInt (BitVec.ofNat 128 addr.toNat)
          (Miri.ABI.Size.ofBytes 8)).mapError (fun e => Miri.Memory.ScalarError.scalarInt e)
        match scalar with
        | some scalar => pure (.integer scalar)
        | none => throw (.pointerOffsetDoesNotFit (Miri.ABI.Size.ofBytes addr)
            (Miri.ABI.Size.ofBytes 8))) :
        Except Miri.Memory.ScalarError Miri.Memory.ScalarIntCastResult) =
      .ok (.integer (.ofUInt64 addr))
    rw [tryFromUInt_8_of_u64]
    rfl

private theorem fromPointer_scalarMayBeNull_eq (layouts : LayoutTable) (c : Ty)
    (addr : UInt64) (prov : AnnealProv) (m : AnnealStepState) (hne : (addr == 0) = false) :
    (annealValidityHooks layouts).scalarMayBeNull c
      (Miri.Memory.Scalar.fromPointer annealTargetDataLayout ⟨Miri.ABI.Size.ofBytes addr, prov⟩) m =
      .ok false m := by
  have hne0 : (Miri.Memory.ScalarInt.ofUInt64 addr).isNull = false := by
    with_unfolding_all
      show (BitVec.ofNat 128 addr.toNat == 0) = false
      cases h : (BitVec.ofNat 128 addr.toNat == 0) with
      | false => rfl
      | true =>
        have heq := congrArg BitVec.toNat (beq_iff_eq.mp h)
        have hlt128 : addr.toNat < 2 ^ 128 := by have := addr.toNat_lt; omega
        simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt128] at heq
        have ha0 : addr = 0 := UInt64.toNat_inj.mp heq
        rw [ha0] at hne
        cases hne
  simp only [annealValidityHooks, fromPointer_tryToScalarInt_eq, hne0, pure, EStateM.pure]

private theorem prim_opsemInhabited_true (layouts : LayoutTable) (c : Ty) {ty : Ty}
    (hprim : IsPrimScalarTy ty) (m : AnnealStepState) :
    (annealValidityHooks layouts).opsemInhabited c (translateTy ty layouts).ty m = .ok true m := by
  rcases hprim with h | h | ⟨it, h⟩ | ⟨ut, h⟩
  · simp only [annealValidityHooks, translateTy, encodeTyId, h]; rfl
  · simp only [annealValidityHooks, translateTy, encodeTyId, h]; rfl
  · cases it <;> (simp only [annealValidityHooks, translateTy, encodeTyId, h]; rfl)
  · cases ut <;> (simp only [annealValidityHooks, translateTy, encodeTyId, h]; rfl)

private theorem prim_layout_fields_eq {ty : Ty} (layouts : LayoutTable)
    (hprim : IsPrimScalarTy ty) :
    (translateTy ty layouts).layout.fields = .Primitive := by
  rcases hprim with h | h | ⟨it, h⟩ | ⟨ut, h⟩
  · simp only [translateTy, h, scalarLayoutData]
  · simp only [translateTy, h, scalarLayoutData]
  · cases it <;> simp only [translateTy, h, scalarLayoutData]
  · cases ut <;> simp only [translateTy, h, scalarLayoutData]

/-- **End-to-end primitive scalar `ValidityVisitor.validatePlace` simulation (`LM-3.2`)**:
running the vendored `Miri.Interpreter.ValidityVisitor.validatePlace` under
`annealValidityHooks` on a root-frame local `idx` (`recursive := false`,
`reset := false`) matches Anneal's scalar validity invariants across all local
states and primitive types:

1. **Uninhabited `!` (`ty.kind = .never`)**: `validatePlace` raises undefined
   behavior (`"validation: never value"`).
2. **Dead local (`.dead`)**: `validatePlace` raises undefined behavior
   (`"validation of a dead local"`).
3. **Uninitialized local (`.uninit`)**: `validatePlace` raises undefined
   behavior (`"read of uninitialized local"`).
4. **Initialized scalar (`.fromScalarInt msc`, `ScalarRel sc msc`)**: for any
   `IsPrimScalarTy ty` (`bool`, `char`, `i8..i128`, `isize`, `u8..u128`, `usize`),
   `validatePlace` succeeds (`.ok () m`) iff `AnnealScalarValid ty sc` holds
   (`0`/`1` for `bool`, valid Unicode scalar value for `char`, and unrestricted
   for integers), and raises `.error (.undefinedBehavior msg) m` iff
   `¬ AnnealScalarValid ty sc`. -/
theorem validatePlace_prim_scalar_simulation
    (layouts : LayoutTable) {ty : Ty} (fuel : Nat)
    {m : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf]) {idx : Nat} (hlt : idx < tf.locals.size) :
    let place : Miri.Interpreter.RuntimePlace AnnealProv :=
      ⟨.local 0 idx none tf.localsIdentity, translateTy ty layouts⟩
    (ty.kind = .never →
      Miri.Interpreter.ValidityVisitor.validatePlace (annealValidityHooks layouts) ty (fuel + 1)
        place false false m =
        .error (.undefinedBehavior "validation: never value") m) ∧
    (IsPrimScalarTy ty →
      (tf.locals[idx]'hlt).value = .dead →
      Miri.Interpreter.ValidityVisitor.validatePlace (annealValidityHooks layouts) ty (fuel + 1)
        place false false m =
        .error (.undefinedBehavior "validation of a dead local") m) ∧
    (IsPrimScalarTy ty →
      (tf.locals[idx]'hlt).value = .live (.immediate .uninit) →
      Miri.Interpreter.ValidityVisitor.validatePlace (annealValidityHooks layouts) ty (fuel + 1)
        place false false m =
        .error (.undefinedBehavior "read of uninitialized local") m) ∧
    (∀ {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt},
      IsPrimScalarTy ty →
      ScalarRel sc msc →
      (translateTy ty layouts).layout.size = translateSizeBytes sc.sizeBytes →
      (tf.locals[idx]'hlt).value = .live (.immediate (.scalar (.fromScalarInt msc))) →
      (Miri.Interpreter.ValidityVisitor.validatePlace (annealValidityHooks layouts) ty (fuel + 1)
          place false false m = .ok () m ↔ AnnealScalarValid ty sc) ∧
      ((∃ msg, Miri.Interpreter.ValidityVisitor.validatePlace (annealValidityHooks layouts) ty
          (fuel + 1) place false false m = .error (.undefinedBehavior msg) m) ↔
        ¬ AnnealScalarValid ty sc)) := by
  intro place
  let initSession : Miri.Interpreter.ValidityVisitor.Session AnnealProv :=
    { path := ⟨"", #[]⟩, flags := ⟨false, false⟩, ctfeMode := none,
      refTracking := none, dataBytes := none }
  have hv := visit_primitive_cases (annealValidityHooks layouts) ty fuel initSession place m rfl
  have hvp := validatePlace_annealValidityHooks_nonrecursive_eq layouts ty (fuel + 1) place m
  obtain ⟨hcb, hcc, hci, hcu, hcn⟩ := annealValidityHooks_classify_prim layouts ty (ty := ty) m
  refine ⟨fun hk => ?_, fun hprim hdead => ?_, fun hprim hun => ?_,
    fun {sc msc} hprim hrel hsz hval => ?_⟩
  · exact hvp.2 _ _ (hv.1 (hcn hk))
  · have hrd := annealValidityHooks_readImmediate_dead_local layouts ty hframes hlt hdead
      (translateTy ty layouts)
    rcases hprim with hk | hk | ⟨it, hk⟩ | ⟨ut, hk⟩
    · exact hvp.2 _ _ (hv.2.1 .boolean (Or.inl rfl) (hcb hk) _ (hrd .boolean))
    · exact hvp.2 _ _ (hv.2.1 .character (Or.inr (Or.inl rfl)) (hcc hk) _ (hrd .character))
    · exact hvp.2 _ _ (hv.2.1 .integer (Or.inr (Or.inr rfl)) (hci it hk) _ (hrd .integer))
    · exact hvp.2 _ _ (hv.2.1 .integer (Or.inr (Or.inr rfl)) (hcu ut hk) _ (hrd .integer))
  · have hrd := annealValidityHooks_readImmediate_uninit_local layouts ty hframes hlt hun
      (translateTy ty layouts)
    rcases hprim with hk | hk | ⟨it, hk⟩ | ⟨ut, hk⟩
    · exact hvp.2 _ _ (hv.2.1 .boolean (Or.inl rfl) (hcb hk) _ (hrd .boolean))
    · exact hvp.2 _ _ (hv.2.1 .character (Or.inr (Or.inl rfl)) (hcc hk) _ (hrd .character))
    · exact hvp.2 _ _ (hv.2.1 .integer (Or.inr (Or.inr rfl)) (hci it hk) _ (hrd .integer))
    · exact hvp.2 _ _ (hv.2.1 .integer (Or.inr (Or.inr rfl)) (hcu ut hk) _ (hrd .integer))
  · have hrd := annealValidityHooks_readImmediate_local layouts ty hframes hlt hval
      (translateTy ty layouts)
    rcases hprim with hk | hk | ⟨it, hk⟩ | ⟨ut, hk⟩
    · obtain ⟨hsz1, _⟩ := sizeBytes_eq_of_translateTy (Or.inl hk) hrel.validBytes hsz
      have hsz1' : sc.sizeBytes = 1 := by rw [hsz1]; simp [boolOrIntByteWidth, hk]
      have hb_iff := fromScalarInt_toBool_ok_iff hrel hsz1'
      have hav_iff : AnnealScalarValid ty sc ↔ (sc.bits = 0 ∨ sc.bits = 1) := by
        unfold AnnealScalarValid
        exact ⟨fun h => h.1 hk, fun h => ⟨fun _ => h, fun hc => (by rw [hk] at hc; cases hc)⟩⟩
      cases htb : (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) msc).toBool with
      | ok b =>
        have hok := hvp.1 initSession m ((hv.2.2.2.1 (hcb hk) _ (hrd .boolean)).1 b htb) rfl
        have hav : AnnealScalarValid ty sc := hav_iff.mpr (hb_iff.mp ⟨b, htb⟩)
        rw [hok]
        exact ⟨⟨fun _ => hav, fun _ => rfl⟩,
          ⟨(by rintro ⟨_, h⟩; cases h), fun hnav => absurd hav hnav⟩⟩
      | error err =>
        have herr := hvp.2 _ m ((hv.2.2.2.1 (hcb hk) _ (hrd .boolean)).2 err htb)
        have hnav : ¬ AnnealScalarValid ty sc := by
          intro hav
          obtain ⟨b, hb⟩ := hb_iff.mpr (hav_iff.mp hav)
          rw [htb] at hb
          cases hb
        rw [herr]
        exact ⟨⟨fun h => (by cases h), fun hav => absurd hav hnav⟩,
          ⟨fun _ => hnav, fun _ => ⟨_, rfl⟩⟩⟩
    · have hsz4 : sc.sizeBytes = 4 := by
        rcases hrel.validBytes with h | h | h | h | h
        · rw [h] at hsz; simp [translateTy, hk, scalarLayoutData, translateSizeBytes, Miri.ABI.Size.ofBytes] at hsz
        · rw [h] at hsz; simp [translateTy, hk, scalarLayoutData, translateSizeBytes, Miri.ABI.Size.ofBytes] at hsz
        · exact h
        · rw [h] at hsz; simp [translateTy, hk, scalarLayoutData, translateSizeBytes, Miri.ABI.Size.ofBytes] at hsz
        · rw [h] at hsz; simp [translateTy, hk, scalarLayoutData, translateSizeBytes, Miri.ABI.Size.ofBytes] at hsz
      have hc_iff := fromScalarInt_toChar_ok_iff hrel hsz4
      have hav_iff : AnnealScalarValid ty sc ↔ isValidCharCode sc.bits = true := by
        unfold AnnealScalarValid
        exact ⟨fun h => h.2 hk, fun h => ⟨fun hb => (by rw [hk] at hb; cases hb), fun _ => h⟩⟩
      cases htc : (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) msc).toChar with
      | ok ch =>
        have hok := hvp.1 initSession m ((hv.2.2.2.2 (hcc hk) _ (hrd .character)).1 ch htc) rfl
        have hav : AnnealScalarValid ty sc := hav_iff.mpr (hc_iff.mp ⟨ch, htc⟩)
        rw [hok]
        exact ⟨⟨fun _ => hav, fun _ => rfl⟩,
          ⟨(by rintro ⟨_, h⟩; cases h), fun hnav => absurd hav hnav⟩⟩
      | error err =>
        have herr := hvp.2 _ m ((hv.2.2.2.2 (hcc hk) _ (hrd .character)).2 err htc)
        have hnav : ¬ AnnealScalarValid ty sc := by
          intro hav
          obtain ⟨c, hc⟩ := hc_iff.mpr (hav_iff.mp hav)
          rw [htc] at hc
          cases hc
        rw [herr]
        exact ⟨⟨fun h => (by cases h), fun hav => absurd hav hnav⟩,
          ⟨fun _ => hnav, fun _ => ⟨_, rfl⟩⟩⟩
    · have hok := hvp.1 initSession m (hv.2.2.1 (hci it hk) _ (hrd .integer)) rfl
      have hav : AnnealScalarValid ty sc :=
        ⟨fun hb => (by rw [hk] at hb; cases hb), fun hc => (by rw [hk] at hc; cases hc)⟩
      rw [hok]
      exact ⟨⟨fun _ => hav, fun _ => rfl⟩,
        ⟨(by rintro ⟨_, h⟩; cases h), fun hnav => absurd hav hnav⟩⟩
    · have hok := hvp.1 initSession m (hv.2.2.1 (hcu ut hk) _ (hrd .integer)) rfl
      have hav : AnnealScalarValid ty sc :=
        ⟨fun hb => (by rw [hk] at hb; cases hb), fun hc => (by rw [hk] at hc; cases hc)⟩
      rw [hok]
      exact ⟨⟨fun _ => hav, fun _ => rfl⟩,
        ⟨(by rintro ⟨_, h⟩; cases h), fun hnav => absurd hav hnav⟩⟩

/-- **End-to-end safe-reference `ValidityVisitor.validatePlace` simulation (`LM-3.2`)**:
in any `StateRelLM3_2` state (`m.stack.frames = #[tf]`), running the vendored
`Miri.Interpreter.ValidityVisitor.validatePlace` (`recursive := false`,
`reset := false`) on a local `refIdx` of safe-reference type `&T` / `&mut T`
with primitive-scalar pointee `T`:

1. **Dead local (`_r` is `.dead`)**: raises `.error (.undefinedBehavior "validation of a dead local") m`.
2. **Uninitialized local (`_r` is `.uninit`)**: raises `.error (.undefinedBehavior "read of uninitialized local") m`.
3. **Null or provenance-free integer scalar in `_r`**: raises `.error (.undefinedBehavior msg) m`
   (`"validation: encountered a null reference"` when `sc.bits = 0`, and
   dangling no-provenance UB when `sc.bits ≠ 0`), matching Anneal's `.ub` on `copy *_r`.
4. **Pointer `p` (`PtrRel allocMap p mptr`) into stack allocation `e ∈ allocMap` (`e.tag = p.tag`)**:
   - **Live offset-`0` pointee (`slot ≠ .dead`, `p.offsetBytes = 0`)**: `validatePlace` succeeds with `.ok () m`.
   - **Out-of-bounds offset (`slot ≠ .dead`, `0 < p.offsetBytes`)**: raises `.error (.undefinedBehavior "validation: encountered a dangling reference (going beyond the bounds of its allocation)") m`.
   - **Dangling pointee after `StorageDead` (`get? s.frame.locals e.localIdx = some .dead`)**: raises `.error (.undefinedBehavior "validation: encountered a dangling reference (use-after-free)") m`. -/
theorem validatePlace_ref_nonrecursive_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf])
    {refIdx : Nat} (hlt : refIdx < tf.locals.size)
    {targetTy : Ty} (hprim : IsPrimScalarTy targetTy)
    {refTy : Ty} {refMut : Mutability}
    (hrefTy : refTy.kind = .ref refMut targetTy.kind)
    (fuel : Nat) :
    let place : Miri.Interpreter.RuntimePlace AnnealProv :=
      ⟨.local 0 refIdx none tf.localsIdentity, translateTy refTy body.layouts⟩
    ((tf.locals[refIdx]'hlt).value = .dead →
      Miri.Interpreter.ValidityVisitor.validatePlace (annealValidityHooks body.layouts) refTy
        (fuel + 1) place false false m =
        .error (.undefinedBehavior "validation of a dead local") m) ∧
    ((tf.locals[refIdx]'hlt).value = .live (.immediate .uninit) →
      Miri.Interpreter.ValidityVisitor.validatePlace (annealValidityHooks body.layouts) refTy
        (fuel + 1) place false false m =
        .error (.undefinedBehavior "read of uninitialized local") m) ∧
    (∀ {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt},
      ScalarRel sc msc → sc.sizeBytes = 8 →
      (tf.locals[refIdx]'hlt).value = .live (.immediate (.scalar (.fromScalarInt msc))) →
      (sc.bits = 0 →
        Miri.Interpreter.ValidityVisitor.validatePlace (annealValidityHooks body.layouts) refTy
          (fuel + 1) place false false m =
          .error (.undefinedBehavior "validation: encountered a null reference") m) ∧
      (sc.bits ≠ 0 →
        ∃ msg, Miri.Interpreter.ValidityVisitor.validatePlace (annealValidityHooks body.layouts) refTy
          (fuel + 1) place false false m = .error (.undefinedBehavior msg) m)) ∧
    (∀ {p : ProvenancePtr} {mptr : Miri.Memory.Pointer AnnealProv} {e : AllocMapEntry},
      PtrRel allocMap p mptr → e ∈ allocMap → e.tag = p.tag →
      (∃ d, get? body.localDecls e.localIdx = some d ∧ d.ty = targetTy) →
      (tf.locals[refIdx]'hlt).value =
        .live (.immediate (.scalar (.fromPointer annealTargetDataLayout mptr))) →
      (∀ slot, get? s.frame.locals e.localIdx = some slot → slot ≠ .dead → p.offsetBytes = 0 →
        Miri.Interpreter.ValidityVisitor.validatePlace (annealValidityHooks body.layouts) refTy
          (fuel + 1) place false false m = .ok () m) ∧
      (∀ slot, get? s.frame.locals e.localIdx = some slot → slot ≠ .dead → 0 < p.offsetBytes →
        Miri.Interpreter.ValidityVisitor.validatePlace (annealValidityHooks body.layouts) refTy
          (fuel + 1) place false false m =
          .error (.undefinedBehavior
            "validation: encountered a dangling reference (going beyond the bounds of its allocation)") m) ∧
      (get? s.frame.locals e.localIdx = some .dead →
        Miri.Interpreter.ValidityVisitor.validatePlace (annealValidityHooks body.layouts) refTy
          (fuel + 1) place false false m =
          .error (.undefinedBehavior
            "validation: encountered a dangling reference (use-after-free)") m)) := by
  intro place
  let initSession : Miri.Interpreter.ValidityVisitor.Session AnnealProv :=
    { path := ⟨"", #[]⟩, flags := ⟨false, false⟩, ctfeMode := none,
      refTracking := none, dataBytes := none }
  let mutBool : Bool := match refMut with | .mut => true | .not => false
  have hcl : (annealValidityHooks body.layouts).classify refTy (translateTy refTy body.layouts).ty m =
      .ok (.reference mutBool) m := by
    cases refMut <;> (simp only [annealValidityHooks, annealValidityClassify, translateTy,
      encodeTyId, hrefTy, mutBool]; rfl)
  have hvr := visit_reference_cases (annealValidityHooks body.layouts) refTy fuel initSession
    place m mutBool hcl rfl rfl rfl
  have hvp := validatePlace_annealValidityHooks_nonrecursive_eq body.layouts refTy (fuel + 1) place m
  have hptLay : annealValidityPointeeLayout body.layouts refTy =
      some (translateTy targetTy body.layouts) := by
    have hexact : derefPointeeKindHasExactLayout targetTy.kind = true := by
      rcases hprim with h | h | ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h] <;> rfl
    unfold annealValidityPointeeLayout
    rw [hrefTy]
    dsimp only []
    rw [hexact]
    simp only [↓reduceIte, Option.some.injEq]
    exact hprim.translateTy_layoutIdx body.layouts
  obtain ⟨hsized, _, _⟩ := hprim.layout_ok (layouts := body.layouts)
  obtain ⟨hsize, hpos, hfit, _, hpow, _⟩ := hprim.size_align_ok body.layouts
  have hpos_nat : 0 < (translateTy targetTy body.layouts).layout.size.bytes.toNat := by
    exact_mod_cast hpos
  refine ⟨fun hdead => ?_, fun hun => ?_, fun {sc msc} hrel hsz8 hval => ?_,
    fun {p mptr e} hptr he htag hdecl_or hval => ?_⟩
  · exact hvp.2 _ _ (hvr.1 _ (annealValidityHooks_readImmediate_dead_local body.layouts refTy
      hframes hlt hdead _ .reference))
  · exact hvp.2 _ _ (hvr.1 _ (annealValidityHooks_readImmediate_uninit_local body.layouts refTy
      hframes hlt hun _ .reference))
  · have hrd := annealValidityHooks_readImmediate_local body.layouts refTy hframes hlt hval
      (translateTy refTy body.layouts) .reference
    obtain ⟨mis, hmis⟩ := annealOffsetMisalignment_ok_of_pow2
      (Miri.Memory.Pointer.withoutProvenance (Prov := AnnealProv) (UInt64.ofNat sc.bits)).offset
      (translateTy targetTy body.layouts).layout.align.abi hpow
    let ptPlace : Miri.Interpreter.MPlaceTy AnnealProv :=
      ⟨⟨Miri.Memory.Pointer.withoutProvenance (UInt64.ofNat sc.bits), .none, mis⟩,
        translateTy targetTy body.layouts⟩
    have hptr_p : (annealValidityHooks body.layouts).ptrToPlace refTy
        ⟨.scalar (.fromScalarInt msc), translateTy refTy body.layouts⟩ m = .ok ptPlace m := by
      show (do _ : EStateM _ _ _) m = .ok ptPlace m
      simp only [annealValidityHooks, hptLay, Miri.Interpreter.Immediate.toScalar,
        scalar_fromScalarInt_toPointer_eq hrel hsz8, hmis, bind, EStateM.bind, pure, EStateM.pure]
      rfl
    have hdyn : (annealValidityHooks body.layouts).sizeAndAlign refTy ptPlace m =
        .ok (some (ptPlace.layout.layout.size, ptPlace.layout.layout.align.abi)) m := by
      simp only [annealValidityHooks, ptPlace, hsized, ↓reduceIte]; rfl
    have hck := checkAndDerefPtr_withoutProvenance_err m.machine (UInt64.ofNat sc.bits)
      ((translateTy targetTy body.layouts).layout.size.bytes.toNat : Int)
      (.dereferenceable "pointer") hpos hfit
    have hacc : (annealValidityHooks body.layouts).checkPointerAccess refTy ptPlace.mplace.ptr
        ptPlace.layout.layout.size m =
        .ok (.error (.danglingIntegerPointer (UInt64.ofNat sc.bits)
          ((translateTy targetTy body.layouts).layout.size.bytes.toNat : Int)
          (.dereferenceable "pointer"))) m := by
      rw [annealValidityHooks_checkPointerAccess_eq]
      unfold annealValidityAccessCheck
      simp only [ptPlace]
      split
      · rename_i heq; rw [hsize] at heq; cases heq
      · rename_i n heq; rw [hsize] at heq; cases heq; rw [hck]
    have herr := hvp.2 _ _ ((hvr.2 _ ptPlace hrd hptr_p hsized hdyn).1 _ hacc)
    refine ⟨fun h0 => ?_, fun hne => ?_⟩
    · rw [herr, h0]
      cases mutBool <;> rfl
    · rw [herr]
      cases mutBool <;> exact ⟨_, rfl⟩
  · obtain ⟨tf₀, hframes₀, _, _, _, _, _, _, _, _, halloc, _⟩ := id hstate
    rw [hframes] at hframes₀; injection hframes₀ with h0; injection h0 with htf; subst htf
    obtain ⟨targetDecl, hdecl_t, hd_ty⟩ := hdecl_or
    subst hd_ty
    obtain ⟨borTag, hmptr, hoff_lt⟩ := PtrRel.allocId_of_entry halloc hptr he htag
    obtain ⟨hid, _, hbase⟩ := halloc.base_addr_valid e he
    have hrd := annealValidityHooks_readImmediate_local body.layouts refTy hframes hlt hval
      (translateTy refTy body.layouts) .reference
    obtain ⟨mis, hmis⟩ := annealOffsetMisalignment_ok_of_pow2 mptr.withOptionalProvenance.offset
      (translateTy targetDecl.ty body.layouts).layout.align.abi hpow
    let ptPlace : Miri.Interpreter.MPlaceTy AnnealProv :=
      ⟨⟨mptr.withOptionalProvenance, .none, mis⟩, translateTy targetDecl.ty body.layouts⟩
    have hptr_p : (annealValidityHooks body.layouts).ptrToPlace refTy
        ⟨.scalar (.fromPointer annealTargetDataLayout mptr), translateTy refTy body.layouts⟩ m =
        .ok ptPlace m := by
      show (do _ : EStateM _ _ _) m = .ok ptPlace m
      simp only [annealValidityHooks, hptLay, Miri.Interpreter.Immediate.toScalar,
        scalar_fromPointer_toPointer_eq, hmis, bind, EStateM.bind, pure, EStateM.pure]
      rfl
    have hdyn : (annealValidityHooks body.layouts).sizeAndAlign refTy ptPlace m =
        .ok (some (ptPlace.layout.layout.size, ptPlace.layout.layout.align.abi)) m := by
      simp only [annealValidityHooks, ptPlace, hsized, ↓reduceIte]; rfl
    obtain ⟨hlive_e, hdead_e⟩ := halloc.local_alloc_sync tf hframes e he
    refine ⟨fun slot hslot hne hoff0 => ?_, fun slot hslot hne hpos_off => ?_, fun hdead => ?_⟩
    · obtain ⟨_, _, hshape⟩ := hlive_e slot hslot hne
      obtain ⟨la, hfind, _, _, hsh⟩ := hshape targetDecl hdecl_t
      have hin : 0 + (translateTy targetDecl.ty body.layouts).layout.size.bytes.toNat ≤
          la.allocation.byteSize.bytes.toNat := by
        rw [hsh.byteSize_eq]; omega
      have hacc_ok := (annealValidityAccessCheck_stack m.machine e.allocId borTag 0
        (translateTy targetDecl.ty body.layouts).layout.size hid (by decide) hbase hsize hpos_nat
        hfit).1 la hfind hin
      have hm : mptr.withOptionalProvenance =
          ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId + UInt64.ofNat 0),
            some (.concrete e.allocId borTag)⟩ := by
        rw [hmptr, hoff0]; rfl
      have hacc : (annealValidityHooks body.layouts).checkPointerAccess refTy ptPlace.mplace.ptr
          ptPlace.layout.layout.size m = .ok (.ok ()) m := by
        simp only [ptPlace]; rw [hm, annealValidityHooks_checkPointerAccess_eq, hacc_ok]
      have hsc_m : Miri.Memory.Scalar.fromMaybePointer (annealValidityHooks body.layouts).target.base
          ptPlace.mplace.ptr = .ok (.fromPointer annealTargetDataLayout mptr) := by
        simp only [ptPlace, hmptr, Miri.Memory.Pointer.withOptionalProvenance,
          Miri.Memory.Scalar.fromMaybePointer, annealValidityHooks, annealRuntimeDataLayout]
        rfl
      have hnn := annealStackBaseAddr_add_ne_zero e.allocId 0 hid (by decide)
      have hnull : (annealValidityHooks body.layouts).scalarMayBeNull refTy
          (.fromPointer annealTargetDataLayout mptr) m = .ok false m := by
        rw [hmptr, hoff0]
        exact fromPointer_scalarMayBeNull_eq body.layouts refTy _ _ m hnn
      have hinh := prim_opsemInhabited_true body.layouts refTy hprim m
      have hal : (annealValidityHooks body.layouts).checkPointerAlignResult refTy ptPlace.mplace.ptr
          ptPlace.layout.layout.align.abi m = .ok (.ok ()) m := by
        simp only [ptPlace, hm, annealValidityHooks]
        have h0 : annealStackBaseAddr e.allocId + UInt64.ofNat 0 = annealStackBaseAddr e.allocId := by
          simp
        rw [h0, annealOffsetMisalignment_stackBase_eq_none e.allocId _ hpow]
        rfl
      have hv_ok := (((hvr.2 _ ptPlace hrd hptr_p hsized hdyn).2 _ hacc hsc_m).2 hnull).2 hinh
      exact hvp.1 initSession m (hv_ok.2 hal) rfl
    · obtain ⟨_, _, hshape⟩ := hlive_e slot hslot hne
      obtain ⟨la, hfind, _, _, hsh⟩ := hshape targetDecl hdecl_t
      have hoob : la.allocation.byteSize.bytes.toNat <
          p.offsetBytes + (translateTy targetDecl.ty body.layouts).layout.size.bytes.toNat := by
        rw [hsh.byteSize_eq]; omega
      have hck := checkAndDerefPtr_live_oob_err (mach := m.machine) e.allocId borTag p.offsetBytes
        (translateTy targetDecl.ty body.layouts).layout.size.bytes.toNat la
        (.dereferenceable "pointer") hid hoff_lt hbase hfind hpos_nat hfit hoob
      have hm : mptr.withOptionalProvenance =
          ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId + UInt64.ofNat p.offsetBytes),
            some (.concrete e.allocId borTag)⟩ := by
        rw [hmptr]; rfl
      have hacc : (annealValidityHooks body.layouts).checkPointerAccess refTy ptPlace.mplace.ptr
          ptPlace.layout.layout.size m =
          .ok (.error (.pointerOutOfBounds e.allocId la.allocation.byteSize (p.offsetBytes : Int)
            ((translateTy targetDecl.ty body.layouts).layout.size.bytes.toNat : Int)
            (.dereferenceable "pointer"))) m := by
        simp only [ptPlace]; rw [hm, annealValidityHooks_checkPointerAccess_eq]
        unfold annealValidityAccessCheck
        split
        · rename_i heq; rw [hsize] at heq; cases heq
        · rename_i n heq; rw [hsize] at heq; cases heq; rw [hck]
      have herr := hvp.2 _ _ ((hvr.2 _ ptPlace hrd hptr_p hsized hdyn).1 _ hacc)
      rw [herr]
      cases mutBool <;> rfl
    · have hfind := hdead_e hdead
      have hck := checkAndDerefPtr_deadAlloc_err (mach := m.machine) e.allocId borTag p.offsetBytes
        ((translateTy targetDecl.ty body.layouts).layout.size.bytes.toNat : Int)
        (.dereferenceable "pointer") hid hoff_lt hbase hfind hpos hfit
      have hm : mptr.withOptionalProvenance =
          ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId + UInt64.ofNat p.offsetBytes),
            some (.concrete e.allocId borTag)⟩ := by
        rw [hmptr]; rfl
      have hacc : (annealValidityHooks body.layouts).checkPointerAccess refTy ptPlace.mplace.ptr
          ptPlace.layout.layout.size m =
          .ok (.error (.allocationLookup (.deadAllocation e.allocId))) m := by
        simp only [ptPlace]; rw [hm, annealValidityHooks_checkPointerAccess_eq]
        unfold annealValidityAccessCheck
        split
        · rename_i heq; rw [hsize] at heq; cases heq
        · rename_i n heq; rw [hsize] at heq; cases heq; rw [hck]
      have herr := hvp.2 _ _ ((hvr.2 _ ptPlace hrd hptr_p hsized hdyn).1 _ hacc)
      rw [herr]
      cases mutBool <;> rfl

/-- **Recursive pointee `ValidityVisitor.visit` simulation (`LM-3.2`)**:
in any `StateRelLM3_2` state (`m.stack.frames = #[tf]`), when a local `refIdx`
of safe-reference type `&T` / `&mut T` holds a live offset-`0` pointer `p`
(`PtrRel allocMap p mptr`, `e ∈ allocMap`, `e.tag = p.tag`,
`get? s.frame.locals e.localIdx = some slot`, `slot ≠ .dead`):

1. **Root `visit` with `RefTracking`**: `ValidityVisitor.visit` from the
   recursive root session (`refTracking := some .empty`) succeeds and pushes the
   pointee key `ptKey` with path `".[deref]"` (`⟨"", #[.deref]⟩`) onto the
   `RefTracking` worklist (`RefTracking.next` pops `(ptKey, ⟨"", #[.deref]⟩)`).
2. **Child `visit` on the tracked pointee `⟨.memory ptKey.mplace, ptKey.layout⟩`**
   (with the child session `flags := ⟨false, true⟩`, `refTracking := none`
   constructed by `ValidityVisitor.validatePlace` at lines 552–555):
   - if the pointee local is `.uninit`, child `ValidityVisitor.visit` raises
     `.error (.undefinedBehavior "read of uninitialized memory") m` (and Anneal's
     `copy *_r` is `.ub` whenever `e.perm ≠ .disabled`);
   - if the pointee local holds an initialized scalar `.init (.scalar sc)` (which
     in `StateRelLM3_2` satisfies `AnnealScalarValid`), child
     `ValidityVisitor.visit` checks `InitMask` and `bool`/`char` bit-pattern
     validity and succeeds with `.ok childSession m`. -/
theorem visit_ref_recursive_pointee_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf])
    {refIdx : Nat} (hlt : refIdx < tf.locals.size)
    {p : ProvenancePtr} {mptr : Miri.Memory.Pointer AnnealProv}
    (hptr : PtrRel allocMap p mptr) (hoff0 : p.offsetBytes = 0)
    {e : AllocMapEntry} (he : e ∈ allocMap) (htag : e.tag = p.tag)
    {targetDecl : LocalDecl} (hdecl_t : get? body.localDecls e.localIdx = some targetDecl)
    (hprim : IsPrimScalarTy targetDecl.ty)
    {refTy : Ty} {refMut : Mutability}
    (hrefTy : refTy.kind = .ref refMut targetDecl.ty.kind)
    (hval : (tf.locals[refIdx]'hlt).value =
      .live (.immediate (.scalar (.fromPointer annealTargetDataLayout mptr))))
    {slot : LocalSlot} (hslot : get? s.frame.locals e.localIdx = some slot)
    (hne_dead : slot ≠ .dead) (fuel : Nat) :
    let rootPlace : Miri.Interpreter.RuntimePlace AnnealProv :=
      ⟨.local 0 refIdx none tf.localsIdentity, translateTy refTy body.layouts⟩
    let rootSession : Miri.Interpreter.ValidityVisitor.Session AnnealProv :=
      { path := ⟨"", #[]⟩, flags := ⟨false, false⟩, ctfeMode := none,
        refTracking := some .empty, dataBytes := none }
    let ptKey : Miri.Interpreter.ValidityVisitor.Key AnnealProv :=
      ⟨⟨mptr.withOptionalProvenance, .none, none⟩, translateTy targetDecl.ty body.layouts⟩
    let childPath : Miri.Memory.ValidationPath := ⟨"", #[.deref]⟩
    let tracked : Miri.Memory.Validity.RefTracking
        (Miri.Interpreter.ValidityVisitor.Key AnnealProv) Miri.Memory.ValidationPath :=
      ⟨#[ptKey], #[(ptKey, childPath)]⟩
    let childSession : Miri.Interpreter.ValidityVisitor.Session AnnealProv :=
      { path := childPath, flags := ⟨false, true⟩, ctfeMode := none,
        refTracking := none, dataBytes := none }
    let childPlace : Miri.Interpreter.RuntimePlace AnnealProv :=
      ⟨.memory ptKey.mplace, ptKey.layout⟩
    Miri.Interpreter.ValidityVisitor.visit (annealValidityHooks body.layouts) refTy (fuel + 1)
        rootSession rootPlace m =
      .ok { rootSession with refTracking := some tracked } m ∧
    tracked.next = some ((ptKey, childPath), ⟨#[ptKey], #[]⟩) ∧
    (slot = .uninit →
      Miri.Interpreter.ValidityVisitor.visit (annealValidityHooks body.layouts) refTy (fuel + 1)
        childSession childPlace m =
        .error (.undefinedBehavior "read of uninitialized memory") m) ∧
    (∀ sc, slot = .init (.scalar sc) →
      AnnealScalarValid targetDecl.ty sc ∧
      Miri.Interpreter.ValidityVisitor.visit (annealValidityHooks body.layouts) refTy (fuel + 1)
        childSession childPlace m = .ok childSession m) := by
  intro rootPlace rootSession ptKey childPath tracked childSession childPlace
  obtain ⟨tf₀, hframes₀, _, _, hfr, _, _, _, _, _, halloc, _⟩ := id hstate
  rw [hframes] at hframes₀; injection hframes₀ with h0; injection h0 with htf; subst htf
  obtain ⟨borTag, hmptr, _⟩ := PtrRel.allocId_of_entry halloc hptr he htag
  obtain ⟨hid, _, hbase⟩ := halloc.base_addr_valid e he
  obtain ⟨hsized, _, _⟩ := hprim.layout_ok (layouts := body.layouts)
  obtain ⟨hsize, hpos, hfit, _, hpow, _⟩ := hprim.size_align_ok body.layouts
  have hpos_nat : 0 < (translateTy targetDecl.ty body.layouts).layout.size.bytes.toNat := by
    exact_mod_cast hpos
  let mutBool : Bool := match refMut with | .mut => true | .not => false
  have hcl_ref : (annealValidityHooks body.layouts).classify refTy
      (translateTy refTy body.layouts).ty m = .ok (.reference mutBool) m := by
    cases refMut <;> (simp only [annealValidityHooks, annealValidityClassify, translateTy,
      encodeTyId, hrefTy, mutBool]; rfl)
  have hptLay : annealValidityPointeeLayout body.layouts refTy =
      some (translateTy targetDecl.ty body.layouts) := by
    have hexact : derefPointeeKindHasExactLayout targetDecl.ty.kind = true := by
      rcases hprim with h | h | ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h] <;> rfl
    unfold annealValidityPointeeLayout
    rw [hrefTy]; dsimp only []; rw [hexact]
    simp only [↓reduceIte, Option.some.injEq]
    exact hprim.translateTy_layoutIdx body.layouts
  have hm0 : mptr.withOptionalProvenance =
      ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId),
        some (.concrete e.allocId borTag)⟩ := by
    rw [hmptr, hoff0]
    simp [Miri.Memory.Pointer.withOptionalProvenance]
  have hmis0 : annealOffsetMisalignment mptr.withOptionalProvenance.offset
      (translateTy targetDecl.ty body.layouts).layout.align.abi = .ok none := by
    rw [hm0]
    exact annealOffsetMisalignment_stackBase_eq_none e.allocId _ hpow
  have hrd_root := annealValidityHooks_readImmediate_local body.layouts refTy hframes hlt hval
    (translateTy refTy body.layouts) .reference
  let ptPlace : Miri.Interpreter.MPlaceTy AnnealProv :=
    ⟨⟨mptr.withOptionalProvenance, .none, none⟩, translateTy targetDecl.ty body.layouts⟩
  have hptr_p : (annealValidityHooks body.layouts).ptrToPlace refTy
      ⟨.scalar (.fromPointer annealTargetDataLayout mptr), translateTy refTy body.layouts⟩ m =
      .ok ptPlace m := by
    show (do _ : EStateM _ _ _) m = .ok ptPlace m
    simp only [annealValidityHooks, hptLay, Miri.Interpreter.Immediate.toScalar,
      scalar_fromPointer_toPointer_eq, hmis0, bind, EStateM.bind, pure, EStateM.pure]
    rfl
  have hdyn : (annealValidityHooks body.layouts).sizeAndAlign refTy ptPlace m =
      .ok (some (ptPlace.layout.layout.size, ptPlace.layout.layout.align.abi)) m := by
    simp only [annealValidityHooks, ptPlace, hsized, ↓reduceIte]; rfl
  obtain ⟨hlive_e, _⟩ := halloc.local_alloc_sync tf hframes e he
  obtain ⟨⟨lay_t, hlay_t⟩, _, hshape⟩ := hlive_e slot hslot hne_dead
  obtain ⟨la, hfind, _, _, hsh⟩ := hshape targetDecl hdecl_t
  have hin : 0 + (translateTy targetDecl.ty body.layouts).layout.size.bytes.toNat ≤
      la.allocation.byteSize.bytes.toNat := by
    rw [hsh.byteSize_eq]; omega
  have hacc_ok := (annealValidityAccessCheck_stack m.machine e.allocId borTag 0
    (translateTy targetDecl.ty body.layouts).layout.size hid (by decide) hbase hsize hpos_nat
    hfit).1 la hfind hin
  have hm : mptr.withOptionalProvenance =
      ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId + UInt64.ofNat 0),
        some (.concrete e.allocId borTag)⟩ := by
    rw [hmptr, hoff0]; rfl
  have hacc : (annealValidityHooks body.layouts).checkPointerAccess refTy ptPlace.mplace.ptr
      ptPlace.layout.layout.size m = .ok (.ok ()) m := by
    simp only [ptPlace]; rw [hm, annealValidityHooks_checkPointerAccess_eq, hacc_ok]
  have hsc_m : Miri.Memory.Scalar.fromMaybePointer (annealValidityHooks body.layouts).target.base
      ptPlace.mplace.ptr = .ok (.fromPointer annealTargetDataLayout mptr) := by
    simp only [ptPlace, hmptr, Miri.Memory.Pointer.withOptionalProvenance,
      Miri.Memory.Scalar.fromMaybePointer, annealValidityHooks, annealRuntimeDataLayout]
    rfl
  have hnn := annealStackBaseAddr_add_ne_zero e.allocId 0 hid (by decide)
  have hnull : (annealValidityHooks body.layouts).scalarMayBeNull refTy
      (.fromPointer annealTargetDataLayout mptr) m = .ok false m := by
    rw [hmptr, hoff0]
    exact fromPointer_scalarMayBeNull_eq body.layouts refTy _ _ m hnn
  have hinh := prim_opsemInhabited_true body.layouts refTy hprim m
  have hal : (annealValidityHooks body.layouts).checkPointerAlignResult refTy ptPlace.mplace.ptr
      ptPlace.layout.layout.align.abi m = .ok (.ok ()) m := by
    simp only [ptPlace, hm0, annealValidityHooks,
      annealOffsetMisalignment_stackBase_eq_none e.allocId _ hpow]
    rfl
  have hvr := visit_reference_cases (annealValidityHooks body.layouts) refTy fuel rootSession
    rootPlace m mutBool hcl_ref rfl rfl rfl
  have hv_root := (((hvr.2 _ ptPlace hrd_root hptr_p hsized hdyn).2 _ hacc hsc_m).2 hnull).2 hinh
  -- Child pointee facts from `FrameRelLM3_2` + `LocalRelLM3_1.indirect_stackAllocPlace_spec`:
  obtain ⟨slot_t', mls_t, _, _, hslot_t', hmls_t, _, hloc_t⟩ := hfr.lookup_local hdecl_t
  rw [hslot] at hslot_t'; injection hslot_t' with hseq; subst hseq
  rcases hloc_t with hloc_t_b | ⟨_, _, _, _, _, _, hty_r, _⟩
  rotate_left
  · exfalso
    rcases hprim with h | h | ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h] at hty_r <;> cases hty_r
  rw [hlay_t] at hmls_t
  have hmls_eq : mls_t = ⟨.live (.indirect (stackAllocPlace e.allocId)), lay_t⟩ :=
    Option.some.inj hmls_t.symm
  have hnz_sz : (translateTy targetDecl.ty body.layouts).layout.size ≠ Miri.ABI.Size.ZERO := by
    intro hz
    rw [hz] at hpos_nat
    exact Nat.lt_irrefl 0 hpos_nat
  obtain ⟨hun_la, hsc_la⟩ := hloc_t_b.indirect_stackAllocPlace_spec hmls_eq hbase hfind
    (halloc.live_key_unique e he) hnz_sz
  have hread_mem_eq := annealReadMemoryPlace_zero_offset_eq hprim hid hbase hfind hsh.byteSize_eq
    (borTag := borTag) (st := m)
  have hfields := prim_layout_fields_eq body.layouts hprim
  have hrd_child : ∀ ev,
      (annealValidityHooks body.layouts).readImmediate refTy childPlace ev m =
        annealReadMemoryPlace ptKey.mplace ptKey.layout m :=
    annealValidityHooks_readImmediate_memory body.layouts refTy hframes ptKey.mplace ptKey.layout
      hfields
  have hv_child := visit_primitive_cases (annealValidityHooks body.layouts) refTy fuel childSession
    childPlace m rfl
  obtain ⟨hcb, hcc, hci, hcu, _⟩ := annealValidityHooks_classify_prim body.layouts refTy
    (ty := targetDecl.ty) m
  have hroot_ok : Miri.Interpreter.ValidityVisitor.visit (annealValidityHooks body.layouts) refTy
      (fuel + 1) rootSession rootPlace m =
      .ok { rootSession with refTracking := some tracked } m := by
    have h1 := hv_root.2 hal
    have htr : Miri.Memory.Validity.RefTracking.empty.track ptKey
        (fun _ => rootSession.path.push .deref) = tracked := by
      simp [Miri.Memory.Validity.RefTracking.track, Miri.Memory.Validity.RefTracking.empty,
        Miri.Memory.ValidationPath.push, rootSession, tracked, childPath]
    simpa [rootSession, ptPlace, ptKey, htr] using h1
  refine ⟨hroot_ok, rfl, fun hs_un => ?_, fun sc hs_sc => ?_⟩
  · obtain ⟨info, hread_err⟩ := hsh.uninit_readScalar_err (hun_la hs_un) false
    have hrm : annealReadMemoryPlace ptKey.mplace ptKey.layout m =
        .error (.undefinedBehavior "read of uninitialized memory") m := by
      simp only [ptKey, hm0]
      rw [hread_mem_eq, hread_err]
    rcases hprim with hk | hk | ⟨it, hk⟩ | ⟨ut, hk⟩
    · exact hv_child.2.1 .boolean (Or.inl rfl) (hcb hk) _ ((hrd_child .boolean).trans hrm)
    · exact hv_child.2.1 .character (Or.inr (Or.inl rfl)) (hcc hk) _
        ((hrd_child .character).trans hrm)
    · exact hv_child.2.1 .integer (Or.inr (Or.inr rfl)) (hci it hk) _
        ((hrd_child .integer).trans hrm)
    · exact hv_child.2.1 .integer (Or.inr (Or.inr rfl)) (hcu ut hk) _
        ((hrd_child .integer).trans hrm)
  · obtain ⟨_, hbool, hchar, msc, hrel, hread_ok⟩ := hsc_la sc hs_sc
    have hav : AnnealScalarValid targetDecl.ty sc :=
      ⟨fun hb => (hbool hb).2, fun hc => (hchar hc).2⟩
    have hval_ty : annealValidateScalarForTyId (translateTy targetDecl.ty body.layouts).ty
        (.fromScalarInt msc) = true :=
      annealValidateScalarForTyId_of_scalarRel hprim hrel (fun hb => hbool hb) (fun hc => hchar hc)
    have hrm : annealReadMemoryPlace ptKey.mplace ptKey.layout m =
        .ok ⟨.scalar (.fromScalarInt msc), ptKey.layout⟩ m := by
      simp only [ptKey, hm0]
      rw [hread_mem_eq, hread_ok]
      dsimp only []
      rw [hval_ty]
      rfl
    refine ⟨hav, ?_⟩
    rcases hprim with hk | hk | ⟨it, hk⟩ | ⟨ut, hk⟩
    · obtain ⟨hsz1, hbits⟩ := hbool hk
      obtain ⟨b, htb⟩ := (fromScalarInt_toBool_ok_iff hrel hsz1).mpr hbits
      exact (hv_child.2.2.2.1 (hcb hk) _ ((hrd_child .boolean).trans hrm)).1 b htb
    · obtain ⟨hsz4, hvc⟩ := hchar hk
      obtain ⟨ch, htc⟩ := (fromScalarInt_toChar_ok_iff hrel hsz4).mpr hvc
      exact (hv_child.2.2.2.2 (hcc hk) _ ((hrd_child .character).trans hrm)).1 ch htc
    · exact hv_child.2.2.1 (hci it hk) _ ((hrd_child .integer).trans hrm)
    · exact hv_child.2.2.1 (hcu ut hk) _ ((hrd_child .integer).trans hrm)

/-- **In-bounds misaligned safe-reference `ValidityVisitor.validatePlace`
simulation (`LM-3.2`)**: in any `StateRelLM3_2` state (`m.stack.frames = #[tf]`),
when `refIdx` holds a safe reference `_r : &(mut) P` (`IsPrimScalarTy P`)
pointing at `p.offsetBytes` inside a live stack allocation `e.localIdx`
(`p.offsetBytes + sizeof(P) ≤ sizeof(allocDecl.ty)`) whose address fails
`P`'s ABI alignment (`annealOffsetMisalignment ... = .ok (some mis)`),
`ValidityVisitor.validatePlace` passes `checkPointerAccess` (in bounds),
`scalarMayBeNull` (non-null), and `opsemInhabited`, and rejects the reference at
`checkPointerAlignResult` with `classifyPointerAlignmentError`. -/
theorem validatePlace_ref_misaligned_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf])
    {refIdx : Nat} (hlt : refIdx < tf.locals.size)
    {pointeeTy : Ty} (hprim : IsPrimScalarTy pointeeTy)
    {refTy : Ty} {refMut : Mutability}
    (hrefTy : refTy.kind = .ref refMut pointeeTy.kind)
    {p : ProvenancePtr} {mptr : Miri.Memory.Pointer AnnealProv} {e : AllocMapEntry}
    (hptr : PtrRel allocMap p mptr) (he : e ∈ allocMap) (htag : e.tag = p.tag)
    {allocDecl : LocalDecl} (hdecl_a : get? body.localDecls e.localIdx = some allocDecl)
    {slot : LocalSlot} (hslot : get? s.frame.locals e.localIdx = some slot)
    (hlive_slot : slot ≠ .dead)
    (hinbounds : p.offsetBytes + (translateTy pointeeTy body.layouts).layout.size.bytes.toNat ≤
      (translateTy allocDecl.ty body.layouts).layout.size.bytes.toNat)
    {mis : Miri.Memory.Misalignment}
    (hmis_err : annealOffsetMisalignment
      (Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId + UInt64.ofNat p.offsetBytes))
      (translateTy pointeeTy body.layouts).layout.align.abi = .ok (some mis))
    (hval : (tf.locals[refIdx]'hlt).value =
      .live (.immediate (.scalar (.fromPointer annealTargetDataLayout mptr))))
    (fuel : Nat) :
    let mutBool : Bool := match refMut with | .mut => true | .not => false
    Miri.Interpreter.ValidityVisitor.validatePlace (annealValidityHooks body.layouts) refTy
      (fuel + 1) ⟨.local 0 refIdx none tf.localsIdentity, translateTy refTy body.layouts⟩
      false false m =
      .error (Miri.Interpreter.ValidityVisitor.classifyPointerAlignmentError
        ⟨"", #[]⟩ (.reference mutBool) mis) m := by
  intro mutBool
  let place : Miri.Interpreter.RuntimePlace AnnealProv :=
    ⟨.local 0 refIdx none tf.localsIdentity, translateTy refTy body.layouts⟩
  let initSession : Miri.Interpreter.ValidityVisitor.Session AnnealProv :=
    { path := ⟨"", #[]⟩, flags := ⟨false, false⟩, ctfeMode := none,
      refTracking := none, dataBytes := none }
  have hcl : (annealValidityHooks body.layouts).classify refTy
      (translateTy refTy body.layouts).ty m = .ok (.reference mutBool) m := by
    cases refMut <;> (simp only [annealValidityHooks, annealValidityClassify, translateTy,
      encodeTyId, hrefTy, mutBool]; rfl)
  have hvr := visit_reference_cases (annealValidityHooks body.layouts) refTy fuel initSession
    place m mutBool hcl rfl rfl rfl
  have hvp := validatePlace_annealValidityHooks_nonrecursive_eq body.layouts refTy (fuel + 1) place m
  have hptLay : annealValidityPointeeLayout body.layouts refTy =
      some (translateTy pointeeTy body.layouts) := by
    have hexact : derefPointeeKindHasExactLayout pointeeTy.kind = true := by
      rcases hprim with h | h | ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h] <;> rfl
    unfold annealValidityPointeeLayout
    rw [hrefTy]
    dsimp only []
    rw [hexact]
    simp only [↓reduceIte, Option.some.injEq]
    exact hprim.translateTy_layoutIdx body.layouts
  obtain ⟨hsized, _, _⟩ := hprim.layout_ok (layouts := body.layouts)
  obtain ⟨hsize, hpos, hfit, _, _, _⟩ := hprim.size_align_ok body.layouts
  have hpos_nat : 0 < (translateTy pointeeTy body.layouts).layout.size.bytes.toNat := by
    exact_mod_cast hpos
  obtain ⟨tf₀, hframes₀, _, _, _, _, _, _, _, _, halloc, _⟩ := id hstate
  rw [hframes] at hframes₀; injection hframes₀ with h0; injection h0 with htf; subst htf
  obtain ⟨borTag, hmptr, hoff_lt⟩ := PtrRel.allocId_of_entry halloc hptr he htag
  obtain ⟨hid, _, hbase⟩ := halloc.base_addr_valid e he
  have hrd := annealValidityHooks_readImmediate_local body.layouts refTy hframes hlt hval
    (translateTy refTy body.layouts) .reference
  have hm : mptr.withOptionalProvenance =
      ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId + UInt64.ofNat p.offsetBytes),
        some (.concrete e.allocId borTag)⟩ := by
    rw [hmptr]; rfl
  have hmis_ptr : annealOffsetMisalignment mptr.withOptionalProvenance.offset
      (translateTy pointeeTy body.layouts).layout.align.abi = .ok (some mis) := by
    rw [hm]; exact hmis_err
  let ptPlace : Miri.Interpreter.MPlaceTy AnnealProv :=
    ⟨⟨mptr.withOptionalProvenance, .none, some mis⟩, translateTy pointeeTy body.layouts⟩
  have hptr_p : (annealValidityHooks body.layouts).ptrToPlace refTy
      ⟨.scalar (.fromPointer annealTargetDataLayout mptr), translateTy refTy body.layouts⟩ m =
      .ok ptPlace m := by
    show (do _ : EStateM _ _ _) m = .ok ptPlace m
    simp only [annealValidityHooks, hptLay, Miri.Interpreter.Immediate.toScalar,
      scalar_fromPointer_toPointer_eq, hmis_ptr, bind, EStateM.bind, pure, EStateM.pure]
    rfl
  have hdyn : (annealValidityHooks body.layouts).sizeAndAlign refTy ptPlace m =
      .ok (some (ptPlace.layout.layout.size, ptPlace.layout.layout.align.abi)) m := by
    simp only [annealValidityHooks, ptPlace, hsized, ↓reduceIte]; rfl
  obtain ⟨hlive_e, _⟩ := halloc.local_alloc_sync tf hframes e he
  obtain ⟨_, _, hshape⟩ := hlive_e slot hslot hlive_slot
  obtain ⟨la, hfind, _, _, hsh⟩ := hshape allocDecl hdecl_a
  have hin : p.offsetBytes + (translateTy pointeeTy body.layouts).layout.size.bytes.toNat ≤
      la.allocation.byteSize.bytes.toNat := by
    rw [hsh.byteSize_eq]; exact hinbounds
  have hacc_ok := (annealValidityAccessCheck_stack m.machine e.allocId borTag p.offsetBytes
    (translateTy pointeeTy body.layouts).layout.size hid hoff_lt hbase hsize hpos_nat hfit).1
    la hfind hin
  have hacc : (annealValidityHooks body.layouts).checkPointerAccess refTy ptPlace.mplace.ptr
      ptPlace.layout.layout.size m = .ok (.ok ()) m := by
    simp only [ptPlace]; rw [hm, annealValidityHooks_checkPointerAccess_eq, hacc_ok]
  have hsc_m : Miri.Memory.Scalar.fromMaybePointer (annealValidityHooks body.layouts).target.base
      ptPlace.mplace.ptr = .ok (.fromPointer annealTargetDataLayout mptr) := by
    simp only [ptPlace, hmptr, Miri.Memory.Pointer.withOptionalProvenance,
      Miri.Memory.Scalar.fromMaybePointer, annealValidityHooks, annealRuntimeDataLayout]
    rfl
  have hnn := annealStackBaseAddr_add_ne_zero e.allocId p.offsetBytes hid hoff_lt
  have hnull : (annealValidityHooks body.layouts).scalarMayBeNull refTy
      (.fromPointer annealTargetDataLayout mptr) m = .ok false m := by
    rw [hmptr]
    exact fromPointer_scalarMayBeNull_eq body.layouts refTy _ _ m hnn
  have hinh := prim_opsemInhabited_true body.layouts refTy hprim m
  have hal : (annealValidityHooks body.layouts).checkPointerAlignResult refTy ptPlace.mplace.ptr
      ptPlace.layout.layout.align.abi m = .ok (.error mis) m := by
    simp only [ptPlace, hm, annealValidityHooks, hmis_err]; rfl
  have hv_ok := (((hvr.2 _ ptPlace hrd hptr_p hsized hdyn).2 _ hacc hsc_m).2 hnull).2 hinh
  exact hvp.2 _ _ (hv_ok.1 mis hal)

private theorem annealOffsetMisalignment_align_one (off : Miri.ABI.Size) :
    annealOffsetMisalignment off Miri.ABI.Align.ONE = .ok none := by
  have his : off.isAligned Miri.ABI.Align.ONE = .ok true := by
    unfold Miri.ABI.Size.isAligned Miri.ABI.Align.bytes Miri.ABI.Align.ONE
    dsimp only [bind, Except.bind, pure, Except.pure]
    change Except.ok ((off.bytes &&& 0) == 0) = Except.ok true
    simp
  unfold annealOffsetMisalignment
  rw [his]

private theorem annealValidityAccessCheck_zero (mach : AnnealMachine)
    (ptr : Miri.Memory.Pointer (Option AnnealProv)) :
    annealValidityAccessCheck mach ptr Miri.ABI.Size.ZERO = .ok () := by
  have hsz : Miri.Memory.sizeAsI64 Miri.ABI.Size.ZERO = .ok 0 := rfl
  unfold annealValidityAccessCheck
  rw [hsz]
  dsimp only []
  rw [Miri.Memory.zero_sized_check_skips_resolution]

/-- **Zero-sized `&()` / `&mut ()` `ValidityVisitor.validatePlace` simulation
(`LM-3.2`)**: for a safe reference to unit `()` (`refTy.kind = .ref refMut (.tuple .nil)`):
1. **Null integer scalar (`sc.bits = 0`)**: `checkPointerAccess` skips resolution on
   `sizeof(()) = 0`, and `scalarMayBeNull` rejects the null ZST reference with
   `"validation: null or maybe-null safe pointer"`.
2. **Non-null integer scalar (`sc.bits ≠ 0`, `sc.bits < 2 ^ 64`, e.g. `NonNull::<()>::dangling().as_ref()`)**:
   accepted (`.ok () m`) without provenance or a backing allocation, because a
   zero-sized access requires `0` dereferenceable bytes and `align(()) = 1`.
3. **Any stack pointer `p` (`PtrRel allocMap p mptr`, `e ∈ allocMap`, even after `StorageDead(e.localIdx)`)**:
   accepted (`.ok () m`), because `annealStackBaseAddr e.allocId + p.offsetBytes ≠ 0`
   and `sizeof(()) = 0`. -/
theorem validatePlace_ref_unit_zst_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf])
    {refIdx : Nat} (hlt : refIdx < tf.locals.size)
    {refTy : Ty} {refMut : Mutability}
    (hrefTy : refTy.kind = .ref refMut (.tuple .nil))
    (fuel : Nat) :
    let place : Miri.Interpreter.RuntimePlace AnnealProv :=
      ⟨.local 0 refIdx none tf.localsIdentity, translateTy refTy body.layouts⟩
    (∀ {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt},
      ScalarRel sc msc → sc.sizeBytes = 8 → sc.bits < 2 ^ 64 →
      (tf.locals[refIdx]'hlt).value = .live (.immediate (.scalar (.fromScalarInt msc))) →
      (sc.bits = 0 →
        Miri.Interpreter.ValidityVisitor.validatePlace (annealValidityHooks body.layouts) refTy
          (fuel + 1) place false false m =
          .error (.undefinedBehavior "validation: null or maybe-null safe pointer") m) ∧
      (sc.bits ≠ 0 →
        Miri.Interpreter.ValidityVisitor.validatePlace (annealValidityHooks body.layouts) refTy
          (fuel + 1) place false false m = .ok () m)) ∧
    (∀ {p : ProvenancePtr} {mptr : Miri.Memory.Pointer AnnealProv} {e : AllocMapEntry},
      PtrRel allocMap p mptr → e ∈ allocMap → e.tag = p.tag →
      (tf.locals[refIdx]'hlt).value =
        .live (.immediate (.scalar (.fromPointer annealTargetDataLayout mptr))) →
      Miri.Interpreter.ValidityVisitor.validatePlace (annealValidityHooks body.layouts) refTy
        (fuel + 1) place false false m = .ok () m) := by
  intro place
  let initSession : Miri.Interpreter.ValidityVisitor.Session AnnealProv :=
    { path := ⟨"", #[]⟩, flags := ⟨false, false⟩, ctfeMode := none,
      refTracking := none, dataBytes := none }
  let mutBool : Bool := match refMut with | .mut => true | .not => false
  let unitLay : Miri.Interpreter.LocalLayout :=
    translateTy { kind := .tuple .nil, layoutIdx := 0 } body.layouts
  have hcl : (annealValidityHooks body.layouts).classify refTy
      (translateTy refTy body.layouts).ty m = .ok (.reference mutBool) m := by
    cases refMut <;> (simp only [annealValidityHooks, annealValidityClassify, translateTy,
      encodeTyId, hrefTy, mutBool]; rfl)
  have hvr := visit_reference_cases (annealValidityHooks body.layouts) refTy fuel initSession
    place m mutBool hcl rfl rfl rfl
  have hvp := validatePlace_annealValidityHooks_nonrecursive_eq body.layouts refTy (fuel + 1) place m
  have hptLay : annealValidityPointeeLayout body.layouts refTy = some unitLay := by
    unfold annealValidityPointeeLayout
    rw [hrefTy]; rfl
  have hsized : unitLay.layout.isSized = true := rfl
  have hinh : (annealValidityHooks body.layouts).opsemInhabited refTy unitLay.ty m = .ok true m :=
    rfl
  have hunitAlign : unitLay.layout.align.abi = Miri.ABI.Align.ONE := rfl
  have hunitSize : unitLay.layout.size = Miri.ABI.Size.ZERO := rfl
  refine ⟨fun {sc msc} hrel hsz8 hlt64 hval => ?_, fun {p mptr e} hptr he htag hval => ?_⟩
  · have hrd := annealValidityHooks_readImmediate_local body.layouts refTy hframes hlt hval
      (translateTy refTy body.layouts) .reference
    have hmis : annealOffsetMisalignment
        (Miri.Memory.Pointer.withoutProvenance (Prov := AnnealProv) (UInt64.ofNat sc.bits)).offset
        unitLay.layout.align.abi = .ok none := by
      rw [hunitAlign]
      exact annealOffsetMisalignment_align_one _
    let ptPlace : Miri.Interpreter.MPlaceTy AnnealProv :=
      ⟨⟨Miri.Memory.Pointer.withoutProvenance (UInt64.ofNat sc.bits), .none, none⟩, unitLay⟩
    have hptr_p : (annealValidityHooks body.layouts).ptrToPlace refTy
        ⟨.scalar (.fromScalarInt msc), translateTy refTy body.layouts⟩ m = .ok ptPlace m := by
      show (do _ : EStateM _ _ _) m = .ok ptPlace m
      simp only [annealValidityHooks, hptLay, Miri.Interpreter.Immediate.toScalar,
        scalar_fromScalarInt_toPointer_eq hrel hsz8, hmis, bind, EStateM.bind, pure, EStateM.pure]
      rfl
    have hdyn : (annealValidityHooks body.layouts).sizeAndAlign refTy ptPlace m =
        .ok (some (ptPlace.layout.layout.size, ptPlace.layout.layout.align.abi)) m := rfl
    have hacc : (annealValidityHooks body.layouts).checkPointerAccess refTy ptPlace.mplace.ptr
        ptPlace.layout.layout.size m = .ok (.ok ()) m := by
      simp only [ptPlace]
      rw [annealValidityHooks_checkPointerAccess_eq, hunitSize, annealValidityAccessCheck_zero]
    have hsc_m : Miri.Memory.Scalar.fromMaybePointer (annealValidityHooks body.layouts).target.base
        ptPlace.mplace.ptr = .ok (.fromScalarInt (.ofUInt64 (UInt64.ofNat sc.bits))) := by
      with_unfolding_all
        change ((do
            let scalar ← (Miri.Memory.ScalarInt.tryFromUInt
              (BitVec.ofNat 128 (UInt64.ofNat sc.bits).toNat)
              (Miri.ABI.Size.ofBytes 8)).mapError (fun e => Miri.Memory.ScalarError.scalarInt e)
            match scalar with
            | some scalar => pure (.fromScalarInt scalar)
            | none => throw (.pointerOffsetDoesNotFit
                (Miri.ABI.Size.ofBytes (UInt64.ofNat sc.bits))
                (Miri.ABI.Size.ofBytes 8))) :
            Except Miri.Memory.ScalarError (Miri.Memory.Scalar AnnealProv)) =
          .ok (.fromScalarInt (.ofUInt64 (UInt64.ofNat sc.bits)))
        rw [tryFromUInt_8_of_u64]
        rfl
    have hal : (annealValidityHooks body.layouts).checkPointerAlignResult refTy ptPlace.mplace.ptr
        ptPlace.layout.layout.align.abi m = .ok (.ok ()) m := by
      simp only [ptPlace, annealValidityHooks, hmis]; rfl
    refine ⟨fun h0 => ?_, fun hne => ?_⟩
    · have hnull : (annealValidityHooks body.layouts).scalarMayBeNull refTy
          (.fromScalarInt (.ofUInt64 (UInt64.ofNat sc.bits))) m = .ok true m := by
        rw [h0]
        with_unfolding_all rfl
      have herr := ((hvr.2 _ ptPlace hrd hptr_p hsized hdyn).2 _ hacc hsc_m).1 hnull
      rw [hvp.2 _ _ herr]
      cases mutBool <;> rfl
    · have hnull : (annealValidityHooks body.layouts).scalarMayBeNull refTy
          (.fromScalarInt (.ofUInt64 (UInt64.ofNat sc.bits))) m = .ok false m := by
        have hne_bv : (BitVec.ofNat 128 sc.bits == 0) = false := by
          cases h : (BitVec.ofNat 128 sc.bits == 0) with
          | false => rfl
          | true =>
            have heq := congrArg BitVec.toNat (beq_iff_eq.mp h)
            have hlt128 : sc.bits < 2 ^ 128 := by omega
            simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt128] at heq
            exact absurd heq hne
        have hu64 : (UInt64.ofNat sc.bits).toNat = sc.bits := Nat.mod_eq_of_lt hlt64
        show EStateM.Result.ok ((Miri.Memory.ScalarInt.ofUInt64 (UInt64.ofNat sc.bits)).isNull) m =
          .ok false m
        with_unfolding_all
          show EStateM.Result.ok (BitVec.ofNat 128 (UInt64.ofNat sc.bits).toNat == 0) m = .ok false m
          rw [hu64, hne_bv]
      have hv_ok := (((hvr.2 _ ptPlace hrd hptr_p hsized hdyn).2 _ hacc hsc_m).2 hnull).2 hinh
      exact hvp.1 initSession m (hv_ok.2 hal) rfl
  · obtain ⟨tf₀, hframes₀, _, _, _, _, _, _, _, _, halloc, _⟩ := id hstate
    rw [hframes] at hframes₀; injection hframes₀ with h0; injection h0 with htf; subst htf
    obtain ⟨borTag, hmptr, hoff_lt⟩ := PtrRel.allocId_of_entry halloc hptr he htag
    obtain ⟨hid, _, _⟩ := halloc.base_addr_valid e he
    have hrd := annealValidityHooks_readImmediate_local body.layouts refTy hframes hlt hval
      (translateTy refTy body.layouts) .reference
    have hmis : annealOffsetMisalignment mptr.withOptionalProvenance.offset
        unitLay.layout.align.abi = .ok none := by
      rw [hunitAlign]
      exact annealOffsetMisalignment_align_one _
    let ptPlace : Miri.Interpreter.MPlaceTy AnnealProv :=
      ⟨⟨mptr.withOptionalProvenance, .none, none⟩, unitLay⟩
    have hptr_p : (annealValidityHooks body.layouts).ptrToPlace refTy
        ⟨.scalar (.fromPointer annealTargetDataLayout mptr), translateTy refTy body.layouts⟩ m =
        .ok ptPlace m := by
      show (do _ : EStateM _ _ _) m = .ok ptPlace m
      simp only [annealValidityHooks, hptLay, Miri.Interpreter.Immediate.toScalar,
        scalar_fromPointer_toPointer_eq, hmis, bind, EStateM.bind, pure, EStateM.pure]
      rfl
    have hdyn : (annealValidityHooks body.layouts).sizeAndAlign refTy ptPlace m =
        .ok (some (ptPlace.layout.layout.size, ptPlace.layout.layout.align.abi)) m := rfl
    have hacc : (annealValidityHooks body.layouts).checkPointerAccess refTy ptPlace.mplace.ptr
        ptPlace.layout.layout.size m = .ok (.ok ()) m := by
      simp only [ptPlace]
      rw [annealValidityHooks_checkPointerAccess_eq, hunitSize, annealValidityAccessCheck_zero]
    have hsc_m : Miri.Memory.Scalar.fromMaybePointer (annealValidityHooks body.layouts).target.base
        ptPlace.mplace.ptr = .ok (.fromPointer annealTargetDataLayout mptr) := by
      simp only [ptPlace, hmptr, Miri.Memory.Pointer.withOptionalProvenance,
        Miri.Memory.Scalar.fromMaybePointer, annealValidityHooks, annealRuntimeDataLayout]
      rfl
    have hnn := annealStackBaseAddr_add_ne_zero e.allocId p.offsetBytes hid hoff_lt
    have hnull : (annealValidityHooks body.layouts).scalarMayBeNull refTy
        (.fromPointer annealTargetDataLayout mptr) m = .ok false m := by
      rw [hmptr]
      exact fromPointer_scalarMayBeNull_eq body.layouts refTy _ _ m hnn
    have hal : (annealValidityHooks body.layouts).checkPointerAlignResult refTy ptPlace.mplace.ptr
        ptPlace.layout.layout.align.abi m = .ok (.ok ()) m := by
      simp only [ptPlace, annealValidityHooks, hmis]; rfl
    have hv_ok := (((hvr.2 _ ptPlace hrd hptr_p hsized hdyn).2 _ hacc hsc_m).2 hnull).2 hinh
    exact hvp.1 initSession m (hv_ok.2 hal) rfl

/-! ## 5. Uninhabited Safe-Reference (`&!`), Enum Discriminant, and Tree-Reborrow Relations -/

/-- **Uninhabited `&!` / `&mut !` `ValidityVisitor.validatePlace` simulation
(`LM-3.2`)**: for a safe reference to `!` (`refTy.kind = .ref refMut .never`):
1. **Dead local (`.dead`)**: rejected with `"validation of a dead local"`.
2. **Uninitialized local (`.uninit`)**: rejected with
   `"read of uninitialized local"`.
3. **Null integer scalar (`sc.bits = 0`)**: `checkPointerAccess` skips
   resolution on `sizeof(!) = 0`, and `scalarMayBeNull` rejects the null
   reference with `"validation: null or maybe-null safe pointer"`.
4. **Non-null integer scalar (`sc.bits ≠ 0`, `sc.bits < 2 ^ 64`)**: passes
   `checkPointerAccess` and `scalarMayBeNull`, and `opsemInhabited` (`tyId = 50`)
   rejects the reference with `"validation: safe pointer to uninhabited type"`.
5. **Any stack pointer `p` (`PtrRel allocMap p mptr`, `e ∈ allocMap`)**:
   rejected by `opsemInhabited` with
   `"validation: safe pointer to uninhabited type"`. -/
theorem validatePlace_ref_never_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf])
    {refIdx : Nat} (hlt : refIdx < tf.locals.size)
    {refTy : Ty} {refMut : Mutability}
    (hrefTy : refTy.kind = .ref refMut .never)
    (fuel : Nat) :
    let place : Miri.Interpreter.RuntimePlace AnnealProv :=
      ⟨.local 0 refIdx none tf.localsIdentity, translateTy refTy body.layouts⟩
    ((tf.locals[refIdx]'hlt).value = .dead →
      Miri.Interpreter.ValidityVisitor.validatePlace
        (annealValidityHooks body.layouts) refTy (fuel + 1) place false false m =
        .error (.undefinedBehavior "validation of a dead local") m) ∧
    ((tf.locals[refIdx]'hlt).value = .live (.immediate .uninit) →
      Miri.Interpreter.ValidityVisitor.validatePlace
        (annealValidityHooks body.layouts) refTy (fuel + 1) place false false m =
        .error (.undefinedBehavior "read of uninitialized local") m) ∧
    (∀ {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt},
      ScalarRel sc msc → sc.sizeBytes = 8 → sc.bits < 2 ^ 64 →
      (tf.locals[refIdx]'hlt).value =
        .live (.immediate (.scalar (.fromScalarInt msc))) →
      (sc.bits = 0 →
        Miri.Interpreter.ValidityVisitor.validatePlace
          (annealValidityHooks body.layouts) refTy (fuel + 1) place false false m =
          .error (.undefinedBehavior
            "validation: null or maybe-null safe pointer") m) ∧
      (sc.bits ≠ 0 →
        Miri.Interpreter.ValidityVisitor.validatePlace
          (annealValidityHooks body.layouts) refTy (fuel + 1) place false false m =
          .error (.undefinedBehavior
            "validation: safe pointer to uninhabited type") m)) ∧
    (∀ {p : ProvenancePtr} {mptr : Miri.Memory.Pointer AnnealProv}
        {e : AllocMapEntry},
      PtrRel allocMap p mptr → e ∈ allocMap → e.tag = p.tag →
      (tf.locals[refIdx]'hlt).value =
        .live (.immediate (.scalar (.fromPointer annealTargetDataLayout mptr))) →
      Miri.Interpreter.ValidityVisitor.validatePlace
        (annealValidityHooks body.layouts) refTy (fuel + 1) place false false m =
        .error (.undefinedBehavior
          "validation: safe pointer to uninhabited type") m) := by
  intro place
  let initSession : Miri.Interpreter.ValidityVisitor.Session AnnealProv :=
    { path := ⟨"", #[]⟩, flags := ⟨false, false⟩, ctfeMode := none,
      refTracking := none, dataBytes := none }
  let mutBool : Bool := match refMut with | .mut => true | .not => false
  let neverLay : Miri.Interpreter.LocalLayout :=
    translateTy { kind := .never, layoutIdx := 0 } body.layouts
  have hcl : (annealValidityHooks body.layouts).classify refTy
      (translateTy refTy body.layouts).ty m = .ok (.reference mutBool) m := by
    cases refMut <;> (simp only [annealValidityHooks, annealValidityClassify,
      translateTy, encodeTyId, hrefTy, mutBool]; rfl)
  have hvr := visit_reference_cases (annealValidityHooks body.layouts) refTy fuel
    initSession place m mutBool hcl rfl rfl rfl
  have hvp := validatePlace_annealValidityHooks_nonrecursive_eq body.layouts refTy
    (fuel + 1) place m
  have hptLay : annealValidityPointeeLayout body.layouts refTy = some neverLay := by
    unfold annealValidityPointeeLayout
    rw [hrefTy]; rfl
  have hsized : neverLay.layout.isSized = true := rfl
  have huninh : (annealValidityHooks body.layouts).opsemInhabited refTy
      neverLay.ty m = .ok false m := rfl
  have hneverAlign : neverLay.layout.align.abi = Miri.ABI.Align.ONE := rfl
  have hneverSize : neverLay.layout.size = Miri.ABI.Size.ZERO := rfl
  refine ⟨fun hdead => ?_, fun hun => ?_,
    fun {sc msc} hrel hsz8 hlt64 hval => ?_,
    fun {p mptr e} hptr he htag hval => ?_⟩
  · have hrd := annealValidityHooks_readImmediate_dead_local body.layouts refTy
      hframes hlt hdead (translateTy refTy body.layouts) .reference
    exact hvp.2 _ _ (hvr.1 _ hrd)
  · have hrd := annealValidityHooks_readImmediate_uninit_local body.layouts refTy
      hframes hlt hun (translateTy refTy body.layouts) .reference
    exact hvp.2 _ _ (hvr.1 _ hrd)
  · have hrd := annealValidityHooks_readImmediate_local body.layouts refTy hframes
      hlt hval (translateTy refTy body.layouts) .reference
    have hmis : annealOffsetMisalignment
        (Miri.Memory.Pointer.withoutProvenance (Prov := AnnealProv)
          (UInt64.ofNat sc.bits)).offset
        neverLay.layout.align.abi = .ok none := by
      rw [hneverAlign]
      exact annealOffsetMisalignment_align_one _
    let ptPlace : Miri.Interpreter.MPlaceTy AnnealProv :=
      ⟨⟨Miri.Memory.Pointer.withoutProvenance (UInt64.ofNat sc.bits), .none, none⟩,
        neverLay⟩
    have hptr_p : (annealValidityHooks body.layouts).ptrToPlace refTy
        ⟨.scalar (.fromScalarInt msc), translateTy refTy body.layouts⟩ m =
        .ok ptPlace m := by
      show (do _ : EStateM _ _ _) m = .ok ptPlace m
      simp only [annealValidityHooks, hptLay, Miri.Interpreter.Immediate.toScalar,
        scalar_fromScalarInt_toPointer_eq hrel hsz8, hmis, bind, EStateM.bind,
        pure, EStateM.pure]
      rfl
    have hdyn : (annealValidityHooks body.layouts).sizeAndAlign refTy ptPlace m =
        .ok (some (ptPlace.layout.layout.size, ptPlace.layout.layout.align.abi)) m :=
      rfl
    have hacc : (annealValidityHooks body.layouts).checkPointerAccess refTy
        ptPlace.mplace.ptr ptPlace.layout.layout.size m = .ok (.ok ()) m := by
      simp only [ptPlace]
      rw [annealValidityHooks_checkPointerAccess_eq, hneverSize,
        annealValidityAccessCheck_zero]
    have hsc_m : Miri.Memory.Scalar.fromMaybePointer
        (annealValidityHooks body.layouts).target.base ptPlace.mplace.ptr =
        .ok (.fromScalarInt (.ofUInt64 (UInt64.ofNat sc.bits))) := by
      with_unfolding_all
        change ((do
            let scalar ← (Miri.Memory.ScalarInt.tryFromUInt
              (BitVec.ofNat 128 (UInt64.ofNat sc.bits).toNat)
              (Miri.ABI.Size.ofBytes 8)).mapError
              (fun e => Miri.Memory.ScalarError.scalarInt e)
            match scalar with
            | some scalar => pure (.fromScalarInt scalar)
            | none => throw (.pointerOffsetDoesNotFit
                (Miri.ABI.Size.ofBytes (UInt64.ofNat sc.bits))
                (Miri.ABI.Size.ofBytes 8))) :
            Except Miri.Memory.ScalarError (Miri.Memory.Scalar AnnealProv)) =
          .ok (.fromScalarInt (.ofUInt64 (UInt64.ofNat sc.bits)))
        rw [tryFromUInt_8_of_u64]
        rfl
    refine ⟨fun h0 => ?_, fun hne => ?_⟩
    · have hnull : (annealValidityHooks body.layouts).scalarMayBeNull refTy
          (.fromScalarInt (.ofUInt64 (UInt64.ofNat sc.bits))) m = .ok true m := by
        rw [h0]
        with_unfolding_all rfl
      have herr := ((hvr.2 _ ptPlace hrd hptr_p hsized hdyn).2 _ hacc hsc_m).1 hnull
      rw [hvp.2 _ _ herr]
      rfl
    · have hnull : (annealValidityHooks body.layouts).scalarMayBeNull refTy
          (.fromScalarInt (.ofUInt64 (UInt64.ofNat sc.bits))) m = .ok false m := by
        have hne_bv : (BitVec.ofNat 128 sc.bits == 0) = false := by
          cases h : (BitVec.ofNat 128 sc.bits == 0) with
          | false => rfl
          | true =>
            have heq := congrArg BitVec.toNat (beq_iff_eq.mp h)
            have hlt128 : sc.bits < 2 ^ 128 := by omega
            simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt128] at heq
            exact absurd heq hne
        have hu64 : (UInt64.ofNat sc.bits).toNat = sc.bits := Nat.mod_eq_of_lt hlt64
        show EStateM.Result.ok
          ((Miri.Memory.ScalarInt.ofUInt64 (UInt64.ofNat sc.bits)).isNull) m =
          .ok false m
        with_unfolding_all
          show EStateM.Result.ok
            (BitVec.ofNat 128 (UInt64.ofNat sc.bits).toNat == 0) m = .ok false m
          rw [hu64, hne_bv]
      have herr := (((hvr.2 _ ptPlace hrd hptr_p hsized hdyn).2 _ hacc hsc_m).2
        hnull).1 huninh
      rw [hvp.2 _ _ herr]
      rfl
  · obtain ⟨tf₀, hframes₀, _, _, _, _, _, _, _, _, halloc, _⟩ := id hstate
    rw [hframes] at hframes₀; injection hframes₀ with h0
    injection h0 with htf; subst htf
    obtain ⟨borTag, hmptr, hoff_lt⟩ := PtrRel.allocId_of_entry halloc hptr he htag
    obtain ⟨hid, _, _⟩ := halloc.base_addr_valid e he
    have hrd := annealValidityHooks_readImmediate_local body.layouts refTy hframes
      hlt hval (translateTy refTy body.layouts) .reference
    have hmis : annealOffsetMisalignment mptr.withOptionalProvenance.offset
        neverLay.layout.align.abi = .ok none := by
      rw [hneverAlign]
      exact annealOffsetMisalignment_align_one _
    let ptPlace : Miri.Interpreter.MPlaceTy AnnealProv :=
      ⟨⟨mptr.withOptionalProvenance, .none, none⟩, neverLay⟩
    have hptr_p : (annealValidityHooks body.layouts).ptrToPlace refTy
        ⟨.scalar (.fromPointer annealTargetDataLayout mptr),
          translateTy refTy body.layouts⟩ m = .ok ptPlace m := by
      show (do _ : EStateM _ _ _) m = .ok ptPlace m
      simp only [annealValidityHooks, hptLay, Miri.Interpreter.Immediate.toScalar,
        scalar_fromPointer_toPointer_eq, hmis, bind, EStateM.bind, pure, EStateM.pure]
      rfl
    have hdyn : (annealValidityHooks body.layouts).sizeAndAlign refTy ptPlace m =
        .ok (some (ptPlace.layout.layout.size, ptPlace.layout.layout.align.abi)) m :=
      rfl
    have hacc : (annealValidityHooks body.layouts).checkPointerAccess refTy
        ptPlace.mplace.ptr ptPlace.layout.layout.size m = .ok (.ok ()) m := by
      simp only [ptPlace]
      rw [annealValidityHooks_checkPointerAccess_eq, hneverSize,
        annealValidityAccessCheck_zero]
    have hsc_m : Miri.Memory.Scalar.fromMaybePointer
        (annealValidityHooks body.layouts).target.base ptPlace.mplace.ptr =
        .ok (.fromPointer annealTargetDataLayout mptr) := by
      simp only [ptPlace, hmptr, Miri.Memory.Pointer.withOptionalProvenance,
        Miri.Memory.Scalar.fromMaybePointer, annealValidityHooks,
        annealRuntimeDataLayout]
      rfl
    have hnn := annealStackBaseAddr_add_ne_zero e.allocId p.offsetBytes hid hoff_lt
    have hnull : (annealValidityHooks body.layouts).scalarMayBeNull refTy
        (.fromPointer annealTargetDataLayout mptr) m = .ok false m := by
      rw [hmptr]
      exact fromPointer_scalarMayBeNull_eq body.layouts refTy _ _ m hnn
    have herr := (((hvr.2 _ ptPlace hrd hptr_p hsized hdyn).2 _ hacc hsc_m).2
      hnull).1 huninh
    rw [hvp.2 _ _ herr]
    rfl

/-- **No valid immediate `&!` / `&mut !` local exists in `StateRelLM3_2`
(`LM-3.2`)**: in any `StateRelLM3_2` state, EVERY non-memory-backed local
`refIdx` (`IsImmediateFrameLocal tf refIdx`) declared with safe-reference type
`&!` or `&mut !` (`decl.ty.kind = .ref refMut .never`) fails
`ValidityVisitor.validatePlace` with `StepError.undefinedBehavior`, regardless
of whether the local is dead, uninitialized, an integer scalar, or a stack
pointer. -/
theorem validatePlace_ref_never_always_ub
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf])
    {refIdx : Nat} {decl : LocalDecl}
    (hdecl : get? body.localDecls refIdx = some decl)
    {refMut : Mutability}
    (hrefTy : decl.ty.kind = .ref refMut .never)
    (himm_loc : IsImmediateFrameLocal tf refIdx)
    (fuel : Nat) :
    ∃ msg,
      Miri.Interpreter.ValidityVisitor.validatePlace
        (annealValidityHooks body.layouts) decl.ty (fuel + 1)
        ⟨.local 0 refIdx none tf.localsIdentity, translateTy decl.ty body.layouts⟩
        false false m =
        .error (.undefinedBehavior msg) m := by
  have hfr := hstate.frame_rel_singleton hframes
  obtain ⟨slot, mls, _, hlt, _, hmls, hmls_eq, hloc⟩ := hfr.lookup_local hdecl
  have hsim := validatePlace_ref_never_simulation hstate hframes hlt hrefTy fuel
  rcases hloc with hloc1 | ⟨p, mptr, cl, _, _, _, _, hptr⟩
  · rcases hloc1 with hb | ⟨_, _, _, _, _, _, hty_r, _⟩
    · rcases hb with ⟨cl, _⟩ | ⟨_, imm, cl, _, himm⟩ | ⟨_, mp, cl, _, _, _⟩
      · exact ⟨_, hsim.1 (by rw [hmls_eq])⟩
      · rcases himm with ⟨_, rfl⟩ | ⟨v, _, himm_rel⟩
        · exact ⟨_, hsim.2.1 (by rw [hmls_eq])⟩
        · cases himm_rel with
          | unit hz =>
            exfalso
            have h8 : (translateTy decl.ty body.layouts).layout.size =
                Miri.ABI.Size.ofBytes 8 := by
              simp [translateTy, hrefTy, pointerLayoutData]
            rw [h8] at hz
            cases hz
          | scalar sc msc hrel hsz _ _ =>
            have h8 : (translateTy decl.ty body.layouts).layout.size =
                Miri.ABI.Size.ofBytes 8 := by
              simp [translateTy, hrefTy, pointerLayoutData]
            rw [h8] at hsz
            have hsz_b : (8 : UInt64) = UInt64.ofNat sc.sizeBytes :=
              congrArg Miri.ABI.Size.bytes hsz
            have hsz8 : sc.sizeBytes = 8 := by
              rcases hrel.validBytes with h | h | h | h | h <;>
                (rw [h] at hsz_b; first | exact h | cases hsz_b)
            have hcan := hrel.canonical
            rw [hsz8] at hcan
            have hlt64 : sc.bits < 2 ^ 64 := by
              have : scalarModulus 8 = 2 ^ 64 := by decide
              omega
            have hval : (tf.locals[refIdx]'hlt).value =
                .live (.immediate (.scalar (.fromScalarInt msc))) := by
              rw [hmls_eq]
            by_cases h0 : sc.bits = 0
            · exact ⟨_, (hsim.2.2.1 hrel hsz8 hlt64 hval).1 h0⟩
            · exact ⟨_, (hsim.2.2.1 hrel hsz8 hlt64 hval).2 h0⟩
          | scalarPair _ _ _ _ _ _ hagg _ =>
            exfalso
            rcases hagg with ⟨_, ht⟩ | ⟨_, _, ht⟩ <;> (rw [hrefTy] at ht; cases ht)
      · exact False.elim (himm_loc ⟨.live (.indirect mp), cl⟩ hmls mp rfl)
    · rw [hrefTy] at hty_r; cases hty_r
  · obtain ⟨_, _, _, _, _, _, e, he, htag, _⟩ := id hptr
    exact ⟨_, hsim.2.2.2 hptr he htag (by rw [hmls_eq])⟩

/-! ### Zero-Variant and Multi-Variant Enum Discriminant Validation (`LM-3.2`) -/

private theorem annealValidityPlaceOperand_local_zero_offset
    {m : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf]) {idx : Nat}
    (lay : Miri.Interpreter.LocalLayout) :
    annealValidityPlaceOperand
        ⟨.local 0 idx (some Miri.ABI.Size.ZERO) tf.localsIdentity, lay⟩ m =
      annealValidityPlaceOperand ⟨.local 0 idx none tf.localsIdentity, lay⟩ m := by
  unfold annealValidityPlaceOperand
  simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind,
    stack_currentFrame?_singleton m.stack tf hframes, BEq.rfl, ↓reduceIte]

private theorem translateWrappingRange_contains_eq
    (r : Layout.WrappingRange) (v : Nat)
    (hs : r.start < 2 ^ 128) (he : r.end_ < 2 ^ 128) (hv : v < 2 ^ 128) :
    (translateWrappingRange r).contains (BitVec.ofNat 128 v) =
      wrappingRangeContains r v := by
  have hs_bv : (BitVec.ofNat 128 r.start).toNat = r.start := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hs]
  have he_bv : (BitVec.ofNat 128 r.end_).toNat = r.end_ := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt he]
  have hv_bv : (BitVec.ofNat 128 v).toNat = v := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv]
  have hble_se : Nat.ble r.start r.end_ = decide (r.start ≤ r.end_) := by
    rw [Bool.eq_iff_iff, Nat.ble_eq, decide_eq_true_eq]
  have hble_sv : Nat.ble r.start v = decide (r.start ≤ v) := by
    rw [Bool.eq_iff_iff, Nat.ble_eq, decide_eq_true_eq]
  have hble_ve : Nat.ble v r.end_ = decide (v ≤ r.end_) := by
    rw [Bool.eq_iff_iff, Nat.ble_eq, decide_eq_true_eq]
  unfold translateWrappingRange Miri.ABI.WrappingRange.contains wrappingRangeContains
  simp only [hs_bv, he_bv, hv_bv, hble_se, hble_sv, hble_ve]
  by_cases h : r.start ≤ r.end_ <;> simp [h]

private theorem u64_truncate_lt_u64 (v : Nat) (hv : v < 2 ^ 64) :
    (Miri.ABI.Size.ofBytes 8).truncate (BitVec.ofNat 128 v) =
      .ok (BitVec.ofNat 128 v) := by
  have hlt128 : v < 2 ^ 128 := by omega
  have htr := size_truncate_translateSizeBytes (sz := 8)
    (by simp [ValidScalarBytes]) (BitVec.ofNat 128 v)
  change (translateSizeBytes 8).truncate (BitVec.ofNat 128 v) = _
  rw [htr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt128, Nat.mod_eq_of_lt hv]

private theorem adt_tyId_bounds {n : Nat} (hn : n < 800) :
    ¬ ((100 + n : Miri.MIR.TyId) < 100) ∧
    (100 ≤ (100 + n : Miri.MIR.TyId) ∧ (100 + n : Miri.MIR.TyId) < 900) := by
  unfold Miri.MIR.TyId
  omega

private theorem forIn'_singleton_estate {ε σ α β : Type}
    (x : α) (b : β) (f : (a : α) → a ∈ #[x] → β → EStateM ε σ (ForInStep β)) :
    forIn' #[x] b f =
      (f x (by simp) b >>= fun step =>
        match step with
        | .done b' => pure b'
        | .yield b' => pure b') := rfl

private theorem estate_bind_assoc {ε σ α β γ : Type}
    (ma : EStateM ε σ α) (kb : α → EStateM ε σ β) (kc : β → EStateM ε σ γ) :
    ((ma >>= kb) >>= kc) = (ma >>= fun a => kb a >>= kc) := by
  funext s; dsimp [Bind.bind, EStateM.bind]; cases ma s <;> rfl

private theorem estate_pure_bind {ε σ α β : Type}
    (a : α) (k : α → EStateM ε σ β) :
    (pure a >>= k : EStateM ε σ β) = k a := rfl

private theorem estate_bind_congr_cont {ε σ α β : Type}
    (ma : EStateM ε σ α) {kb kc : α → EStateM ε σ β}
    (h : ∀ a s', kb a s' = kc a s') (s : σ) :
    (ma >>= kb) s = (ma >>= kc) s := by
  dsimp [Bind.bind, EStateM.bind]
  cases ma s with
  | ok a s' => exact h a s'
  | error e s' => rfl

/-- **Zero-variant enum (`VariantsShape.empty`) `ValidityVisitor.validatePlace`
and `&Void` reference simulation (`LM-3.2`)**:
1. Any place `place` whose layout is a zero-variant enum `enumTy`
   (`enumTy.kind = .adt defPath args`, `enumTy.layoutIdx < 800`,
   `LayoutTable.lookup layouts enumTy.layoutIdx = some tl`,
   `tl.variants = .empty`, `tl.fields = .arbitrary .nil .nil`) is rejected by
   `ValidityVisitor.validatePlace` with
   `"validation: zero-variant enum value"`, matching
   `Bytes.decodeValueFromBytes (dFuel + 1) layouts enumTy bytes = none` on
   every byte sequence `bytes`.
2. Every byte sequence `bytes` fails `decodeValueFromBytes` for `enumTy`. -/
theorem validatePlace_zero_variant_enum_simulation
    (layouts : LayoutTable) {enumTy : Ty} {defPath : String} {args : List RigidTy}
    (hk : enumTy.kind = .adt defPath args)
    (hidx : enumTy.layoutIdx < 800)
    {tl : Layout.TypeLayout}
    (hlook : LayoutTable.lookup layouts enumTy.layoutIdx = some tl)
    (hvar : tl.variants = .empty)
    (hfields : tl.fields = .arbitrary .nil .nil)
    (fuel : Nat) :
    (∀ (place : Miri.Interpreter.RuntimePlace AnnealProv) (m : AnnealStepState),
      place.layout = translateTy enumTy layouts →
      Miri.Interpreter.ValidityVisitor.validatePlace
        (annealValidityHooks layouts) enumTy (fuel + 1) place false false m =
        .error (.undefinedBehavior "validation: zero-variant enum value") m) ∧
    (∀ (dFuel : Nat) (bytes : List AbstractByte),
      decodeValueFromBytes (dFuel + 1) layouts enumTy bytes = none) := by
  obtain ⟨hb_not_lt, hb_in⟩ := adt_tyId_bounds hidx
  refine ⟨fun place m hlay => ?_, fun dFuel bytes => ?_⟩
  · let initSession : Miri.Interpreter.ValidityVisitor.Session AnnealProv :=
      { path := ⟨"", #[]⟩, flags := ⟨false, false⟩, ctfeMode := none,
        refTracking := none, dataBytes := none }
    have hvp := validatePlace_annealValidityHooks_nonrecursive_eq layouts enumTy
      (fuel + 1) place m
    have htyId : place.layout.ty = 100 + enumTy.layoutIdx := by
      rw [hlay]; simp [translateTy, encodeTyId, hk]
    have hcl : (annealValidityHooks layouts).classify enumTy place.layout.ty m =
        .ok (.aggregate false false true) m := by
      simp only [annealValidityHooks, htyId, ite_false_eq hb_not_lt,
        annealValidityClassifyAdt, ite_true_eq hb_in,
        Nat.add_sub_cancel_left, hlook, hvar]
      rfl
    have hfl : place.layout.layout.fields = .Arbitrary #[] #[] := by
      rw [hlay]
      simp [translateTy, hk, hlook, translateTypeLayout, hfields, translateFieldsShape]
    have hvr : place.layout.layout.variants = .Empty := by
      rw [hlay]
      simp [translateTy, hk, hlook, translateTypeLayout, hvar, translateVariantsShape]
    have hv : Miri.Interpreter.ValidityVisitor.visit (annealValidityHooks layouts)
        enumTy (fuel + 1) initSession place m =
        .error (.undefinedBehavior "validation: zero-variant enum value") m := by
      unfold Miri.Interpreter.ValidityVisitor.visit
      rw [estate_bind_ok _ _ _ _ _ hcl]
      refine (estate_bind_ok _ _ _ _ none rfl).trans ?_
      simp only [initSession, hfl, hvr]
      rfl
    exact hvp.2 _ _ hv
  · unfold decodeValueFromBytes
    simp only [hk, hlook, hvar]
    cases (Bool.or tl.isUninhabited (Bool.not (Nat.beq (length bytes) tl.size.bytes))) <;>
      rfl

/-- **Fieldless `u8`-tagged enum discriminant `ValidityVisitor.validatePlace`
vs. `Bytes.decodeValueFromBytes` simulation (`LM-3.2`)**: for a multi-variant
C-like enum `enumTy` (`enumTy.kind = .adt defPath args`,
`enumTy.layoutIdx < 800`, `LayoutTable.lookup layouts enumTy.layoutIdx = some tl`)
with 1-byte `u8` tag scalar `tagSl = .initialized (.int 8 false) validRange`
at field `0` (`tl.size = ⟨1⟩`, `tl.isUninhabited = false`,
`tl.fields = .arbitrary [⟨0⟩] [0]`,
`tl.variants = .multiple tagSl 0 variantShapes`, and every variant in
`variantShapes` fieldless `.arbitrary .nil .nil`):

1. **Dead local (`.dead`)**: `validatePlace` raises undefined behavior
   (`"validation of a dead local"`).
2. **Uninitialized local (`.uninit`)**: `validatePlace` raises undefined
   behavior (`"read of uninitialized local"`), matching
   `decodeValueFromBytes (dFuel + 1) layouts enumTy [.uninit] = none`.
3. **Initialized `u8` discriminant byte (`ScalarRel sc msc`, `sc.sizeBytes = 1`)**:
   - if `wrappingRangeContains validRange sc.bits = false`, `validatePlace`
     raises `.error (.undefinedBehavior "InvalidTag(outside valid range)") m`
     and `decodeValueFromBytes ... [.init (UInt8.ofNat sc.bits) none] = none`;
   - if `wrappingRangeContains validRange sc.bits = true` and
     `variantShapes.length ≤ sc.bits` (undeclared discriminant gap inside
     `validRange`), `validatePlace` raises
     `.error (.undefinedBehavior "InvalidTag(no declared discriminant)") m`
     and `decodeValueFromBytes ... [.init (UInt8.ofNat sc.bits) none] = none`;
   - if `wrappingRangeContains validRange sc.bits = true` and
     `sc.bits < variantShapes.length`, `validatePlace` succeeds (`.ok () m`)
     and `decodeValueFromBytes ... [.init (UInt8.ofNat sc.bits) none] =
     some (.aggregate sc.bits .nil)`. -/
theorem validatePlace_enum_discriminant_simulation
    (layouts : LayoutTable) {enumTy : Ty} {defPath : String} {args : List RigidTy}
    (hk : enumTy.kind = .adt defPath args)
    (hidx : enumTy.layoutIdx < 800)
    {tl : Layout.TypeLayout}
    (hlook : LayoutTable.lookup layouts enumTy.layoutIdx = some tl)
    {validRange : Layout.WrappingRange}
    (hr_start : validRange.start < 2 ^ 128)
    (hr_end : validRange.end_ < 2 ^ 128)
    {variantShapes : List Layout.FieldsShape}
    (hsz1 : tl.size = ⟨1⟩)
    (hinh : tl.isUninhabited = false)
    (hfields : tl.fields = .arbitrary [⟨0⟩] [0])
    (hvars : tl.variants =
      .multiple (.initialized (.int 8 false) validRange) 0 variantShapes)
    (hv_fieldless : ∀ v < variantShapes.length,
      get? variantShapes v = some (.arbitrary .nil .nil))
    (fuel dFuel : Nat)
    {m : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf]) {idx : Nat} (hlt : idx < tf.locals.size) :
    let place : Miri.Interpreter.RuntimePlace AnnealProv :=
      ⟨.local 0 idx none tf.localsIdentity, translateTy enumTy layouts⟩
    ((tf.locals[idx]'hlt).value = .dead →
      Miri.Interpreter.ValidityVisitor.validatePlace
        (annealValidityHooks layouts) enumTy (fuel + 2) place false false m =
        .error (.undefinedBehavior "validation of a dead local") m) ∧
    ((tf.locals[idx]'hlt).value = .live (.immediate .uninit) →
      Miri.Interpreter.ValidityVisitor.validatePlace
        (annealValidityHooks layouts) enumTy (fuel + 2) place false false m =
        .error (.undefinedBehavior "read of uninitialized local") m ∧
      decodeValueFromBytes (dFuel + 1) layouts enumTy [.uninit] = none) ∧
    (∀ {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt},
      ScalarRel sc msc → sc.sizeBytes = 1 →
      (tf.locals[idx]'hlt).value =
        .live (.immediate (.scalar (.fromScalarInt msc))) →
      (wrappingRangeContains validRange sc.bits = false →
        Miri.Interpreter.ValidityVisitor.validatePlace
          (annealValidityHooks layouts) enumTy (fuel + 2) place false false m =
          .error (.undefinedBehavior "InvalidTag(outside valid range)") m ∧
        decodeValueFromBytes (dFuel + 1) layouts enumTy
          [.init (UInt8.ofNat sc.bits) none] = none) ∧
      (wrappingRangeContains validRange sc.bits = true →
        variantShapes.length ≤ sc.bits →
        Miri.Interpreter.ValidityVisitor.validatePlace
          (annealValidityHooks layouts) enumTy (fuel + 2) place false false m =
          .error (.undefinedBehavior "InvalidTag(no declared discriminant)") m ∧
        decodeValueFromBytes (dFuel + 1) layouts enumTy
          [.init (UInt8.ofNat sc.bits) none] = none) ∧
      (wrappingRangeContains validRange sc.bits = true →
        sc.bits < variantShapes.length →
        Miri.Interpreter.ValidityVisitor.validatePlace
          (annealValidityHooks layouts) enumTy (fuel + 2) place false false m =
          .ok () m ∧
        decodeValueFromBytes (dFuel + 1) layouts enumTy
          [.init (UInt8.ofNat sc.bits) none] =
          some (.aggregate sc.bits .nil)) ∧
      (Miri.Interpreter.ValidityVisitor.validatePlace
          (annealValidityHooks layouts) enumTy (fuel + 2) place false false m =
          .ok () m ↔
        ∃ v, decodeValueFromBytes (dFuel + 1) layouts enumTy
          [.init (UInt8.ofNat sc.bits) none] = some v)) := by
  intro place
  obtain ⟨hb_not_lt, hb_in⟩ := adt_tyId_bounds hidx
  let initSession : Miri.Interpreter.ValidityVisitor.Session AnnealProv :=
    { path := ⟨"", #[]⟩, flags := ⟨false, false⟩, ctfeMode := none,
      refTracking := none, dataBytes := none }
  let u8Lay : Miri.Interpreter.LocalLayout :=
    { ty := 20, layout := scalarLayoutData 1 false }
  let tagPlace : Miri.Interpreter.RuntimePlace AnnealProv :=
    ⟨.local 0 idx (some Miri.ABI.Size.ZERO) tf.localsIdentity, u8Lay⟩
  have hvp := validatePlace_annealValidityHooks_nonrecursive_eq layouts enumTy
    (fuel + 2) place m
  have htyId : (translateTy enumTy layouts).ty = 100 + enumTy.layoutIdx := by
    simp [translateTy, encodeTyId, hk]
  have hcl : (annealValidityHooks layouts).classify enumTy
      (translateTy enumTy layouts).ty m =
      .ok (.aggregate false false true) m := by
    simp only [annealValidityHooks, htyId, ite_false_eq hb_not_lt,
      annealValidityClassifyAdt, ite_true_eq hb_in,
      Nat.add_sub_cancel_left, hlook, hvars]
    rfl
  have hinh_hook : (annealValidityHooks layouts).opsemInhabited enumTy
      (translateTy enumTy layouts).ty m = .ok true m := by
    simp only [annealValidityHooks, htyId, ite_false_eq hb_not_lt,
      annealAdtTyIdInhabited, ite_true_eq hb_in,
      Nat.add_sub_cancel_left, hlook, hinh, hvars]
    rfl
  have hlay_eq : (translateTy enumTy layouts).layout = translateTypeLayout tl := by
    simp [translateTy, hk, hlook]
  have hfl : (translateTy enumTy layouts).layout.fields =
      .Arbitrary #[Miri.ABI.Size.ZERO] #[0] := by
    rw [hlay_eq]
    unfold translateTypeLayout
    rw [hfields]
    rfl
  have hvr : (translateTy enumTy layouts).layout.variants =
      .Multiple (translateScalarLayout (.initialized (.int 8 false) validRange))
        .Direct 0 (variantShapes.map translateVariantFieldsShape).toArray := by
    rw [hlay_eq]
    simp [translateTypeLayout, hvars, translateVariantsShape]
  have hp_size : (translateTy enumTy layouts).layout.size = Miri.ABI.Size.ofBytes 1 := by
    rw [hlay_eq]
    simp [translateTypeLayout, hsz1, translateSize, translateSizeBytes]
  have hp_field : Miri.Interpreter.PlaceDynamic.field
      (annealValidityHooks layouts).projection enumTy place 0 m =
      .ok tagPlace m := by
    with_unfolding_all
      unfold Miri.Interpreter.PlaceDynamic.field
        Miri.Interpreter.PlaceDynamic.offsetWithMeta
        Miri.Interpreter.ValidityVisitor.Hooks.projection
        annealValidityHooks annealValidityProjectionHooksWithLayouts
      simp only [place, hfl, hvr, hp_size]
      rfl
  let tagSession : Miri.Interpreter.ValidityVisitor.Session AnnealProv :=
    { initSession with path := ⟨"", #[.enumTag]⟩ }
  have hv_tag := visit_primitive_cases (annealValidityHooks layouts) enumTy fuel
    tagSession tagPlace m rfl
  have hcl_u8 : (annealValidityHooks layouts).classify enumTy tagPlace.layout.ty m =
      .ok .integer m := rfl
  have hfp : (annealValidityHooks layouts).fieldPath enumTy place.layout 0
      tagPlace.layout.ty m = .ok .enumTag m := rfl
  refine ⟨fun hdead => ?_, fun hun => ?_,
    fun {sc msc} hrel hsc_sz1 hval => ?_⟩
  · have hop_dead : annealValidityPlaceOperand tagPlace m =
        .error (.undefinedBehavior "validation of a dead local") m := by
      exact (annealValidityPlaceOperand_local_zero_offset hframes u8Lay).trans
        (annealValidityPlaceOperand_dead_local hframes hlt hdead u8Lay)
    have hrd_dead : (annealValidityHooks layouts).readImmediate enumTy tagPlace
        .integer m =
        .error (.undefinedBehavior "validation of a dead local") m :=
      estate_bind_err _ _ _ _ _ hop_dead
    have htag_err := hv_tag.2.1 .integer (Or.inr (Or.inr rfl)) hcl_u8 _ hrd_dead
    have hvisit_err : Miri.Interpreter.ValidityVisitor.visit
        (annealValidityHooks layouts) enumTy (fuel + 2) initSession place m =
        .error (.undefinedBehavior "validation of a dead local") m := by
      unfold Miri.Interpreter.ValidityVisitor.visit
      rw [estate_bind_ok _ _ _ _ _ hcl]
      refine (estate_bind_ok _ _ _ _ none rfl).trans ?_
      have hf_eq : place.layout.layout.fields = .Arbitrary #[Miri.ABI.Size.ZERO] #[0] := hfl
      rw [hf_eq]
      dsimp only [initSession, forIn]
      rw [forIn'_singleton_estate]
      refine estate_bind_err _ _ _ _ _ (estate_bind_err _ _ _ _ _ ?_)
      refine (estate_bind_ok _ _ _ _ _ hp_field).trans ?_
      refine (estate_bind_ok _ _ _ _ _ hfp).trans ?_
      exact estate_bind_err _ _ _ _ _ htag_err
    exact hvp.2 _ _ hvisit_err
  · have hop_un : annealValidityPlaceOperand tagPlace m =
        .ok (.immediate .uninit) m :=
      (annealValidityPlaceOperand_local_zero_offset hframes u8Lay).trans
        (annealValidityPlaceOperand_local hframes hlt hun u8Lay)
    have hrd_un : (annealValidityHooks layouts).readImmediate enumTy tagPlace
        .integer m =
        .error (.undefinedBehavior "read of uninitialized local") m :=
      (estate_bind_ok _ _ _ _ _ hop_un).trans rfl
    have htag_err := hv_tag.2.1 .integer (Or.inr (Or.inr rfl)) hcl_u8 _ hrd_un
    have hvisit_err : Miri.Interpreter.ValidityVisitor.visit
        (annealValidityHooks layouts) enumTy (fuel + 2) initSession place m =
        .error (.undefinedBehavior "read of uninitialized local") m := by
      unfold Miri.Interpreter.ValidityVisitor.visit
      rw [estate_bind_ok _ _ _ _ _ hcl]
      refine (estate_bind_ok _ _ _ _ none rfl).trans ?_
      have hf_eq : place.layout.layout.fields = .Arbitrary #[Miri.ABI.Size.ZERO] #[0] := hfl
      rw [hf_eq]
      dsimp only [initSession, forIn]
      rw [forIn'_singleton_estate]
      refine estate_bind_err _ _ _ _ _ (estate_bind_err _ _ _ _ _ ?_)
      refine (estate_bind_ok _ _ _ _ _ hp_field).trans ?_
      refine (estate_bind_ok _ _ _ _ _ hfp).trans ?_
      exact estate_bind_err _ _ _ _ _ htag_err
    have hdec_un : decodeValueFromBytes (dFuel + 1) layouts enumTy [.uninit] = none := by
      unfold decodeValueFromBytes
      rw [hk, hlook]; dsimp only []
      rw [hinh, hsz1, hvars, hfields]
      rfl
    exact ⟨hvp.2 _ _ hvisit_err, hdec_un⟩
  · have hcan := hrel.canonical
    rw [hsc_sz1] at hcan
    have hlt256 : sc.bits < 256 := by
      have : scalarModulus 1 = 256 := by decide
      omega
    have htb : msc.toBits (Miri.ABI.Size.ofBytes 1) =
        .ok (BitVec.ofNat 128 sc.bits) := by
      have hb := hrel.toBits_eq
      rw [hsc_sz1] at hb
      exact hb
    have hop_ok : annealValidityPlaceOperand place m =
        .ok (.immediate (.scalar (.fromScalarInt msc))) m :=
      annealValidityPlaceOperand_local hframes hlt hval place.layout
    have hop_tag : annealValidityPlaceOperand tagPlace m =
        .ok (.immediate (.scalar (.fromScalarInt msc))) m :=
      (annealValidityPlaceOperand_local_zero_offset hframes u8Lay).trans
        (annealValidityPlaceOperand_local hframes hlt hval u8Lay)
    have hrd_ok : (annealValidityHooks layouts).readImmediate enumTy tagPlace
        .integer m =
        .ok ⟨.scalar (.fromScalarInt msc), u8Lay⟩ m :=
      (estate_bind_ok _ _ _ _ _ hop_tag).trans rfl
    have htag_ok : Miri.Interpreter.ValidityVisitor.visit
        (annealValidityHooks layouts) enumTy (fuel + 1) tagSession tagPlace m =
        .ok tagSession m :=
      hv_tag.2.2.1 hcl_u8 _ hrd_ok
    have hr_eq := translateWrappingRange_contains_eq validRange sc.bits hr_start
      hr_end (by omega)
    have htr64 := u64_truncate_lt_u64 sc.bits (by omega)
    have hbv_nat : (BitVec.ofNat 128 sc.bits).toNat = sc.bits := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : sc.bits < 2 ^ 128)]
    have hu8_nat : (UInt8.ofNat sc.bits).toBitVec.toNat = sc.bits := by
      simp [UInt8.ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt256]
    have hdsl :
        decodeScalarLayoutBytes (.initialized (.int 8 false) validRange)
          [.init (UInt8.ofNat sc.bits) none] =
          (if wrappingRangeContains validRange sc.bits then
             some (.scalar ⟨sc.bits, 1⟩)
           else
             none) := by
      change (match wrappingRangeContains validRange
                (UInt8.ofNat sc.bits).toBitVec.toNat with
              | false => none
              | true =>
                some (Value.scalar ⟨(UInt8.ofNat sc.bits).toBitVec.toNat, 1⟩)) = _
      rw [hu8_nat]
      cases wrappingRangeContains validRange sc.bits <;> rfl
    have hdec_eq :
        decodeValueFromBytes (dFuel + 1) layouts enumTy
          [.init (UInt8.ofNat sc.bits) none] =
          (match decodeScalarLayoutBytes (.initialized (.int 8 false) validRange)
                  [.init (UInt8.ofNat sc.bits) none] with
           | some (.scalar tagSc) =>
             match get? variantShapes tagSc.bits with
             | some (.arbitrary varOffsets _) =>
               match decodeFieldsBySpan [.init (UInt8.ofNat sc.bits) none] 1 varOffsets with
               | some vals => some (.aggregate tagSc.bits vals)
               | none => none
             | _ => none
           | _ => none) := by
      unfold decodeValueFromBytes
      rw [hk, hlook]; dsimp only []
      rw [hinh, hsz1, hvars, hfields]
      rfl
    have hdiscr :
        Miri.Interpreter.Discriminant.readDiscriminant
          (annealValidityHooks layouts).discriminant enumTy
          ⟨.immediate (.scalar (.fromScalarInt msc)), place.layout⟩ m =
          (if wrappingRangeContains validRange sc.bits == false then
             .error (.undefinedBehavior "InvalidTag(outside valid range)") m
           else if sc.bits < variantShapes.length then
             .ok sc.bits m
           else
             .error (.undefinedBehavior "InvalidTag(no declared discriminant)") m) := by
      let rawTag := translateScalarLayout (.initialized (.int 8 false) validRange)
      have hproj_rd :
          (annealValidityHooks layouts).discriminant.projectRead enumTy
            ⟨.immediate (.scalar (.fromScalarInt msc)), place.layout⟩ 0 m =
            .ok ⟨.immediate (.scalar (.fromScalarInt msc)), u8Lay⟩ m := by
        simp only [annealValidityHooks, place, hfl, hvr]
        rfl
      have hvfd :
          (annealValidityHooks layouts).discriminant.variantForDiscriminant enumTy
            place.layout.ty (BitVec.ofNat 128 sc.bits) m =
            (if sc.bits < variantShapes.length then
               .ok (some sc.bits) m
             else
               .ok none m) := by
        simp only [annealValidityHooks, place, htyId, ite_true_eq hb_in,
          Nat.add_sub_cancel_left, hlook, hvars, hbv_nat]
        split <;> rfl
      with_unfolding_all
        unfold Miri.Interpreter.Discriminant.readDiscriminant Miri.Interpreter.RvalueM
        repeat rw [estate_pure_bind]
        refine (estate_bind_ok _ _ _ _
          ({ ty := 23, layout := scalarLayoutData 8 false } : Miri.Interpreter.LocalLayout)
          rfl).trans ?_
        have hvr_eq :
            place.layout.layout.variants =
              .Multiple rawTag .Direct 0
                (variantShapes.map translateVariantFieldsShape).toArray := hvr
        rw [hvr_eq]
        dsimp only []
        refine (estate_bind_ok _ _ _ _ u8Lay rfl).trans ?_
        refine (estate_bind_ok _ _ _ _ _ hproj_rd).trans ?_
        refine (estate_bind_ok _ _ _ _
          (⟨.scalar (.fromScalarInt msc), u8Lay⟩ : Miri.Interpreter.RvalueImmTy AnnealProv)
          rfl).trans ?_
        dsimp only []
        repeat rw [estate_bind_assoc]
        repeat rw [estate_pure_bind]
        refine (estate_bind_ok _ _ _ _ false rfl).trans ?_
        refine (estate_bind_ok _ _ _ _ false rfl).trans ?_
        repeat rw [estate_bind_assoc]
        repeat rw [estate_pure_bind]
        refine (estate_bind_ok _ _ _ _
          (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) msc) rfl).trans ?_
        refine (estate_bind_ok _ _ _ _
          (Miri.Memory.ScalarIntCastResult.integer msc) rfl).trans ?_
        refine (estate_bind_ok _ _ _ _ (BitVec.ofNat 128 sc.bits) (by
          dsimp [u8Lay, scalarLayoutData, translateSizeBytes]
          rw [htb]; rfl)).trans ?_
        repeat rw [estate_bind_assoc]
        refine (estate_bind_ok _ _ _ _ (translateWrappingRange validRange) rfl).trans ?_
        rw [hr_eq]
        by_cases hrc : wrappingRangeContains validRange sc.bits = true
        · rw [hrc, show (!true) = false from rfl, ite_false_eq (by decide)]
          repeat rw [estate_pure_bind]
          refine (estate_bind_ok _ _ _ _ (BitVec.ofNat 128 sc.bits) (by
            dsimp [scalarLayoutData, translateSizeBytes]; rw [htr64]; rfl)).trans ?_
          by_cases hlt_v : sc.bits < variantShapes.length
          · have hvfd_ok :
                (annealValidityHooks layouts).discriminant.variantForDiscriminant enumTy
                  place.layout.ty (BitVec.ofNat 128 sc.bits) m = .ok (some sc.bits) m := by
              rw [hvfd, ite_true_eq hlt_v]
            refine (estate_bind_ok _ _ _ _ _ hvfd_ok).trans ?_
            dsimp only []
            repeat rw [estate_pure_bind]
            rw [ite_true_eq hlt_v]
            have huninh : place.layout.layout.isVariantUninhabited sc.bits = false := by
              unfold Miri.ABI.LayoutData.isVariantUninhabited
              rw [hvr]
              dsimp only []
              have harr :
                  (variantShapes.map translateVariantFieldsShape).toArray[sc.bits]? =
                    some (translateVariantFieldsShape (.arbitrary .nil .nil)) := by
                rw [List.getElem?_toArray, List.getElem?_map,
                  ← get?_eq_getElem?, hv_fieldless sc.bits hlt_v]
                rfl
              rw [harr]
              rfl
            rw [huninh]
            rfl
          · have hvfd_none :
                (annealValidityHooks layouts).discriminant.variantForDiscriminant enumTy
                  place.layout.ty (BitVec.ofNat 128 sc.bits) m = .ok none m := by
              rw [hvfd, ite_false_eq hlt_v]
            refine (estate_bind_ok _ _ _ _ _ hvfd_none).trans ?_
            rw [ite_false_eq hlt_v]
            rfl
        · have hrf : wrappingRangeContains validRange sc.bits = false :=
            Bool.eq_false_iff.mpr hrc
          rw [hrf]
          rfl
    have hstep_after_tag :
        Miri.Interpreter.ValidityVisitor.visit
          (annealValidityHooks layouts) enumTy (fuel + 2) initSession place m =
          (do
            let variant ← Miri.Interpreter.Discriminant.readDiscriminant
              (annealValidityHooks layouts).discriminant enumTy
              ⟨.immediate (.scalar (.fromScalarInt msc)), place.layout⟩
            let child ← Miri.Interpreter.PlaceDynamic.downcast
              (annealValidityHooks layouts).projection enumTy place variant
            let s2 ← Miri.Interpreter.ValidityVisitor.visit
              (annealValidityHooks layouts) enumTy (fuel + 1)
              { initSession with path := initSession.path.push (.variant (toString variant)) }
              child
            let s3 := { s2 with path := ⟨"", #[]⟩, flags := { s2.flags with mayDangle := false } }
            let inh ← (annealValidityHooks layouts).opsemInhabited enumTy place.layout.ty
            if !inh then throw (.invalidProgram "uninhabited type passed validity")
            pure s3 : EStateM _ _ _) m := by
      conv => lhs; unfold Miri.Interpreter.ValidityVisitor.visit Miri.Interpreter.ValidityVisitor.M
      repeat rw [estate_bind_assoc]
      repeat rw [estate_pure_bind]
      rw [estate_bind_ok _ _ _ _ _ hcl]
      refine (estate_bind_ok _ _ _ _ none rfl).trans ?_
      have hf_eq : place.layout.layout.fields = .Arbitrary #[Miri.ABI.Size.ZERO] #[0] := hfl
      have hv_eq : place.layout.layout.variants =
          .Multiple (translateScalarLayout (.initialized (.int 8 false) validRange))
            .Direct 0 (variantShapes.map translateVariantFieldsShape).toArray := hvr
      have hbox :
          (Miri.Interpreter.ValidityVisitor.TypeKind.aggregate false false true == .box) =
            false := rfl
      dsimp +zetaHave only [initSession, Bool.false_or]
      rw [hbox, ite_false_eq (by decide)]
      repeat rw [estate_bind_assoc]
      repeat rw [estate_pure_bind]
      rw [hf_eq, hv_eq]
      dsimp +zetaHave only [forIn]
      rw [forIn'_singleton_estate]
      repeat rw [estate_bind_assoc]
      repeat rw [estate_pure_bind]
      have htoOp : (annealValidityHooks layouts).toOp enumTy place m =
          .ok ⟨.immediate (.scalar (.fromScalarInt msc)), place.layout⟩ m :=
        (estate_bind_ok _ _ _ _ _ hop_ok).trans rfl
      have hdbg : (annealValidityHooks layouts).debugAssertions = false := rfl
      rw [estate_bind_ok _ _ _ _ _ hp_field]
      repeat rw [estate_bind_assoc]
      rw [estate_bind_ok _ _ _ _ _ hfp]
      repeat rw [estate_bind_assoc]
      change (Miri.Interpreter.ValidityVisitor.visit (annealValidityHooks layouts)
          enumTy (fuel + 1) tagSession tagPlace >>= _) m = _
      rw [estate_bind_ok _ _ _ _ _ htag_ok]
      dsimp +zetaHave only []
      repeat rw [estate_pure_bind]
      rw [estate_bind_ok _ _ _ _ _ htoOp]
      repeat rw [estate_bind_assoc]
      apply estate_bind_congr_cont; intro variant m1
      repeat rw [estate_bind_assoc]
      repeat rw [estate_pure_bind]
      apply estate_bind_congr_cont; intro child m2
      dsimp +zetaHave only [initSession]
      have hvp_v :
          (annealValidityHooks layouts).variantPath enumTy place.layout variant =
            pure (.variant (toString variant)) := rfl
      rw [hvp_v]
      dsimp +zetaHave only [Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
        initSession, hdbg]
      cases Miri.Interpreter.ValidityVisitor.visit (annealValidityHooks layouts)
          enumTy (fuel + 1)
          { path := (Miri.Memory.ValidationPath.mk "" #[]).push (.variant (toString variant))
            flags := ⟨false, false⟩
            ctfeMode := none
            refTracking := none
            dataBytes := none } child m2 with
      | error _ _ => rfl
      | ok s2 m3 =>
        dsimp only []
        cases (annealValidityHooks layouts).opsemInhabited enumTy place.layout.ty m3 with
        | error _ _ => rfl
        | ok inh m4 => cases inh <;> rfl
    have hcase_oob :
        wrappingRangeContains validRange sc.bits = false →
        Miri.Interpreter.ValidityVisitor.validatePlace
          (annealValidityHooks layouts) enumTy (fuel + 2) place false false m =
          .error (.undefinedBehavior "InvalidTag(outside valid range)") m ∧
        decodeValueFromBytes (dFuel + 1) layouts enumTy
          [.init (UInt8.ofNat sc.bits) none] = none := by
      intro hrf
      have hd_err : Miri.Interpreter.Discriminant.readDiscriminant
          (annealValidityHooks layouts).discriminant enumTy
          ⟨.immediate (.scalar (.fromScalarInt msc)), place.layout⟩ m =
          .error (.undefinedBehavior "InvalidTag(outside valid range)") m := by
        rw [hdiscr, hrf]; rfl
      have hv_err : Miri.Interpreter.ValidityVisitor.visit
          (annealValidityHooks layouts) enumTy (fuel + 2) initSession place m =
          .error (.undefinedBehavior "InvalidTag(outside valid range)") m := by
        rw [hstep_after_tag, estate_bind_err _ _ _ _ _ hd_err]
      have hdec : decodeValueFromBytes (dFuel + 1) layouts enumTy
          [.init (UInt8.ofNat sc.bits) none] = none := by
        rw [hdec_eq, hdsl, hrf]; rfl
      exact ⟨hvp.2 _ _ hv_err, hdec⟩
    have hcase_gap :
        wrappingRangeContains validRange sc.bits = true →
        variantShapes.length ≤ sc.bits →
        Miri.Interpreter.ValidityVisitor.validatePlace
          (annealValidityHooks layouts) enumTy (fuel + 2) place false false m =
          .error (.undefinedBehavior "InvalidTag(no declared discriminant)") m ∧
        decodeValueFromBytes (dFuel + 1) layouts enumTy
          [.init (UInt8.ofNat sc.bits) none] = none := by
      intro hrt hge
      have hd_err : Miri.Interpreter.Discriminant.readDiscriminant
          (annealValidityHooks layouts).discriminant enumTy
          ⟨.immediate (.scalar (.fromScalarInt msc)), place.layout⟩ m =
          .error (.undefinedBehavior "InvalidTag(no declared discriminant)") m := by
        rw [hdiscr, hrt, ite_false_eq (by omega : ¬ (sc.bits < variantShapes.length))]
        rfl
      have hv_err : Miri.Interpreter.ValidityVisitor.visit
          (annealValidityHooks layouts) enumTy (fuel + 2) initSession place m =
          .error (.undefinedBehavior "InvalidTag(no declared discriminant)") m := by
        rw [hstep_after_tag, estate_bind_err _ _ _ _ _ hd_err]
      have hget_none : get? variantShapes sc.bits = none := by
        rw [get?_eq_getElem?]
        exact List.getElem?_eq_none hge
      have hdec : decodeValueFromBytes (dFuel + 1) layouts enumTy
          [.init (UInt8.ofNat sc.bits) none] = none := by
        rw [hdec_eq, hdsl, ite_true_eq hrt]; dsimp only []; rw [hget_none]
      exact ⟨hvp.2 _ _ hv_err, hdec⟩
    have hcase_ok :
        wrappingRangeContains validRange sc.bits = true →
        sc.bits < variantShapes.length →
        Miri.Interpreter.ValidityVisitor.validatePlace
          (annealValidityHooks layouts) enumTy (fuel + 2) place false false m =
          .ok () m ∧
        decodeValueFromBytes (dFuel + 1) layouts enumTy
          [.init (UInt8.ofNat sc.bits) none] =
          some (.aggregate sc.bits .nil) := by
      intro hrt hlt_v
      have hd_ok : Miri.Interpreter.Discriminant.readDiscriminant
          (annealValidityHooks layouts).discriminant enumTy
          ⟨.immediate (.scalar (.fromScalarInt msc)), place.layout⟩ m =
          .ok sc.bits m := by
        rw [hdiscr, hrt, ite_true_eq hlt_v]; rfl
      let zstLay : Miri.Interpreter.LocalLayout := { ty := 51, layout := zstLayoutData }
      let vPlace : Miri.Interpreter.RuntimePlace AnnealProv :=
        ⟨.local 0 idx (some Miri.ABI.Size.ZERO) tf.localsIdentity, zstLay⟩
      have hdown : Miri.Interpreter.PlaceDynamic.downcast
          (annealValidityHooks layouts).projection enumTy place sc.bits m =
          .ok vPlace m := by
        with_unfolding_all
          unfold Miri.Interpreter.PlaceDynamic.downcast
            Miri.Interpreter.ValidityVisitor.Hooks.projection
            annealValidityHooks annealValidityProjectionHooksWithLayouts
          simp only [place, htyId, ite_true_eq hb_in,
            Nat.add_sub_cancel_left, hlook, hvars, hv_fieldless sc.bits hlt_v]
          rfl
      let vSession : Miri.Interpreter.ValidityVisitor.Session AnnealProv :=
        { initSession with path := initSession.path.push (.variant (toString sc.bits)) }
      have hv_zst : Miri.Interpreter.ValidityVisitor.visit
          (annealValidityHooks layouts) enumTy (fuel + 1) vSession vPlace m =
          .ok vSession m :=
        Miri.Interpreter.ValidityVisitor.visit_fieldless
          (annealValidityHooks layouts) enumTy fuel vSession vPlace m 0
          rfl rfl rfl rfl rfl rfl
      have hv_ok : Miri.Interpreter.ValidityVisitor.visit
          (annealValidityHooks layouts) enumTy (fuel + 2) initSession place m =
          .ok initSession m := by
        rw [hstep_after_tag, estate_bind_ok _ _ _ _ _ hd_ok,
          estate_bind_ok _ _ _ _ _ hdown,
          estate_bind_ok _ _ _ _ _ hv_zst,
          estate_bind_ok _ _ _ _ _ hinh_hook]
        rfl
      have hdec : decodeValueFromBytes (dFuel + 1) layouts enumTy
          [.init (UInt8.ofNat sc.bits) none] =
          some (.aggregate sc.bits .nil) := by
        rw [hdec_eq, hdsl, ite_true_eq hrt]; dsimp only []
        rw [hv_fieldless sc.bits hlt_v]
      exact ⟨hvp.1 initSession m hv_ok rfl, hdec⟩
    refine ⟨hcase_oob, hcase_gap, hcase_ok, ?_⟩
    cases hrc : wrappingRangeContains validRange sc.bits with
    | false =>
      obtain ⟨he, hd⟩ := hcase_oob hrc
      rw [he]
      exact ⟨(fun h => nomatch h), fun ⟨_, h⟩ => by rw [hd] at h; cases h⟩
    | true =>
      by_cases hlt_v : sc.bits < variantShapes.length
      · obtain ⟨he, hd⟩ := hcase_ok hrc hlt_v
        rw [he]
        exact ⟨fun _ => ⟨_, hd⟩, fun _ => rfl⟩
      · obtain ⟨he, hd⟩ := hcase_gap hrc (by omega)
        rw [he]
        exact ⟨(fun h => nomatch h), fun ⟨_, h⟩ => by rw [hd] at h; cases h⟩

/-- Converse of `annealValidateScalarForTyId_of_scalarRel`: when a canonical
scalar `sc` (`ScalarRel sc msc`) of the exact byte width of primitive scalar
type `ty` violates `AnnealScalarValid ty sc` (e.g. `2_u8` for `bool` or
`0xD800_u32` for `char`), `annealValidateScalarForTyId (translateTy ty ly).ty
(.fromScalarInt msc)` evaluates to `false`. -/
theorem annealValidateScalarForTyId_false_of_not_scalarValid
    {ty : Ty} (ly : LayoutTable) {sc : MirAst.ScalarInt}
    {msc : Miri.Memory.ScalarInt}
    (hrel : ScalarRel sc msc)
    (hsz : (translateTy ty ly).layout.size = translateSizeBytes sc.sizeBytes)
    (hinv : ¬ AnnealScalarValid ty sc) :
    annealValidateScalarForTyId (translateTy ty ly).ty (.fromScalarInt msc) = false := by
  have htoSi : (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) msc).toScalarInt =
      .ok msc := rfl
  cases hv : annealValidateScalarForTyId (translateTy ty ly).ty (.fromScalarInt msc) with
  | false => rfl
  | true =>
    exfalso
    apply hinv
    refine ⟨fun hb => ?_, fun hc => ?_⟩
    · have hsz1 : sc.sizeBytes = 1 := by
        have hp_sz : (translateTy ty ly).layout.size = Miri.ABI.Size.ofBytes 1 := by
          simp [translateTy, hb, scalarLayoutData, translateSizeBytes]
        have hb_eq : (1 : UInt64) = UInt64.ofNat sc.sizeBytes :=
          congrArg Miri.ABI.Size.bytes (hp_sz.symm.trans hsz)
        rcases hrel.validBytes with h | h | h | h | h <;>
          (rw [h] at hb_eq; first | exact h | cases hb_eq)
      have hty1 : (translateTy ty ly).ty = 1 := by simp [translateTy, encodeTyId, hb]
      have hmsc_sz : msc.size = Miri.ABI.Size.ofBytes 1 := by
        rw [hrel.size_eq, hsz1]; rfl
      have hlt128 : sc.bits < 2 ^ 128 := by
        have hcan := hrel.canonical
        rw [hsz1] at hcan
        have : scalarModulus 1 = 256 := rfl
        omega
      have hdata_nat : msc.data.toNat = sc.bits := by
        rw [hrel.data_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt128]
      rw [hty1] at hv
      simp only [annealValidateScalarForTyId, htoSi, hmsc_sz, hdata_nat, BEq.rfl,
        Bool.true_and, Bool.or_eq_true, beq_iff_eq] at hv
      exact hv
    · have hsz4 : sc.sizeBytes = 4 := by
        have hp_sz : (translateTy ty ly).layout.size = Miri.ABI.Size.ofBytes 4 := by
          simp [translateTy, hc, scalarLayoutData, translateSizeBytes]
        have hb_eq : (4 : UInt64) = UInt64.ofNat sc.sizeBytes :=
          congrArg Miri.ABI.Size.bytes (hp_sz.symm.trans hsz)
        rcases hrel.validBytes with h | h | h | h | h <;>
          (rw [h] at hb_eq; first | exact h | cases hb_eq)
      have hty2 : (translateTy ty ly).ty = 2 := by simp [translateTy, encodeTyId, hc]
      have hmsc_sz : msc.size = Miri.ABI.Size.ofBytes 4 := by
        rw [hrel.size_eq, hsz4]; rfl
      have hlt128 : sc.bits < 2 ^ 128 := by
        have hcan := hrel.canonical
        rw [hsz4] at hcan
        have : scalarModulus 4 = 2 ^ 32 := rfl
        omega
      have hdata_nat : msc.data.toNat = sc.bits := by
        rw [hrel.data_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt128]
      rw [hty2] at hv
      simp only [annealValidateScalarForTyId, htoSi, hmsc_sz, hdata_nat, BEq.rfl,
        Bool.true_and] at hv
      exact hv

/-- **Recursive safe-reference pointee validation at invalid `bool`/`char`
bit patterns (`LM-3.2`)**: in any `StateRelLM3_2` state (`m.stack.frames = #[tf]`),
when a safe reference `_r : &P` / `&mut P` (`P` is `bool` or `char`) points at
offset `0` of a live stack allocation `e.localIdx` of same-width integer type
`allocDecl.ty` (`u8`/`i8` for `bool`, `u32`/`i32` for `char`) holding a scalar
`.init (.scalar sc)` that violates `AnnealScalarValid P sc` (e.g. `2_u8` for
`&bool` or `0xD800_u32` for `&char`):
1. Root `ValidityVisitor.visit` (`refTracking := some .empty`) passes
   dereferenceability, non-null, inhabitedness, and alignment checks and queues
   the pointee `ptKey` at `".[deref]"`.
2. Child `ValidityVisitor.visit` on `⟨.memory ptKey.mplace, ptKey.layout⟩`
   reads the pointee at layout `P` (`annealReadMemoryPlace`) and rejects the
   invalid bit pattern with `.error (.undefinedBehavior "reading invalid value") m`. -/
theorem visit_ref_recursive_invalid_scalar_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf])
    {refIdx : Nat} (hlt : refIdx < tf.locals.size)
    {p : ProvenancePtr} {mptr : Miri.Memory.Pointer AnnealProv}
    (hptr : PtrRel allocMap p mptr) (hoff0 : p.offsetBytes = 0)
    {e : AllocMapEntry} (he : e ∈ allocMap) (htag : e.tag = p.tag)
    {allocDecl : LocalDecl}
    (hdecl_a : get? body.localDecls e.localIdx = some allocDecl)
    {pointeeTy : Ty} (hprim_p : IsPrimScalarTy pointeeTy)
    (hsz_eq : (translateTy pointeeTy body.layouts).layout.size =
      (translateTy allocDecl.ty body.layouts).layout.size)
    {refTy : Ty} {refMut : Mutability}
    (hrefTy : refTy.kind = .ref refMut pointeeTy.kind)
    (hval : (tf.locals[refIdx]'hlt).value =
      .live (.immediate (.scalar (.fromPointer annealTargetDataLayout mptr))))
    {sc : MirAst.ScalarInt}
    (hslot : get? s.frame.locals e.localIdx = some (.init (.scalar sc)))
    (hinv : ¬ AnnealScalarValid pointeeTy sc)
    (fuel : Nat) :
    let rootPlace : Miri.Interpreter.RuntimePlace AnnealProv :=
      ⟨.local 0 refIdx none tf.localsIdentity, translateTy refTy body.layouts⟩
    let rootSession : Miri.Interpreter.ValidityVisitor.Session AnnealProv :=
      { path := ⟨"", #[]⟩, flags := ⟨false, false⟩, ctfeMode := none,
        refTracking := some .empty, dataBytes := none }
    let ptKey : Miri.Interpreter.ValidityVisitor.Key AnnealProv :=
      ⟨⟨mptr.withOptionalProvenance, .none, none⟩,
        translateTy pointeeTy body.layouts⟩
    let childPath : Miri.Memory.ValidationPath := ⟨"", #[.deref]⟩
    let tracked : Miri.Memory.Validity.RefTracking
        (Miri.Interpreter.ValidityVisitor.Key AnnealProv) Miri.Memory.ValidationPath :=
      ⟨#[ptKey], #[(ptKey, childPath)]⟩
    let childSession : Miri.Interpreter.ValidityVisitor.Session AnnealProv :=
      { path := childPath, flags := ⟨false, true⟩, ctfeMode := none,
        refTracking := none, dataBytes := none }
    let childPlace : Miri.Interpreter.RuntimePlace AnnealProv :=
      ⟨.memory ptKey.mplace, ptKey.layout⟩
    Miri.Interpreter.ValidityVisitor.visit (annealValidityHooks body.layouts)
        refTy (fuel + 1) rootSession rootPlace m =
      .ok { rootSession with refTracking := some tracked } m ∧
    Miri.Interpreter.ValidityVisitor.visit (annealValidityHooks body.layouts)
        refTy (fuel + 1) childSession childPlace m =
      .error (.undefinedBehavior "reading invalid value") m := by
  intro rootPlace rootSession ptKey childPath tracked childSession childPlace
  obtain ⟨tf₀, hframes₀, _, _, hfr, _, _, _, _, _, halloc, _⟩ := id hstate
  rw [hframes] at hframes₀; injection hframes₀ with h0
  injection h0 with htf; subst htf
  obtain ⟨borTag, hmptr, _⟩ := PtrRel.allocId_of_entry halloc hptr he htag
  obtain ⟨hid, _, hbase⟩ := halloc.base_addr_valid e he
  obtain ⟨hsized, _, _⟩ := hprim_p.layout_ok (layouts := body.layouts)
  obtain ⟨hsize, hpos, hfit, _, hpow, _⟩ := hprim_p.size_align_ok body.layouts
  have hpos_nat : 0 < (translateTy pointeeTy body.layouts).layout.size.bytes.toNat := by
    exact_mod_cast hpos
  let mutBool : Bool := match refMut with | .mut => true | .not => false
  have hcl_ref : (annealValidityHooks body.layouts).classify refTy
      (translateTy refTy body.layouts).ty m = .ok (.reference mutBool) m := by
    cases refMut <;> (simp only [annealValidityHooks, annealValidityClassify,
      translateTy, encodeTyId, hrefTy, mutBool]; rfl)
  have hptLay : annealValidityPointeeLayout body.layouts refTy =
      some (translateTy pointeeTy body.layouts) := by
    have hexact : derefPointeeKindHasExactLayout pointeeTy.kind = true := by
      rcases hprim_p with h | h | ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h] <;> rfl
    unfold annealValidityPointeeLayout
    rw [hrefTy]; dsimp only []; rw [hexact]
    simp only [↓reduceIte, Option.some.injEq]
    exact hprim_p.translateTy_layoutIdx body.layouts
  have hm0 : mptr.withOptionalProvenance =
      ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId),
        some (.concrete e.allocId borTag)⟩ := by
    rw [hmptr, hoff0]
    simp [Miri.Memory.Pointer.withOptionalProvenance]
  have hmis0 : annealOffsetMisalignment mptr.withOptionalProvenance.offset
      (translateTy pointeeTy body.layouts).layout.align.abi = .ok none := by
    rw [hm0]
    exact annealOffsetMisalignment_stackBase_eq_none e.allocId _ hpow
  have hrd_root := annealValidityHooks_readImmediate_local body.layouts refTy
    hframes hlt hval (translateTy refTy body.layouts) .reference
  let ptPlace : Miri.Interpreter.MPlaceTy AnnealProv :=
    ⟨⟨mptr.withOptionalProvenance, .none, none⟩,
      translateTy pointeeTy body.layouts⟩
  have hptr_p : (annealValidityHooks body.layouts).ptrToPlace refTy
      ⟨.scalar (.fromPointer annealTargetDataLayout mptr),
        translateTy refTy body.layouts⟩ m = .ok ptPlace m := by
    show (do _ : EStateM _ _ _) m = .ok ptPlace m
    simp only [annealValidityHooks, hptLay, Miri.Interpreter.Immediate.toScalar,
      scalar_fromPointer_toPointer_eq, hmis0, bind, EStateM.bind, pure, EStateM.pure]
    rfl
  have hdyn : (annealValidityHooks body.layouts).sizeAndAlign refTy ptPlace m =
      .ok (some (ptPlace.layout.layout.size, ptPlace.layout.layout.align.abi)) m := by
    simp only [annealValidityHooks, ptPlace, hsized, ↓reduceIte]; rfl
  obtain ⟨hlive_e, _⟩ := halloc.local_alloc_sync tf hframes e he
  obtain ⟨⟨lay_t, hlay_t⟩, _, hshape⟩ :=
    hlive_e (.init (.scalar sc)) hslot (by intro h; cases h)
  obtain ⟨la, hfind, _, _, hsh⟩ := hshape allocDecl hdecl_a
  have hbyte_eq :
      la.allocation.byteSize = (translateTy pointeeTy body.layouts).layout.size := by
    rw [hsh.byteSize_eq, hsz_eq]
  have hin : 0 + (translateTy pointeeTy body.layouts).layout.size.bytes.toNat ≤
      la.allocation.byteSize.bytes.toNat := by
    rw [hbyte_eq]; omega
  have hacc_ok := (annealValidityAccessCheck_stack m.machine e.allocId borTag 0
    (translateTy pointeeTy body.layouts).layout.size hid (by decide) hbase hsize
    hpos_nat hfit).1 la hfind hin
  have hm : mptr.withOptionalProvenance =
      ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId + UInt64.ofNat 0),
        some (.concrete e.allocId borTag)⟩ := by
    rw [hmptr, hoff0]; rfl
  have hacc : (annealValidityHooks body.layouts).checkPointerAccess refTy
      ptPlace.mplace.ptr ptPlace.layout.layout.size m = .ok (.ok ()) m := by
    simp only [ptPlace]; rw [hm, annealValidityHooks_checkPointerAccess_eq, hacc_ok]
  have hsc_m : Miri.Memory.Scalar.fromMaybePointer
      (annealValidityHooks body.layouts).target.base ptPlace.mplace.ptr =
      .ok (.fromPointer annealTargetDataLayout mptr) := by
    simp only [ptPlace, hmptr, Miri.Memory.Pointer.withOptionalProvenance,
      Miri.Memory.Scalar.fromMaybePointer, annealValidityHooks,
      annealRuntimeDataLayout]
    rfl
  have hnn := annealStackBaseAddr_add_ne_zero e.allocId 0 hid (by decide)
  have hnull : (annealValidityHooks body.layouts).scalarMayBeNull refTy
      (.fromPointer annealTargetDataLayout mptr) m = .ok false m := by
    rw [hmptr, hoff0]
    exact fromPointer_scalarMayBeNull_eq body.layouts refTy _ _ m hnn
  have hinh := prim_opsemInhabited_true body.layouts refTy hprim_p m
  have hal : (annealValidityHooks body.layouts).checkPointerAlignResult refTy
      ptPlace.mplace.ptr ptPlace.layout.layout.align.abi m = .ok (.ok ()) m := by
    simp only [ptPlace, hm0, annealValidityHooks,
      annealOffsetMisalignment_stackBase_eq_none e.allocId _ hpow]
    rfl
  have hvr := visit_reference_cases (annealValidityHooks body.layouts) refTy fuel
    rootSession rootPlace m mutBool hcl_ref rfl rfl rfl
  have hv_root := (((hvr.2 _ ptPlace hrd_root hptr_p hsized hdyn).2 _ hacc hsc_m).2
    hnull).2 hinh
  have hroot_ok : Miri.Interpreter.ValidityVisitor.visit
      (annealValidityHooks body.layouts) refTy (fuel + 1) rootSession rootPlace m =
      .ok { rootSession with refTracking := some tracked } m := by
    have h1 := hv_root.2 hal
    have htr : Miri.Memory.Validity.RefTracking.empty.track ptKey
        (fun _ => rootSession.path.push .deref) = tracked := by
      simp [Miri.Memory.Validity.RefTracking.track,
        Miri.Memory.Validity.RefTracking.empty,
        Miri.Memory.ValidationPath.push, rootSession, tracked, childPath]
    simpa [rootSession, ptPlace, ptKey, htr] using h1
  -- Child read fails `annealValidateScalarForTyId` because `¬ AnnealScalarValid`:
  obtain ⟨slot_t', mls_t, _, _, hslot_t', hmls_t, _, hloc_t⟩ :=
    hfr.lookup_local hdecl_a
  rw [hslot] at hslot_t'; injection hslot_t' with hseq; subst hseq
  rw [hlay_t] at hmls_t
  have hmls_eq : mls_t = ⟨.live (.indirect (stackAllocPlace e.allocId)), lay_t⟩ :=
    Option.some.inj hmls_t.symm
  have hloc_t_b :
      LocalRelLM3_1 m.machine allocMap allocDecl body.layouts (.init (.scalar sc)) mls_t := by
    rw [hmls_eq] at hloc_t ⊢
    exact hloc_t.indirect_base
  have hnz_sz :
      (translateTy allocDecl.ty body.layouts).layout.size ≠ Miri.ABI.Size.ZERO := by
    intro hz
    rw [hsz_eq, hz] at hpos_nat
    exact Nat.lt_irrefl 0 hpos_nat
  obtain ⟨_, hsc_la⟩ := hloc_t_b.indirect_stackAllocPlace_spec hmls_eq hbase hfind
    (halloc.live_key_unique e he) hnz_sz
  obtain ⟨hsc_sz, _, _, msc, hrel, hread_ok⟩ := hsc_la sc rfl
  have hread_ok' :
      la.allocation.readScalar annealTargetDataLayout
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO
          (translateTy pointeeTy body.layouts).layout.size) false =
        .ok (.fromScalarInt msc) := by
    rw [hsz_eq]; exact hread_ok
  have hread_mem_eq := annealReadMemoryPlace_zero_offset_eq hprim_p hid hbase
    hfind hbyte_eq (borTag := borTag) (st := m)
  have hval_false :
      annealValidateScalarForTyId (translateTy pointeeTy body.layouts).ty
        (.fromScalarInt msc) = false :=
    annealValidateScalarForTyId_false_of_not_scalarValid body.layouts hrel
      (hsz_eq.trans hsc_sz) hinv
  have hrm : annealReadMemoryPlace ptKey.mplace ptKey.layout m =
      .error (.undefinedBehavior "reading invalid value") m := by
    simp only [ptKey, hm0]
    rw [hread_mem_eq, hread_ok']
    dsimp only []
    rw [hval_false]
    rfl
  have hfields := prim_layout_fields_eq body.layouts hprim_p
  have hrd_child : ∀ ev,
      (annealValidityHooks body.layouts).readImmediate refTy childPlace ev m =
        annealReadMemoryPlace ptKey.mplace ptKey.layout m :=
    annealValidityHooks_readImmediate_memory body.layouts refTy hframes
      ptKey.mplace ptKey.layout hfields
  have hv_child := visit_primitive_cases (annealValidityHooks body.layouts) refTy
    fuel childSession childPlace m rfl
  obtain ⟨hcb, hcc, hci, hcu, _⟩ := annealValidityHooks_classify_prim body.layouts
    refTy (ty := pointeeTy) m
  refine ⟨hroot_ok, ?_⟩
  rcases hprim_p with hk | hk | ⟨it, hk⟩ | ⟨ut, hk⟩
  · exact hv_child.2.1 .boolean (Or.inl rfl) (hcb hk) _
      ((hrd_child .boolean).trans hrm)
  · exact hv_child.2.1 .character (Or.inr (Or.inl rfl)) (hcc hk) _
      ((hrd_child .character).trans hrm)
  · exact hv_child.2.1 .integer (Or.inr (Or.inr rfl)) (hci it hk) _
      ((hrd_child .integer).trans hrm)
  · exact hv_child.2.1 .integer (Or.inr (Or.inr rfl)) (hcu ut hk) _
      ((hrd_child .integer).trans hrm)

/-! ### Composable Reborrow-Hierarchy State Relation (`StateRelLM3_2Tree`) -/

/-- Entry in a Tree Borrows reborrow hierarchy mapping an Anneal provenance tag
`tag` (which may be either a root borrow `parentTag = none` or a reborrow child
`parentTag = some pTag`) to its target local `localIdx`, backing `lean-miri`
stack allocation `allocId`, and current `TreeBorrowPerm`. -/
structure ReborrowMapEntry where
  /-- Anneal provenance tag (`BorrowEntry.tag`). -/
  tag : Nat
  /-- Root stack local targeted by this borrow (`BorrowEntry.targetLocal`). -/
  localIdx : Local
  /-- Backing `lean-miri` stack `AllocId` for `localIdx`. -/
  allocId : Miri.Memory.AllocId
  /-- Current Tree Borrows access permission (`BorrowEntry.perm`). -/
  perm : TreeBorrowPerm
  /-- Optional parent tag in the reborrow tree (`BorrowEntry.parentTag`). -/
  parentTag : Option Nat := none

namespace ReborrowMapEntry

/-- Project a `ReborrowMapEntry` to its flat `AllocMapEntry` view (dropping
`parentTag`, which `lean-miri`'s memory-only interpreter does not consult). -/
def toAllocMapEntry (e : ReborrowMapEntry) : AllocMapEntry :=
  { tag := e.tag
    localIdx := e.localIdx
    allocId := e.allocId
    perm := e.perm }

/-- Embed a root `AllocMapEntry` into `ReborrowMapEntry` (`parentTag := none`). -/
def ofRoot (e : AllocMapEntry) : ReborrowMapEntry :=
  { tag := e.tag
    localIdx := e.localIdx
    allocId := e.allocId
    perm := e.perm
    parentTag := none }

/-- Project a `ReborrowMapEntry` to the exact `MirSemantics.BorrowEntry` stored
in `s.memory.borrows` (retaining `parentTag`). -/
def toBorrowEntry (e : ReborrowMapEntry) : BorrowEntry :=
  { tag := e.tag
    targetLocal := e.localIdx
    targetProjection := .nil
    perm := e.perm
    parentTag := e.parentTag }

@[simp]
theorem toAllocMapEntry_ofRoot (e : AllocMapEntry) :
    (ofRoot e).toAllocMapEntry = e := rfl

@[simp]
theorem toBorrowEntry_ofRoot (e : AllocMapEntry) :
    (ofRoot e).toBorrowEntry = e.toBorrowEntry := rfl

theorem map_toAllocMapEntry_ofRoot (allocMap : List AllocMapEntry) :
    (allocMap.map ofRoot).map toAllocMapEntry = allocMap := by
  induction allocMap with
  | nil => rfl
  | cons _ _ ih => simp only [List.map_cons, toAllocMapEntry_ofRoot, ih]

theorem map_toBorrowEntry_ofRoot (allocMap : List AllocMapEntry) :
    (allocMap.map ofRoot).map toBorrowEntry =
      allocMap.map AllocMapEntry.toBorrowEntry := by
  induction allocMap with
  | nil => rfl
  | cons _ _ ih => simp only [List.map_cons, toBorrowEntry_ofRoot, ih]

theorem map_toBorrowEntry_of_noParents :
    ∀ {treeMap : List ReborrowMapEntry},
      (∀ e ∈ treeMap, e.parentTag = none) →
      (treeMap.map toAllocMapEntry).map AllocMapEntry.toBorrowEntry =
        treeMap.map toBorrowEntry
  | [], _ => rfl
  | e :: es, hnop => by
    have he0 : e.parentTag = none := hnop e (List.mem_cons_self ..)
    have hes : ∀ x ∈ es, x.parentTag = none :=
      fun x hx => hnop x (List.mem_cons_of_mem _ hx)
    simp only [List.map_cons, toAllocMapEntry, AllocMapEntry.toBorrowEntry,
      toBorrowEntry, he0, map_toBorrowEntry_of_noParents hes]

end ReborrowMapEntry

/-- Replace `s.memory.borrows` with the `parentTag = none` view of `treeMap`
while keeping `s.frame`, `s.memory.nextTag`, and all other machine fields
identical. -/
def eraseBorrowParents (s : MachineState)
    (treeMap : List ReborrowMapEntry) : MachineState :=
  { s with
    memory :=
      { s.memory with
        borrows :=
          (treeMap.map ReborrowMapEntry.toAllocMapEntry).map
            AllocMapEntry.toBorrowEntry } }

/-- Composable post-reborrow simulation relation (`LM-3.2`) extending
`StateRelLM3_2` to arbitrary parent/child Tree Borrows hierarchies `treeMap`
(`BorrowEntry.parentTag = some pTag` created by `Rvalue.ref` reborrows `&*_r`
and `&mut *_r`).

Every local, frame, and `lean-miri` stack allocation invariant of
`StateRelLM3_2` holds on `eraseBorrowParents s treeMap` against
`treeMap.map ReborrowMapEntry.toAllocMapEntry`, while `s.memory.borrows`
retains the exact `parentTag` tree (`treeMap.map ReborrowMapEntry.toBorrowEntry`)
so child writes (`*_r_child = v`) and parent reads (`copy *_r_parent`) execute
Anneal's `isBorrowDescendantOrSelf` local/foreign transitions and preserve
`StateRelLM3_2Tree` across multi-step traces. -/
structure StateRelLM3_2Tree
    (body : CapturedMir) (s : MachineState) (m : AnnealStepState)
    (treeMap : List ReborrowMapEntry) : Prop where
  /-- Flat local/frame/allocation relation on the parent-erased view. -/
  erased_rel :
    StateRelLM3_2 body (eraseBorrowParents s treeMap) m
      (treeMap.map ReborrowMapEntry.toAllocMapEntry)
  /-- Exact `parentTag`-preserving borrow list in `s.memory.borrows`. -/
  borrows_eq :
    s.memory.borrows = treeMap.map ReborrowMapEntry.toBorrowEntry

/-- One-step outcome correspondence under `StateRelLM3_2Tree`, allowing a step
(such as reborrow, deref write, or deref read) to evolve `treeMap` to
`treeMap'`. -/
inductive StepRelLM3_2Tree (body : CapturedMir) (m : AnnealStepState) :
    List ReborrowMapEntry →
    MirStepNode → Miri.Interpreter.StepResult AnnealStepState Bool → Prop where
  /-- Normal intra-frame step to `StateRelLM3_2Tree`-related states under
  `treeMap'`. -/
  | step (s' : MachineState) (m' : AnnealStepState)
      (treeMap' : List ReborrowMapEntry) :
      StateRelLM3_2Tree body s' m' treeMap' →
      StepRelLM3_2Tree body m treeMap' (MirStepNode.step s') (m', .ok true)
  /-- Normal root-frame return with `ImmediateRelLM3_2`-related return values. -/
  | retRoot (treeMap : List ReborrowMapEntry)
      (decl0 : LocalDecl) (retVal : Value)
      (imm0 : Miri.Interpreter.Immediate AnnealProv)
      (mem' : Memory) (m' : AnnealStepState) :
      get? body.localDecls 0 = some decl0 →
      annealControlHooks.returnOperand () m = (m, .ok (.immediate imm0)) →
      ImmediateRelLM3_2 (treeMap.map ReborrowMapEntry.toAllocMapEntry)
        decl0.ty body.layouts retVal imm0 →
      m' = { m with stack := ⟨#[]⟩ } →
      StepRelLM3_2Tree body m treeMap
        (MirStepNode.retNormal retVal mem') (m', .ok true)
  /-- Both machines report undefined behavior. -/
  | ub (treeMap : List ReborrowMapEntry)
      (m' : AnnealStepState) (msg : String) :
      StepRelLM3_2Tree body m treeMap (MirStepNode.fail .ub)
        (m', .error (.undefinedBehavior msg))

/-- Embed any root-borrow `StateRelLM3_2` state into `StateRelLM3_2Tree` with
`allocMap.map ReborrowMapEntry.ofRoot`. -/
theorem StateRelLM3_2.toTree
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap) :
    StateRelLM3_2Tree body s m (allocMap.map ReborrowMapEntry.ofRoot) := by
  have hmap_alloc := ReborrowMapEntry.map_toAllocMapEntry_ofRoot allocMap
  have hmap_bor := ReborrowMapEntry.map_toBorrowEntry_ofRoot allocMap
  obtain ⟨_, _, _, _, _, _, _, _, _, hbor, _, _⟩ := id hstate
  have herase : eraseBorrowParents s (allocMap.map ReborrowMapEntry.ofRoot) = s := by
    unfold eraseBorrowParents
    rw [hmap_alloc, ← hbor]
  refine ⟨?_, ?_⟩
  · rw [herase, hmap_alloc]; exact hstate
  · rw [hmap_bor]; exact hbor

/-- Any `StateRelLM3_2Tree` in which every entry has `parentTag = none`
collapses directly back to `StateRelLM3_2`. -/
theorem StateRelLM3_2Tree.toFlatOfNoParents
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {treeMap : List ReborrowMapEntry}
    (htree : StateRelLM3_2Tree body s m treeMap)
    (hnop : ∀ e ∈ treeMap, e.parentTag = none) :
    StateRelLM3_2 body s m (treeMap.map ReborrowMapEntry.toAllocMapEntry) := by
  have hbor_eq := ReborrowMapEntry.map_toBorrowEntry_of_noParents hnop
  have herase : eraseBorrowParents s treeMap = s := by
    unfold eraseBorrowParents
    rw [hbor_eq, ← htree.borrows_eq]
  simpa [herase] using htree.erased_rel

/-- Look up the first `ReborrowMapEntry` in `treeMap` with provenance tag `tag`. -/
def lookupTreeMapByTag : List ReborrowMapEntry → Nat → Option ReborrowMapEntry
  | .nil, _ => none
  | e :: rest, tag => if Nat.beq e.tag tag then some e else lookupTreeMapByTag rest tag

theorem lookupBorrow_map_toBorrowEntry_treeMap
    (treeMap : List ReborrowMapEntry) (tag : Nat) :
    lookupBorrow (treeMap.map ReborrowMapEntry.toBorrowEntry) tag =
      (lookupTreeMapByTag treeMap tag).map ReborrowMapEntry.toBorrowEntry := by
  induction treeMap with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.map_cons, lookupBorrow, lookupTreeMapByTag,
      ReborrowMapEntry.toBorrowEntry]
    cases Nat.beq hd.tag tag
    · exact ih
    · rfl

theorem lookupBorrow_erased_treeMap
    (treeMap : List ReborrowMapEntry) (tag : Nat) :
    lookupBorrow
        ((treeMap.map ReborrowMapEntry.toAllocMapEntry).map AllocMapEntry.toBorrowEntry) tag =
      (lookupTreeMapByTag treeMap tag).map (fun e => e.toAllocMapEntry.toBorrowEntry) := by
  induction treeMap with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.map_cons, lookupBorrow, lookupTreeMapByTag,
      ReborrowMapEntry.toAllocMapEntry, AllocMapEntry.toBorrowEntry]
    cases Nat.beq hd.tag tag
    · exact ih
    · rfl

theorem lookupTreeMapByTag_of_mem_nodup
    {treeMap : List ReborrowMapEntry}
    (hnodup : (treeMap.map ReborrowMapEntry.tag).Nodup)
    {e : ReborrowMapEntry} (he : e ∈ treeMap) {t : Nat} (ht : e.tag = t) :
    lookupTreeMapByTag treeMap t = some e := by
  induction treeMap with
  | nil => cases he
  | cons hd tl ih =>
    simp only [List.map_cons, List.nodup_cons] at hnodup
    unfold lookupTreeMapByTag
    rcases List.mem_cons.mp he with rfl | hmem
    · simp [← ht]
    · have hne : Nat.beq hd.tag t = false := by
        cases h : Nat.beq hd.tag t
        · rfl
        · have heq := (Nat.eq_of_beq_eq_true h).trans ht.symm
          exact absurd (heq ▸ List.mem_map_of_mem hmem) hnodup.1
      rw [hne]
      exact ih hnodup.2 hmem

/-- Tree-Borrows-aware read transition on a single `ReborrowMapEntry` within
full hierarchy `allBorrows` when `targetLocal` is read through `rTag`:
descendant/self reads (`isBorrowDescendantOrSelf allBorrows rTag x.tag = true`)
preserve `x.perm`, while foreign reads freeze `.active -> .frozen`. -/
def ReborrowMapEntry.updateOnRead (allBorrows : List BorrowEntry)
    (targetLocal : Local) (rTag : Nat) (x : ReborrowMapEntry) : ReborrowMapEntry :=
  match Nat.beq x.localIdx targetLocal with
  | false => x
  | true =>
    match isBorrowDescendantOrSelf allBorrows rTag x.tag with
    | true => x
    | false =>
      match x.perm with
      | .active => { x with perm := .frozen }
      | _ => x

@[simp]
theorem ReborrowMapEntry.updateOnRead_tag (allBorrows : List BorrowEntry)
    (targetLocal : Local) (rTag : Nat) (x : ReborrowMapEntry) :
    (x.updateOnRead allBorrows targetLocal rTag).tag = x.tag := by
  unfold ReborrowMapEntry.updateOnRead
  cases Nat.beq x.localIdx targetLocal <;> try rfl
  cases isBorrowDescendantOrSelf allBorrows rTag x.tag <;> try rfl
  cases x.perm <;> rfl

@[simp]
theorem ReborrowMapEntry.updateOnRead_localIdx (allBorrows : List BorrowEntry)
    (targetLocal : Local) (rTag : Nat) (x : ReborrowMapEntry) :
    (x.updateOnRead allBorrows targetLocal rTag).localIdx = x.localIdx := by
  unfold ReborrowMapEntry.updateOnRead
  cases Nat.beq x.localIdx targetLocal <;> try rfl
  cases isBorrowDescendantOrSelf allBorrows rTag x.tag <;> try rfl
  cases x.perm <;> rfl

@[simp]
theorem ReborrowMapEntry.updateOnRead_allocId (allBorrows : List BorrowEntry)
    (targetLocal : Local) (rTag : Nat) (x : ReborrowMapEntry) :
    (x.updateOnRead allBorrows targetLocal rTag).allocId = x.allocId := by
  unfold ReborrowMapEntry.updateOnRead
  cases Nat.beq x.localIdx targetLocal <;> try rfl
  cases isBorrowDescendantOrSelf allBorrows rTag x.tag <;> try rfl
  cases x.perm <;> rfl

theorem ReborrowMapEntry.updateOnRead_toBorrowEntry (allBorrows : List BorrowEntry)
    (targetLocal : Local) (rTag : Nat) (x : ReborrowMapEntry) :
    (x.updateOnRead allBorrows targetLocal rTag).toBorrowEntry =
      updateBorrowPermOnReadAtProj allBorrows x.toBorrowEntry targetLocal
        (some rTag) .nil 0 0 := by
  rcases x with ⟨tag, loc, aid, perm, ptag⟩
  unfold ReborrowMapEntry.updateOnRead updateBorrowPermOnReadAtProj
    borrowEntryOverlapsWrite projectionsOverlap stripTransparentProjections
    projectionsOverlapAux
  dsimp only [ReborrowMapEntry.toBorrowEntry]
  cases Nat.beq loc targetLocal
  · rfl
  · dsimp only
    cases isBorrowDescendantOrSelf allBorrows rTag tag
    · dsimp only
      cases perm <;> rfl
    · rfl

theorem freezeTreeBorrowsOnReadAtProj_map_toBorrowEntry_tree
    (allBorrows : List BorrowEntry) (treeMap : List ReborrowMapEntry)
    (targetLocal : Local) (rTag : Nat) :
    freezeTreeBorrowsOnReadAtProj allBorrows
        (treeMap.map ReborrowMapEntry.toBorrowEntry) targetLocal (some rTag) .nil 0 0 =
      (treeMap.map (ReborrowMapEntry.updateOnRead allBorrows targetLocal rTag)).map
        ReborrowMapEntry.toBorrowEntry := by
  induction treeMap with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.map_cons, freezeTreeBorrowsOnReadAtProj,
      ReborrowMapEntry.updateOnRead_toBorrowEntry, ih]

/-- Per-entry deref-read transition on `treeMap` (mirroring Anneal's length-`< 2`
skip in `evalRvalue` for `.use (opKind ⟨ptrIdx, [.deref]⟩)`). -/
def derefReadMapFnTree (treeMap : List ReborrowMapEntry)
    (targetLocal : Local) (rTag : Nat) (x : ReborrowMapEntry) : ReborrowMapEntry :=
  match treeMap with
  | _ :: _ :: _ => x.updateOnRead (treeMap.map ReborrowMapEntry.toBorrowEntry) targetLocal rTag
  | _ => x

@[simp]
theorem derefReadMapFnTree_tag (treeMap : List ReborrowMapEntry)
    (targetLocal : Local) (rTag : Nat) (x : ReborrowMapEntry) :
    (derefReadMapFnTree treeMap targetLocal rTag x).tag = x.tag := by
  unfold derefReadMapFnTree
  cases treeMap with
  | nil => rfl
  | cons _ tl => cases tl <;> simp

@[simp]
theorem derefReadMapFnTree_localIdx (treeMap : List ReborrowMapEntry)
    (targetLocal : Local) (rTag : Nat) (x : ReborrowMapEntry) :
    (derefReadMapFnTree treeMap targetLocal rTag x).localIdx = x.localIdx := by
  unfold derefReadMapFnTree
  cases treeMap with
  | nil => rfl
  | cons _ tl => cases tl <;> simp

@[simp]
theorem derefReadMapFnTree_allocId (treeMap : List ReborrowMapEntry)
    (targetLocal : Local) (rTag : Nat) (x : ReborrowMapEntry) :
    (derefReadMapFnTree treeMap targetLocal rTag x).allocId = x.allocId := by
  unfold derefReadMapFnTree
  cases treeMap with
  | nil => rfl
  | cons _ tl => cases tl <;> simp

/-- Computable post-step `treeMap'` after a deref read `_d = (copy|move) *_r`:
preserves ancestor/self borrows (`isBorrowDescendantOrSelf = true`) and freezes
foreign `.active` borrows on `e.localIdx` when `treeMap` has `≥ 2` entries. -/
def derefReadNextTreeMap (locals : List LocalSlot) (treeMap : List ReborrowMapEntry)
    (ptrIdx : Local) : List ReborrowMapEntry :=
  match get? locals ptrIdx with
  | some (.init (.ptr ptrVal 8)) =>
    match lookupTreeMapByTag treeMap ptrVal.tag with
    | some e => treeMap.map (derefReadMapFnTree treeMap e.localIdx ptrVal.tag)
    | none => treeMap
  | _ => treeMap

/-- Tree-Borrows-aware write transition on a single `ReborrowMapEntry` within
full hierarchy `allBorrows` when `targetLocal` is written through `wTag`,
mirroring the unprotected per-node write transition (`treeBorrowNodeAccess
.write`) that `updateBorrowPermTreeAtProj` applies: descendant/self writes
(`isBorrowDescendantOrSelf allBorrows wTag x.tag = true`) activate the
reservations `.reservedFrz _` and `.reservedIM` to `.active` and preserve every
other permission, while foreign writes disable `x` unless it is `.cell` or
`.reservedIM`, which tolerate foreign writes. -/
def ReborrowMapEntry.updateOnWrite (allBorrows : List BorrowEntry)
    (targetLocal : Local) (wTag : Nat) (x : ReborrowMapEntry) : ReborrowMapEntry :=
  match Nat.beq x.localIdx targetLocal with
  | false => x
  | true =>
    match isBorrowDescendantOrSelf allBorrows wTag x.tag with
    | true =>
      match x.perm with
      | .reservedFrz _ => { x with perm := .active }
      | .reservedIM => { x with perm := .active }
      | _ => x
    | false =>
      match x.perm with
      | .cell => x
      | .reservedIM => x
      | _ => { x with perm := .disabled }

@[simp]
theorem ReborrowMapEntry.updateOnWrite_tag (allBorrows : List BorrowEntry)
    (targetLocal : Local) (wTag : Nat) (x : ReborrowMapEntry) :
    (x.updateOnWrite allBorrows targetLocal wTag).tag = x.tag := by
  unfold ReborrowMapEntry.updateOnWrite
  cases Nat.beq x.localIdx targetLocal <;> try rfl
  cases isBorrowDescendantOrSelf allBorrows wTag x.tag <;> cases x.perm <;> rfl

@[simp]
theorem ReborrowMapEntry.updateOnWrite_localIdx (allBorrows : List BorrowEntry)
    (targetLocal : Local) (wTag : Nat) (x : ReborrowMapEntry) :
    (x.updateOnWrite allBorrows targetLocal wTag).localIdx = x.localIdx := by
  unfold ReborrowMapEntry.updateOnWrite
  cases Nat.beq x.localIdx targetLocal <;> try rfl
  cases isBorrowDescendantOrSelf allBorrows wTag x.tag <;> cases x.perm <;> rfl

@[simp]
theorem ReborrowMapEntry.updateOnWrite_allocId (allBorrows : List BorrowEntry)
    (targetLocal : Local) (wTag : Nat) (x : ReborrowMapEntry) :
    (x.updateOnWrite allBorrows targetLocal wTag).allocId = x.allocId := by
  unfold ReborrowMapEntry.updateOnWrite
  cases Nat.beq x.localIdx targetLocal <;> try rfl
  cases isBorrowDescendantOrSelf allBorrows wTag x.tag <;> cases x.perm <;> rfl

private theorem isBorrowDescendantOrSelf_self (borrows : List BorrowEntry) (t : Nat) :
    isBorrowDescendantOrSelf borrows t t = true := by
  unfold isBorrowDescendantOrSelf
  cases length borrows with
  | zero => exact Nat.beq_refl t
  | succ _ => simp only [isBorrowDescendantOrSelfAux, Nat.beq_refl]

theorem ReborrowMapEntry.updateOnWrite_toBorrowEntry_tree
    (allBorrows : List BorrowEntry) (targetLocal : Local) (wTag : Nat)
    (x : ReborrowMapEntry) :
    (x.updateOnWrite allBorrows targetLocal wTag).toBorrowEntry =
      updateBorrowPermTreeAtProj allBorrows x.toBorrowEntry targetLocal
        (some wTag) .nil 0 0 := by
  rcases x with ⟨tag, loc, aid, perm, ptag⟩
  unfold ReborrowMapEntry.updateOnWrite updateBorrowPermTreeAtProj
    resolveTreeBorrowWriterTag updateBorrowPermAtProj
    borrowEntryOverlapsWrite projectionsOverlap stripTransparentProjections
    projectionsOverlapAux
  dsimp only [ReborrowMapEntry.toBorrowEntry]
  cases Nat.beq loc targetLocal
  · rfl
  · dsimp only
    cases hdesc : isBorrowDescendantOrSelf allBorrows wTag tag
    · have hne : Nat.beq tag wTag = false := by
        cases h : Nat.beq tag wTag
        · rfl
        · have heq := Nat.eq_of_beq_eq_true h
          subst heq
          rw [isBorrowDescendantOrSelf_self] at hdesc
          cases hdesc
      have hrel : treeBorrowWriterRelatedness
          { tag := tag, targetLocal := loc, targetProjection := .nil, perm := perm,
            parentTag := ptag } (some wTag) = .foreignAccess := by
        simp only [treeBorrowWriterRelatedness, hne]
      rw [hrel]
      rcases perm with _ | ⟨_ | _⟩ | _ | _ | _ | _ <;> rfl
    · have hrel : treeBorrowWriterRelatedness
          { tag := tag, targetLocal := loc, targetProjection := .nil, perm := perm,
            parentTag := ptag } (some tag) = .localAccess := by
        simp only [treeBorrowWriterRelatedness, Nat.beq_refl]
      rw [hrel]
      rcases perm with _ | ⟨_ | _⟩ | _ | _ | _ | _ <;> rfl

theorem invalidateTreeBorrowsAtProj_map_toBorrowEntry_tree
    (allBorrows : List BorrowEntry) (treeMap : List ReborrowMapEntry)
    (targetLocal : Local) (wTag : Nat) :
    invalidateTreeBorrowsAtProj allBorrows
        (treeMap.map ReborrowMapEntry.toBorrowEntry) targetLocal (some wTag) .nil 0 0 =
      (treeMap.map (ReborrowMapEntry.updateOnWrite allBorrows targetLocal wTag)).map
        ReborrowMapEntry.toBorrowEntry := by
  induction treeMap with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.map_cons, invalidateTreeBorrowsAtProj,
      ReborrowMapEntry.updateOnWrite_toBorrowEntry_tree, ih]

/-- Computable post-step `treeMap'` after a deref write `*_r = .use op`:
applies `ReborrowMapEntry.updateOnWrite`, activating reservations to `.active`
on all `NodeRelation::Local` ancestors (`isBorrowDescendantOrSelf = true`),
while disabling foreign borrows on `e.localIdx` other than `.cell` and
`.reservedIM`. -/
def derefWriteNextTreeMap (locals : List LocalSlot) (treeMap : List ReborrowMapEntry)
    (ptrIdx : Local) : List ReborrowMapEntry :=
  match get? locals ptrIdx with
  | some (.init (.ptr ptrVal 8)) =>
    match lookupTreeMapByTag treeMap ptrVal.tag with
    | some e =>
      treeMap.map
        (ReborrowMapEntry.updateOnWrite (treeMap.map ReborrowMapEntry.toBorrowEntry)
          e.localIdx ptrVal.tag)
    | none => treeMap
  | _ => treeMap

theorem invalidateDerefWriteBorrows_map_toBorrowEntry_tree
    (locals₁ : List LocalSlot) (treeMap : List ReborrowMapEntry)
    (hnodup : (treeMap.map ReborrowMapEntry.tag).Nodup)
    (ptrIdx : Local) (ptrVal : ProvenancePtr)
    {e : ReborrowMapEntry} (he : e ∈ treeMap) (htag : e.tag = ptrVal.tag)
    (hget : get? locals₁ ptrIdx = some (.init (.ptr ptrVal 8))) :
    invalidateDerefWriteBorrows locals₁ (treeMap.map ReborrowMapEntry.toBorrowEntry)
        ⟨ptrIdx, .cons .deref .nil⟩ .nil =
      (derefWriteNextTreeMap locals₁ treeMap ptrIdx).map ReborrowMapEntry.toBorrowEntry := by
  have hlook_tm := lookupTreeMapByTag_of_mem_nodup hnodup he htag
  have hlook_bor :
      lookupBorrow (treeMap.map ReborrowMapEntry.toBorrowEntry) ptrVal.tag =
        some e.toBorrowEntry := by
    rw [lookupBorrow_map_toBorrowEntry_treeMap, hlook_tm]; rfl
  have hdw :
      derefWriteNextTreeMap locals₁ treeMap ptrIdx =
        treeMap.map
          (ReborrowMapEntry.updateOnWrite (treeMap.map ReborrowMapEntry.toBorrowEntry)
            e.localIdx ptrVal.tag) := by
    simp [derefWriteNextTreeMap, hget, hlook_tm]
  rw [hdw]
  cases treeMap with
  | nil => cases he
  | cons b₁ rest =>
    cases rest with
    | nil =>
      rcases List.mem_singleton.mp he with rfl
      rcases e with ⟨tag, loc, aid, perm, ptag⟩
      dsimp only at htag
      subst htag
      simp only [invalidateDerefWriteBorrows, hget, List.map_cons, List.map_nil] at hlook_bor ⊢
      rw [hlook_bor]
      have hrel : treeBorrowWriterRelatedness
          { tag := ptrVal.tag, targetLocal := loc, targetProjection := .nil, perm := perm,
            parentTag := ptag } (some ptrVal.tag) = .localAccess := by
        simp only [treeBorrowWriterRelatedness, Nat.beq_refl]
      dsimp only [ReborrowMapEntry.toBorrowEntry, appendProjections,
        invalidateConflictingBorrows, updateBorrowPerm, ReborrowMapEntry.updateOnWrite]
      simp only [Nat.beq_refl, isBorrowDescendantOrSelf_self, hrel]
      rcases perm with _ | ⟨_ | _⟩ | _ | _ | _ | _ <;> rfl
    | cons b₂ rest₂ =>
      simp only [invalidateDerefWriteBorrows, hget, List.map_cons] at hlook_bor ⊢
      rw [hlook_bor]; dsimp only []
      have hproj : appendProjections e.toBorrowEntry.targetProjection .nil = .nil := rfl
      have hro : e.toBorrowEntry.rangeOffset = 0 := rfl
      have hrl : e.toBorrowEntry.rangeLen = 0 := rfl
      have htl : e.toBorrowEntry.targetLocal = e.localIdx := rfl
      rw [hproj, hro, hrl, htl]
      exact invalidateTreeBorrowsAtProj_map_toBorrowEntry_tree
        ((b₁ :: b₂ :: rest₂).map ReborrowMapEntry.toBorrowEntry)
        (b₁ :: b₂ :: rest₂) e.localIdx ptrVal.tag

/-- Initial `TreeBorrowPerm` assigned by `evalRvalue` to a reborrow `&bk (*ptrIdx)`:
`sharedBorrowPerm` for shared reborrows and `mutableBorrowPerm` for mutable and
two-phase reborrows. -/
def reborrowPermOf (localDecls : List LocalDecl) (layouts : LayoutTable)
    (bk : BorrowKind) (ptrIdx : Local) : TreeBorrowPerm :=
  match bk with
  | .shared => sharedBorrowPerm localDecls layouts ⟨ptrIdx, .cons .deref .nil⟩
  | .mut _ => mutableBorrowPerm localDecls layouts ⟨ptrIdx, .cons .deref .nil⟩

/-- Computable post-step `treeMap'` after reborrowing `_d = &bk (*ptrIdx)` with
fresh provenance tag `newTag`: applies `ReborrowMapEntry.updateOnRead` across
`treeMap` for the initial reborrow read and prepends the child borrow entry
with `parentTag = some ptrVal.tag`. -/
def reborrowTreeMapNext (localDecls : List LocalDecl) (layouts : LayoutTable)
    (bk : BorrowKind) (locals : List LocalSlot) (treeMap : List ReborrowMapEntry)
    (ptrIdx : Local) (newTag : Nat) : List ReborrowMapEntry :=
  match get? locals ptrIdx with
  | some (.init (.ptr ptrVal 8)) =>
    match lookupTreeMapByTag treeMap ptrVal.tag with
    | some e =>
      let newEntry : ReborrowMapEntry :=
        { tag := newTag
          localIdx := e.localIdx
          allocId := e.allocId
          perm := reborrowPermOf localDecls layouts bk ptrIdx
          parentTag := some ptrVal.tag }
      newEntry ::
        treeMap.map
          (ReborrowMapEntry.updateOnRead (treeMap.map ReborrowMapEntry.toBorrowEntry)
            e.localIdx ptrVal.tag)
    | none => treeMap
  | _ => treeMap

end LeanMiriSpec.Correspondence
