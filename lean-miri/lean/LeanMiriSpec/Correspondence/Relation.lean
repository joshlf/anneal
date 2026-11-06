/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import LeanMiriSpec.Correspondence.Translate

/-!
# Simulation Relations Between Anneal `MirSemantics` and `lean-miri` (`Miri.Interpreter`)

Defines the cross-specification simulation relations (`ScalarRel`, `ImmediateRel`,
`MemPlaceRel`, `LocalRel`, `FrameRel`, `StateRel`, `RvalueResultRel`, and `StepRel`)
connecting Anneal's `Trusted.Rustc.V2026_06_01.MirSemantics` operational state to
upstream `proofs-rs/lean-miri`'s `Miri.Interpreter.StepState`.

Per Architectural Constraint #3 (`LM-1.1`), `LocalRel` includes all three local
storage representations from Day 1:
1. `.dead` (`LocalSlot.dead` ↔ `LocalValue.dead`),
2. `.immediate` (`LocalSlot.uninit` / `LocalSlot.init v` ↔ `LocalValue.live (.immediate imm)`), and
3. `.indirect` (`LocalSlot.uninit` / `LocalSlot.init v` ↔ `LocalValue.live (.indirect mplace)`
   via `MemPlaceRel`),
so Phase 2 address-taken locals require zero refactoring of `FrameRel` or `StateRel`.
-/

namespace LeanMiriSpec.Correspondence

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

/-! ## 1. Scalar & Immediate Correspondence (`ScalarRel`, `ImmediateRel`) -/

/-- Valid Rust scalar integer byte widths (`1, 2, 4, 8, 16`). -/
def ValidScalarBytes (sizeBytes : Nat) : Prop :=
  sizeBytes = 1 ∨ sizeBytes = 2 ∨ sizeBytes = 4 ∨ sizeBytes = 8 ∨ sizeBytes = 16

/-- Simulation relation between an Anneal `MirAst.ScalarInt` (`bits`, `sizeBytes`)
and a `Miri.Memory.ScalarInt` (`data : BitVec 128`, `size : Size`). -/
structure ScalarRel (sc : MirAst.ScalarInt) (msc : Miri.Memory.ScalarInt) : Prop where
  /-- The byte width is one of the five standard integer byte widths (`1, 2, 4, 8, 16`). -/
  validBytes : ValidScalarBytes sc.sizeBytes
  /-- The unsigned bit pattern is canonical (`sc.bits < 2 ^ (8 * sc.sizeBytes)`). -/
  canonical : sc.bits < scalarModulus sc.sizeBytes
  /-- `msc.size` agrees with `translateSizeBytes sc.sizeBytes`. -/
  size_eq : msc.size = translateSizeBytes sc.sizeBytes
  /-- `msc.data` is the 128-bit zero-extended representation of `sc.bits`. -/
  data_eq : msc.data = BitVec.ofNat 128 sc.bits

namespace ScalarRel

/-- Every `ValidScalarBytes` width is non-zero. -/
theorem sizeBytes_ne_zero {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    (h : ScalarRel sc msc) : sc.sizeBytes ≠ 0 := by
  rcases h.validBytes with h1 | h2 | h4 | h8 | h16 <;> omega

/-- `Nat.beq sc.sizeBytes 0 = false` for related scalars. -/
theorem beq_sizeBytes_zero {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    (h : ScalarRel sc msc) : Nat.beq sc.sizeBytes 0 = false := by
  rcases h.validBytes with h1 | h2 | h4 | h8 | h16
  · rw [h1]; rfl
  · rw [h2]; rfl
  · rw [h4]; rfl
  · rw [h8]; rfl
  · rw [h16]; rfl

/-- `wrapScalarBits sc.bits (scalarModulus sc.sizeBytes) = sc.bits` for canonical scalars. -/
theorem wrapScalarBits_self {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    (h : ScalarRel sc msc) :
    wrapScalarBits sc.bits (scalarModulus sc.sizeBytes) = sc.bits := by
  unfold wrapScalarBits
  have hlt := h.canonical
  have hble : Nat.ble (scalarModulus sc.sizeBytes) sc.bits = false := by
    rw [Bool.eq_false_iff]
    intro hle
    have hle' := Nat.le_of_ble_eq_true hle
    omega
  rw [hble]

/-- `msc.toBits (translateSizeBytes sc.sizeBytes)` succeeds with `BitVec.ofNat 128 sc.bits`. -/
theorem toBits_eq {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    (h : ScalarRel sc msc) :
    msc.toBits (translateSizeBytes sc.sizeBytes) = .ok (BitVec.ofNat 128 sc.bits) := by
  unfold Miri.Memory.ScalarInt.toBits
  change (if (translateSizeBytes sc.sizeBytes != msc.size) = true then
      Except.error (Miri.Memory.ScalarIntError.sizeMismatch (translateSizeBytes sc.sizeBytes) msc.size)
    else
      Except.ok msc.data) = .ok (BitVec.ofNat 128 sc.bits)
  rw [← h.size_eq, h.data_eq]
  simp

/-- `msc.toUInt (translateSizeBytes sc.sizeBytes)` succeeds with `BitVec.ofNat 128 sc.bits`. -/
theorem toUInt_eq {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    (h : ScalarRel sc msc) :
    msc.toUInt (translateSizeBytes sc.sizeBytes) = .ok (BitVec.ofNat 128 sc.bits) :=
  h.toBits_eq

/-- `boolToScalar b` is related by `ScalarRel` to `Miri.Memory.ScalarInt.ofBool b`. -/
theorem of_boolToScalar (b : Bool) :
    ScalarRel (boolToScalar b) (Miri.Memory.ScalarInt.ofBool b) := by
  cases b <;>
    refine ⟨Or.inl rfl, by decide, rfl, rfl⟩

end ScalarRel

/-- Simulation relation between an Anneal `MirSemantics.Value` and a
`Miri.Interpreter.Immediate AnnealProv` at type `ty` and layout table `layouts`. -/
inductive ImmediateRel (ty : Ty) (layouts : LayoutTable) :
    Value → Miri.Interpreter.Immediate AnnealProv → Prop where
  /-- Zero-sized unit value corresponds to `.uninit` immediate at size zero. -/
  | unit :
      (translateTy ty layouts).layout.size = Miri.ABI.Size.ZERO →
      ImmediateRel ty layouts .unit .uninit
  /-- Single scalar value corresponds to `.scalar (.fromScalarInt msc)` with matching layout size. -/
  | scalar (sc : MirAst.ScalarInt) (msc : Miri.Memory.ScalarInt) :
      ScalarRel sc msc →
      (translateTy ty layouts).layout.size = translateSizeBytes sc.sizeBytes →
      (ty.kind = .bool → sc.sizeBytes = 1 ∧ (sc.bits = 0 ∨ sc.bits = 1)) →
      (ty.kind = .char → sc.sizeBytes = 4 ∧ isValidCharCode sc.bits = true) →
      ImmediateRel ty layouts (.scalar sc) (.scalar (.fromScalarInt msc))
  /-- Two-element scalar tuple/struct (such as checked arithmetic `(T, bool)`) corresponds to `.scalarPair`. -/
  | scalarPair (sc₁ sc₂ : MirAst.ScalarInt) (msc₁ msc₂ : Miri.Memory.ScalarInt) :
      ScalarRel sc₁ msc₁ →
      ScalarRel sc₂ msc₂ →
      ((∃ ts, ty.kind = .tuple ts) ∨ (∃ p a, ty.kind = .adt p a)) →
      (∀ t₁, ty.kind = .tuple [t₁, .bool] → sc₂.sizeBytes = 1 ∧ (sc₂.bits = 0 ∨ sc₂.bits = 1)) →
      ImmediateRel ty layouts
        (.aggregate 0 [.scalar sc₁, .scalar sc₂])
        (.scalarPair (.fromScalarInt msc₁) (.fromScalarInt msc₂))

namespace ImmediateRel

/-- Inversion lemma: any `ImmediateRel` at a primitive scalar type (`bool`, `char`,
`int`, or `uint`) is a single scalar (`ImmediateRel.scalar`). -/
theorem of_primitive_scalar
    {ty : Ty} {layouts : LayoutTable}
    {v : Value} {imm : Miri.Interpreter.Immediate AnnealProv}
    (h : ImmediateRel ty layouts v imm)
    (hprim :
      ty.kind = .bool ∨ ty.kind = .char ∨
        (∃ it, ty.kind = .int it) ∨ (∃ ut, ty.kind = .uint ut)) :
    ∃ sc msc,
      v = .scalar sc ∧
      imm = .scalar (.fromScalarInt msc) ∧
      ScalarRel sc msc ∧
      (translateTy ty layouts).layout.size = translateSizeBytes sc.sizeBytes ∧
      (ty.kind = .bool → sc.sizeBytes = 1 ∧ (sc.bits = 0 ∨ sc.bits = 1)) ∧
      (ty.kind = .char → sc.sizeBytes = 4 ∧ isValidCharCode sc.bits = true) := by
  cases h with
  | unit hzero =>
    have hne : (translateTy ty layouts).layout.size ≠ Miri.ABI.Size.ZERO := by
      rcases hprim with h | h | ⟨it, h⟩ | ⟨ut, h⟩ <;>
        (try cases it) <;> (try cases ut) <;>
        (simp only [translateTy, h]; decide)
    exact False.elim (hne hzero)
  | scalar sc msc hrel hsz hbool hchar =>
    exact ⟨sc, msc, rfl, rfl, hrel, hsz, hbool, hchar⟩
  | scalarPair _ _ _ _ _ _ hagg _ =>
    rcases hagg with ⟨ts, ht⟩ | ⟨p, a, ht⟩ <;>
      rcases hprim with h | h | ⟨it, h⟩ | ⟨ut, h⟩ <;>
      (rw [h] at ht; cases ht)

end ImmediateRel

/-! ## 2. Memory-Backed Place & Local Storage Correspondence (`MemPlaceRel`, `LocalRel`) -/

/-- Simulation relation between an optional Anneal `Value` (`none` for uninitialized
storage, `some v` for initialized storage) at type `ty` and a memory-backed
`Miri.Interpreter.MemPlace AnnealProv` in `mach`.

`baseAddr` is the 64-bit virtual base address of `allocId` cached in
`mach.addresses` (`mach.lookupBaseAddr allocId = some baseAddr`), and
`relOffset` is the allocation-relative byte offset within
`localAlloc.allocation`. Together with `addr_no_overflow`
(`baseAddr.toNat + relOffset.bytes.toNat < 2 ^ 64`), the exact address
equation `mp.ptr.offset = Size.ofBytes (baseAddr + relOffset.bytes)` uniquely
pins `relOffset.bytes.toNat = mp.ptr.offset.bytes.toNat - baseAddr.toNat`
(proved in `MemPlaceRel.relOffset_bytes_eq`, with concrete uninitialized and
initialized `LocalRel.indirect` witnesses in `Witness.lean`). -/
inductive MemPlaceRel
    (mach : AnnealMachine)
    (ty : Ty)
    (layouts : LayoutTable)
    (optVal : Option Value)
    (mp : Miri.Interpreter.MemPlace AnnealProv) : Prop where
  | mk
      (allocId : Miri.Memory.AllocId)
      (tag : Miri.Memory.BorTag)
      (baseAddr : UInt64)
      (relOffset : Miri.ABI.Size)
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
      (addr_no_overflow : baseAddr.toNat + relOffset.bytes.toNat < 2 ^ 64)
      (ptr_addr_eq : mp.ptr.offset = Miri.ABI.Size.ofBytes (baseAddr + relOffset.bytes))
      (mut_alloc : localAlloc.allocation.mutability = .Mut)
      (aligned_ptr :
        mp.ptr.offset.isAligned (translateTy ty layouts).layout.align.abi = .ok true)
      (in_bounds :
        relOffset.bytes.toNat + (translateTy ty layouts).layout.size.bytes.toNat ≤
          localAlloc.allocation.byteSize.bytes.toNat)
      (uninit_consistent :
        optVal = none →
          (translateTy ty layouts).layout.size ≠ Miri.ABI.Size.ZERO →
          localAlloc.allocation.initializationMask.isRangeInitialized
            (Miri.Memory.allocRange relOffset ((translateTy ty layouts).layout.size)) ≠
              Except.ok (Except.ok ()))
      (val_consistent :
        ∀ v, optVal = some v →
          localAlloc.allocation.initializationMask.isRangeInitialized
            (Miri.Memory.allocRange relOffset ((translateTy ty layouts).layout.size)) =
              Except.ok (Except.ok ()))
      (scalar_consistent :
        ∀ sc, optVal = some (.scalar sc) →
          (translateTy ty layouts).layout.size = translateSizeBytes sc.sizeBytes ∧
          (ty.kind = .bool → sc.sizeBytes = 1 ∧ (sc.bits = 0 ∨ sc.bits = 1)) ∧
          (ty.kind = .char → sc.sizeBytes = 4 ∧ isValidCharCode sc.bits = true) ∧
          ∃ msc,
            ScalarRel sc msc ∧
            localAlloc.allocation.readScalar
              annealTargetDataLayout
              (Miri.Memory.allocRange relOffset ((translateTy ty layouts).layout.size))
              false = .ok (.fromScalarInt msc)) :
      MemPlaceRel mach ty layouts optVal mp

namespace MemPlaceRel

/-- Under `addr_no_overflow` and `ptr_addr_eq`, the allocation-relative byte
offset is uniquely `mp.ptr.offset.bytes.toNat - baseAddr.toNat`. -/
theorem relOffset_bytes_eq {mp : Miri.Interpreter.MemPlace AnnealProv}
    {baseAddr : UInt64} {relOffset : Miri.ABI.Size}
    (hno_ovf : baseAddr.toNat + relOffset.bytes.toNat < 2 ^ 64)
    (hptr : mp.ptr.offset = Miri.ABI.Size.ofBytes (baseAddr + relOffset.bytes)) :
    relOffset.bytes.toNat = mp.ptr.offset.bytes.toNat - baseAddr.toNat := by
  have hbytes : mp.ptr.offset.bytes = baseAddr + relOffset.bytes := by
    rw [hptr]; rfl
  have hadd : (baseAddr + relOffset.bytes).toNat = baseAddr.toNat + relOffset.bytes.toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt]
    simpa [UInt64.size] using hno_ovf
  rw [hbytes, hadd]
  omega

end MemPlaceRel

/-- Simulation relation between an Anneal `LocalSlot` and a `Miri.Interpreter.LocalState`
for a local declaration `decl` under machine state `mach` and layout table `layouts`.

Includes all three constructors from Day 1 (`.dead`, `.immediate`, `.indirect`) so
both register-immediate scalars and memory-backed address-taken locals are uniformly
represented in `FrameRel` and `StateRel`. -/
inductive LocalRel
    (mach : AnnealMachine)
    (decl : LocalDecl)
    (layouts : LayoutTable) :
    LocalSlot →
    Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout →
    Prop where
  /-- Dead storage slot (`LocalSlot.dead` ↔ `LocalValue.dead`). -/
  | dead (cachedLayout : Option Miri.Interpreter.LocalLayout) :
      (∀ l ∈ cachedLayout, l = translateTy decl.ty layouts) →
      LocalRel mach decl layouts .dead ⟨.dead, cachedLayout⟩
  /-- Live immediate storage slot (`LocalSlot.uninit` or `LocalSlot.init v` ↔
  `LocalValue.live (.immediate imm)`). -/
  | immediate
      (slot : LocalSlot)
      (imm : Miri.Interpreter.Immediate AnnealProv)
      (cachedLayout : Option Miri.Interpreter.LocalLayout) :
      (∀ l ∈ cachedLayout, l = translateTy decl.ty layouts) →
      ((slot = .uninit ∧ imm = .uninit) ∨
        ∃ v, slot = .init v ∧ ImmediateRel decl.ty layouts v imm) →
      LocalRel mach decl layouts slot ⟨.live (.immediate imm), cachedLayout⟩
  /-- Live indirect (memory-backed) storage slot (`LocalSlot.uninit` or `LocalSlot.init v` ↔
  `LocalValue.live (.indirect mp)` via `MemPlaceRel`). -/
  | indirect
      (slot : LocalSlot)
      (mp : Miri.Interpreter.MemPlace AnnealProv)
      (cachedLayout : Option Miri.Interpreter.LocalLayout) :
      (∀ l ∈ cachedLayout, l = translateTy decl.ty layouts) →
      slot ≠ .dead →
      MemPlaceRel
        mach
        decl.ty
        layouts
        (match slot with | .init v => some v | _ => none)
        mp →
      LocalRel mach decl layouts slot ⟨.live (.indirect mp), cachedLayout⟩

namespace LocalRel

/-- Cached layout in a `LocalRel`-related `LocalState` always agrees with `translateTy decl.ty layouts`. -/
theorem cachedLayout_eq
    {mach : AnnealMachine}
    {decl : LocalDecl}
    {layouts : LayoutTable}
    {slot : LocalSlot}
    {mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout}
    (h : LocalRel mach decl layouts slot mls) :
    ∀ l ∈ mls.layout, l = translateTy decl.ty layouts := by
  cases h with
  | dead _ hc => exact hc
  | immediate _ _ _ hc _ => exact hc
  | indirect _ _ _ hc _ _ => exact hc

end LocalRel

/-! ## 3. Stack Frame & Machine State Correspondence (`FrameRel`, `StateRel`, `StepRel`) -/

/-- Simulation relation between an Anneal `StackFrame` (`af`) and a `lean-miri`
`Miri.Interpreter.Frame` (`mf`) executing `body` under machine state `mach`. -/
structure FrameRel
    (body : CapturedMir)
    (mach : AnnealMachine)
    (af : StackFrame)
    (mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit) : Prop where
  /-- `mf.body` is the translation of `body`. -/
  body_eq : mf.body = translateBody body
  /-- `mf.location` is `.mir ⟨af.blockIdx, af.stmtIdx⟩`. -/
  location_eq : mf.location = .mir ⟨af.blockIdx, af.stmtIdx⟩
  /-- `af.locals` and `mf.locals` have the same length as `body.localDecls`. -/
  af_locals_len : af.locals.length = body.localDecls.length
  mf_locals_size : mf.locals.size = body.localDecls.length
  /-- Pointwise correspondence of every local slot via `LocalRel`. -/
  locals_rel :
    ∀ (i : Nat) (decl : LocalDecl) (slot : LocalSlot)
      (mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout),
      get? body.localDecls i = some decl →
      get? af.locals i = some slot →
      mf.locals[i]? = some mls →
      LocalRel mach decl body.layouts slot mls

/-- Simulation relation between an Anneal `MachineState` (`s`) and a single-threaded
`AnnealStepState` (`m`) executing `body`. -/
inductive StateRel
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
      (frame_rel : FrameRel body m.machine s.frame topFrame)
      (activeCallee_none : s.memory.activeCallee = none)
      (callStack_nil : s.memory.callStack = .nil)
      (borrows_nil : s.memory.borrows = .nil)
      (activeProtectors_nil : s.memory.activeProtectors = .nil)
      (callerLocals_nil : s.memory.callerLocals = .nil) :
      StateRel body s m

/-- Predicate characterizing when a `Miri.Interpreter.StepError` is an undefined-behavior fault. -/
def isMiriUBError : Miri.Interpreter.StepError → Prop
  | .undefinedBehavior _ => True
  | _ => False

/-- Outcome correspondence between an Anneal `RvalueEvalResult` at result type `resTy`
and a `lean-miri` `Except StepError (RvalueImmTy AnnealProv)` outcome. -/
inductive RvalueResultRel (resTy : Ty) (layouts : LayoutTable) :
    RvalueEvalResult →
    Except Miri.Interpreter.StepError (Miri.Interpreter.RvalueImmTy AnnealProv) →
    Prop where
  /-- Both sides succeed with `ImmediateRel`-related values and `translateTy resTy layouts`. -/
  | ok (v : Value) (locals : List LocalSlot) (mem : Memory)
      (imm : Miri.Interpreter.Immediate AnnealProv) :
      ImmediateRel resTy layouts v imm →
      RvalueResultRel resTy layouts (.ok v locals mem)
        (.ok ⟨imm, translateTy resTy layouts⟩)
  /-- Both sides diagnose undefined behavior. -/
  | ub (msg : String) :
      RvalueResultRel resTy layouts .ub (.error (.undefinedBehavior msg))

/-- Outcome correspondence between an Anneal one-step `MirStepNode` and a `lean-miri`
`StepResult AnnealStepState Bool` (`Miri.Interpreter.Step.step`) from pre-state `m`. -/
inductive StepRel (body : CapturedMir) (m : AnnealStepState) :
    MirStepNode →
    Miri.Interpreter.StepResult AnnealStepState Bool →
    Prop where
  /-- Normal intra-frame step: both machines step to `StateRel`-related states. -/
  | step (s' : MachineState) (m' : AnnealStepState) :
      StateRel body s' m' →
      StepRel body m (MirStepNode.step s') (m', .ok true)
  /-- Normal root-frame return: Anneal halts with `MirStepNode.retNormal retVal mem'`,
  `lean-miri` extracts an `ImmediateRel`-related return value from `_0` via
  `annealControlHooks.returnOperand`, and pops the root frame (`m' = { m with stack := ⟨#[]⟩ }`)
  with `.ok true`. -/
  | retRoot (decl0 : LocalDecl) (retVal : Value)
      (imm0 : Miri.Interpreter.Immediate AnnealProv)
      (mem' : Memory) (m' : AnnealStepState) :
      get? body.localDecls 0 = some decl0 →
      annealControlHooks.returnOperand () m = (m, .ok (.immediate imm0)) →
      ImmediateRel decl0.ty body.layouts retVal imm0 →
      m' = { m with stack := ⟨#[]⟩ } →
      StepRel body m (MirStepNode.retNormal retVal mem') (m', .ok true)
  /-- Both machines diagnose undefined behavior (`MirStepNode.fail .ub` ↔ `.error (.undefinedBehavior msg)`). -/
  | ub (m' : AnnealStepState) (msg : String) :
      StepRel body m (MirStepNode.fail .ub) (m', .error (.undefinedBehavior msg))

namespace StepRel

/-- Bidirectional normal intra-frame step equivalence under `StepRel`. -/
theorem step_iff {body : CapturedMir} {m : AnnealStepState}
    {aRes : MirStepNode} {mRes : Miri.Interpreter.StepResult AnnealStepState Bool}
    (h : StepRel body m aRes mRes) :
    (∃ s', aRes = .step s' ∧ StateRel body s' mRes.1) ↔
      (mRes.2 = .ok true ∧ mRes.1.stack.frames ≠ #[]) := by
  cases h with
  | step s' m' hrel =>
    rcases hrel with ⟨tf, hf, hrc, hrp, hfr, hcal, hst, hbor, hprot, hcaller⟩
    constructor
    · intro _
      refine ⟨rfl, ?_⟩
      rw [hf]
      intro hemp
      have hsz := congrArg Array.size hemp
      contradiction
    · intro _
      exact ⟨s', rfl, StateRel.mk tf hf hrc hrp hfr hcal hst hbor hprot hcaller⟩
  | retRoot _ _ _ _ _ _ _ _ hm' =>
    subst hm'
    constructor
    · rintro ⟨_, h, _⟩; cases h
    · rintro ⟨_, hne⟩; exact False.elim (hne rfl)
  | ub _ _ =>
    constructor
    · rintro ⟨_, h, _⟩; cases h
    · rintro ⟨hok, _⟩; cases hok

/-- Bidirectional root-frame normal return equivalence under `StepRel`. -/
theorem retNormal_iff {body : CapturedMir} {m : AnnealStepState}
    {aRes : MirStepNode} {mRes : Miri.Interpreter.StepResult AnnealStepState Bool}
    (h : StepRel body m aRes mRes) :
    (∃ retVal mem', aRes = .retNormal retVal mem') ↔
      (mRes.2 = .ok true ∧ mRes.1.stack.frames = #[]) := by
  cases h with
  | step s' m' hrel =>
    rcases hrel with ⟨tf, hf, _, _, _, _, _, _, _, _⟩
    constructor
    · rintro ⟨_, _, h⟩; cases h
    · rintro ⟨_, hemp⟩
      rw [hf] at hemp
      have hsz := congrArg Array.size hemp
      contradiction
  | retRoot _ retVal _ mem' _ _ _ _ hm' =>
    subst hm'
    exact ⟨fun _ => ⟨rfl, rfl⟩, fun _ => ⟨retVal, mem', rfl⟩⟩
  | ub _ _ =>
    constructor
    · rintro ⟨_, _, h⟩; cases h
    · rintro ⟨hok, _⟩; cases hok

/-- Under `StepRel`, a root-frame normal return produces an `ImmediateRel`-related
return value in `lean-miri`'s `_0` and empties the call stack. -/
theorem retNormal_rel {body : CapturedMir} {m : AnnealStepState}
    {retVal : Value} {mem' : Memory}
    {mRes : Miri.Interpreter.StepResult AnnealStepState Bool}
    (h : StepRel body m (.retNormal retVal mem') mRes) :
    ∃ decl0 imm0,
      get? body.localDecls 0 = some decl0 ∧
      annealControlHooks.returnOperand () m = (m, .ok (.immediate imm0)) ∧
      ImmediateRel decl0.ty body.layouts retVal imm0 ∧
      mRes = ({ m with stack := ⟨#[]⟩ }, .ok true) := by
  cases h with
  | retRoot decl0 _ imm0 _ _ hdecl hop himm hm' =>
    subst hm'
    exact ⟨decl0, imm0, hdecl, hop, himm, rfl⟩

/-- Bidirectional undefined-behavior equivalence under `StepRel`. -/
theorem ub_iff {body : CapturedMir} {m : AnnealStepState}
    {aRes : MirStepNode} {mRes : Miri.Interpreter.StepResult AnnealStepState Bool}
    (h : StepRel body m aRes mRes) :
    (aRes = .fail .ub) ↔ (∃ msg, mRes.2 = .error (.undefinedBehavior msg)) := by
  cases h with
  | step _ _ _ =>
    constructor
    · intro h; cases h
    · rintro ⟨_, h⟩; cases h
  | retRoot _ _ _ _ _ _ _ _ _ =>
    constructor
    · intro h; cases h
    · rintro ⟨_, h⟩; cases h
  | ub _ msg =>
    exact ⟨fun _ => ⟨msg, rfl⟩, fun _ => rfl⟩

end StepRel

end LeanMiriSpec.Correspondence
