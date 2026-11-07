/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import LeanMiriSpec.Correspondence.Simulation
import LeanMiriSpec.Correspondence.AllocLM1_4

/-!
# `LM-1.4`: Storage, Destructive Moves, and Immediate-to-Memory Coalescing

Single-step correspondence between Anneal's `MirSemantics` and `lean-miri` under
`annealStepHooks` for:

* `StorageLive` and `StorageDead` of any local, immediate or memory-backed
  (`step_storageLive_simulation`, `step_storageDead_simulation`);
* `PlaceMention` of a live local (`step_placeMention_simulation`);
* destructive moves `_d = move _s` (`evalOperand_move_simulation`), including
  undefined behavior when `_s` is dead or uninitialized and when `_d` is dead;
* the representation coalescing theorem `forceAllocation_preserves_StateRel`:
  `Miri.Interpreter.forceAllocation` moves an immediate local into a fresh stack
  allocation without disturbing `StateRel`, and the Anneal state stays
  unchanged.

`step_stmt_lm1_4_simulation` combines the statement cases.
-/

namespace LeanMiriSpec.Correspondence

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

/-! ## 1. Well-typed `LM-1.4` statements -/

/-- A local of `mf` that is not `.dead`. -/
def IsLiveFrameLocal
    (mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    (idx : Nat) : Prop :=
  ∀ mls, mf.locals[idx]? = some mls → mls.value ≠ .dead

/-- Statements covered by the `LM-1.4` simulation, relative to the `lean-miri`
root frame `topFrame`.

The side conditions exclude exactly the cases where the two semantics
intentionally diverge or where the scalar-fragment hooks fail closed:

* `StorageDead(_0)`: rustc's MIR validator forbids it, and `lean-miri` rejects
  it with `cannotMakeReturnPlaceDead` while Anneal accepts it.
* `PlaceMention` of a dead local: Anneal reports undefined behavior, whereas
  rustc's `eval_place` (and `annealEvalPlace`) does not check liveness for sized
  locals.
* `_d = move _s` requires both locals to be immediate (memory-backed operands
  and destinations are outside the scalar fragment) and the moved type to have
  non-zero size: Anneal reads a zero-sized `()` successfully, while
  `annealReadImmediate` rejects the `.uninit` immediate that represents it.

`StatementKind.deinit` is absent: the pinned rustc has no `Deinit` statement,
and `annealStepHooks_deinit_ne_ok` pins its fail-closed translation. -/
inductive WellTypedLM1_4Stmt (body : CapturedMir)
    (topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit) :
    Statement → Prop where
  | storageLive (loc : Local) (decl : LocalDecl) (span : String) :
      get? body.localDecls loc = some decl →
      WellTypedLM1_4Stmt body topFrame ⟨.storageLive loc, span⟩
  | storageDead (loc : Local) (decl : LocalDecl) (span : String) :
      get? body.localDecls loc = some decl →
      loc ≠ 0 →
      WellTypedLM1_4Stmt body topFrame ⟨.storageDead loc, span⟩
  | placeMention (loc : Local) (decl : LocalDecl) (span : String) :
      get? body.localDecls loc = some decl →
      IsLiveFrameLocal topFrame loc →
      WellTypedLM1_4Stmt body topFrame ⟨.placeMention ⟨loc, .nil⟩, span⟩
  | assignMove (dstIdx srcIdx : Local) (dstDecl srcDecl : LocalDecl) (span : String) :
      get? body.localDecls dstIdx = some dstDecl →
      get? body.localDecls srcIdx = some srcDecl →
      dstDecl.ty = srcDecl.ty →
      (translateTy srcDecl.ty body.layouts).layout.size ≠ Miri.ABI.Size.ZERO →
      IsImmediateFrameLocal topFrame srcIdx →
      IsImmediateFrameLocal topFrame dstIdx →
      WellTypedLM1_4Stmt body topFrame
        ⟨.assign ⟨dstIdx, .nil⟩ (.use (.move ⟨srcIdx, .nil⟩)), span⟩

/-! ## 2. `StorageLive` and `StorageDead` -/

/-- Memory after `Frame.deallocateLocal` frees the allocation, if any, that the
local value `v` owns (`annealLocalStorageHooks.deallocateStack`). -/
def deallocLocalMemory (mem : AnnealMemory) (v : Miri.Interpreter.LocalValue AnnealProv) :
    AnnealMemory :=
  match v with
  | .live (.indirect mp) =>
    match mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId with
    | some id => { mem with live := mem.live.filter (fun entry => entry.1 != id) }
    | none => mem
  | _ => mem

/-- The allocation, if any, that the local value `v` owns is live in `mem`. -/
def LocalAllocLive (mem : AnnealMemory) (v : Miri.Interpreter.LocalValue AnnealProv) : Prop :=
  ∀ mp, v = .live (.indirect mp) →
    ∃ id, mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId = some id ∧
      mem.live.any (fun entry => entry.1 == id) = true

/-- `Frame.deallocateLocal` frees exactly the allocation that a memory-backed
local owns, and leaves the memory unchanged for every other local value. -/
theorem annealLocalStorageHooks_deallocateLocal_eq
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (st : AnnealMemory) (v : Miri.Interpreter.LocalValue AnnealProv)
    (hlive : LocalAllocLive st v) :
    Miri.Interpreter.Frame.deallocateLocal (annealLocalStorageHooks localDecls layouts) st v =
      ⟨deallocLocalMemory st v, .ok ()⟩ := by
  unfold Miri.Interpreter.Frame.deallocateLocal
  cases v with
  | dead => rfl
  | live op =>
    cases op with
    | immediate _ => rfl
    | indirect mp =>
      obtain ⟨id, hid, hany⟩ := hlive mp rfl
      simp only [annealLocalStorageHooks, deallocLocalMemory, hid, hany, ↓reduceIte]

/-- A local related by `LocalRel` owns, if anything, a live allocation. -/
theorem LocalRel.allocLive {mach : AnnealMachine} {decl : LocalDecl} {layouts : LayoutTable}
    {slot : LocalSlot}
    {mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout}
    (h : LocalRel mach decl layouts slot mls) :
    LocalAllocLive mach.memory mls.value := by
  intro mp hv
  cases h with
  | dead _ _ => cases hv
  | immediate _ _ _ _ _ => cases hv
  | indirect _ mp' _ _ _ hmp =>
    injection hv with hv
    injection hv with hv
    subst hv
    obtain ⟨allocId, tag, _, _, localAlloc, hprov, _, _, hl, _⟩ := hmp
    refine ⟨allocId, by rw [hprov]; rfl, ?_⟩
    obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hl
    rw [Array.any_eq_true]
    refine ⟨i, by simpa using hi, ?_⟩
    simp only [Array.getElem_toList] at hget
    simp [hget]

/-- Removing an allocation from `memory.live` keeps every `MemPlaceRel` that
names a different allocation. -/
theorem MemPlaceRel.of_filter_live {mach : AnnealMachine} {id : Miri.Memory.AllocId}
    {ty : Ty} {layouts : LayoutTable} {optVal : Option Value}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    (h : MemPlaceRel mach ty layouts optVal mp)
    (hne : mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId ≠ some id) :
    MemPlaceRel { mach with memory := { mach.memory with
        live := mach.memory.live.filter (fun entry => entry.1 != id) } }
      ty layouts optVal mp := by
  cases h with
  | mk allocId tag baseAddr relOffset localAlloc hprov hmis hmeta hl hb hovf hptr hmut halign
      hbounds huninit hval hscalar =>
    have hne' : allocId ≠ id := by
      intro heq
      apply hne
      rw [hprov, heq]
      rfl
    refine .mk allocId tag baseAddr relOffset localAlloc hprov hmis hmeta ?_ hb hovf hptr hmut
      halign hbounds huninit hval hscalar
    simp only [Array.toList_filter, List.mem_filter]
    exact ⟨hl, by simp [hne']⟩

/-- Deallocating the allocation of one local keeps the `LocalRel` of every local
that owns a different allocation. -/
theorem LocalRel.of_dealloc {mach : AnnealMachine} {decl : LocalDecl} {layouts : LayoutTable}
    {slot : LocalSlot}
    {mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout}
    {v : Miri.Interpreter.LocalValue AnnealProv}
    (h : LocalRel mach decl layouts slot mls)
    (hdisj : ∀ mp mp', v = .live (.indirect mp) → mls.value = .live (.indirect mp') →
      mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId ≠
        mp'.ptr.provenance.bind Miri.Memory.Provenance.getAllocId) :
    LocalRel { mach with memory := deallocLocalMemory mach.memory v } decl layouts slot mls := by
  cases h with
  | dead c hc => exact .dead c hc
  | immediate slot imm c hc hv => exact .immediate slot imm c hc hv
  | indirect slot mp' c hc hne hmp =>
    refine .indirect slot mp' c hc hne ?_
    match v, hdisj with
    | .live (.indirect mp), hdisj =>
      have hd := hdisj mp mp' rfl rfl
      cases hid : mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId with
      | none =>
        have hmem : deallocLocalMemory mach.memory (.live (.indirect mp)) = mach.memory := by
          simp only [deallocLocalMemory, hid]
        rw [hmem]
        exact hmp
      | some id =>
        have hmem : deallocLocalMemory mach.memory (.live (.indirect mp)) =
            { mach.memory with live := mach.memory.live.filter (fun entry => entry.1 != id) } := by
          simp only [deallocLocalMemory, hid]
        rw [hmem]
        exact hmp.of_filter_live (by rw [← hid]; exact Ne.symm hd)
    | .live (.immediate _), _ => exact hmp
    | .dead, _ => exact hmp

/-- `FrameRel.update_local` in the machine after deallocating the old value of
the updated local, given `MemoryAllocDisjoint` for the old frame. -/
theorem FrameRel.update_local_dealloc
    {body : CapturedMir} {mach : AnnealMachine}
    {af : StackFrame} {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hrel : FrameRel body mach af mf) (hdisj : MemoryAllocDisjoint mf)
    {idx : Nat} {decl : LocalDecl}
    (hdecl : get? body.localDecls idx = some decl)
    {hlt_mf : idx < mf.locals.size}
    (newSlot : LocalSlot) (newVal : Miri.Interpreter.LocalValue AnnealProv)
    (hnew : LocalRel
      { mach with memory := deallocLocalMemory mach.memory (mf.locals[idx]'hlt_mf).value }
      decl body.layouts newSlot { mf.locals[idx]'hlt_mf with value := newVal }) :
    FrameRel body
      { mach with memory := deallocLocalMemory mach.memory (mf.locals[idx]'hlt_mf).value }
      { af with locals := af.locals.set idx newSlot }
      { mf with locals := mf.locals.set idx { mf.locals[idx]'hlt_mf with value := newVal } hlt_mf }
    where
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
      apply (hrel.locals_rel i decl_i slot_i mls_i hdecl_i hslot_i hmls_i).of_dealloc
      intro mp mp' hv hv'
      apply hdisj idx i mp mp' (mf.locals[idx]'hlt_mf).layout mls_i.layout h_eq
      · rw [Array.getElem?_eq_getElem hlt_mf, ← hv]
      · rw [hmls_i, ← hv']

/-- `Frame.storageLive` on any local makes it `.live (.immediate .uninit)`,
keeps its cached layout, and frees the allocation it owned, if any. -/
theorem annealStepHooks_storageLive_any_eq
    {localDecls : List LocalDecl} {layouts : LayoutTable} {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {loc : Nat} (hframes : m.stack.frames = #[topFrame])
    (hlt : loc < topFrame.locals.size)
    (hty : ∃ ty, topFrame.body.locals[loc]? = some ty)
    (hlive : LocalAllocLive m.machine.memory (topFrame.locals[loc]'hlt).value) :
    (annealStepHooks localDecls layouts).storageLive () loc m =
      ({ stack := ⟨#[{ topFrame with
            locals := topFrame.locals.set loc
              { topFrame.locals[loc]'hlt with value := .live (.immediate .uninit) } hlt }]⟩
         machine := { m.machine with
            memory := deallocLocalMemory m.machine.memory (topFrame.locals[loc]'hlt).value } },
        .ok ()) := by
  obtain ⟨ty, hty⟩ := hty
  have hget : topFrame.getLocal loc = .ok (topFrame.locals[loc]'hlt) := by
    unfold Miri.Interpreter.Frame.getLocal
    simp [hlt, pure, Except.pure]
  simp only [annealStepHooks, annealRunFrameStorage,
    stack_currentFrame?_singleton m.stack topFrame hframes]
  simp only [Miri.Interpreter.Frame.storageLive, Miri.Interpreter.Frame.storageLiveDyn, hget, hty,
    annealLocalStorageHooks_veryTriviallySized, annealLocalStorageHooks_afterLocalWrite,
    Miri.Interpreter.MemPlaceMeta.hasMeta,
    frame_replaceLocalValue_of_lt topFrame loc hlt,
    annealLocalStorageHooks_deallocateLocal_eq _ _ _ _ hlive,
    Id.run, hframes, pure_bind, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rcases m with ⟨⟨frames⟩, ⟨mem, addr, bt⟩⟩
  rfl

/-- `Frame.storageDead` on any local other than the return place makes it
`.dead`, keeps its cached layout, and frees the allocation it owned, if any. -/
theorem annealStepHooks_storageDead_any_eq
    {localDecls : List LocalDecl} {layouts : LayoutTable} {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {loc : Nat} (hframes : m.stack.frames = #[topFrame])
    (hlt : loc < topFrame.locals.size)
    (hne : loc ≠ 0)
    (hlive : LocalAllocLive m.machine.memory (topFrame.locals[loc]'hlt).value) :
    (annealStepHooks localDecls layouts).storageDead () loc m =
      ({ stack := ⟨#[{ topFrame with
            locals := topFrame.locals.set loc
              { topFrame.locals[loc]'hlt with value := .dead } hlt }]⟩
         machine := { m.machine with
            memory := deallocLocalMemory m.machine.memory (topFrame.locals[loc]'hlt).value } },
        .ok ()) := by
  have hget : topFrame.getLocal loc = .ok (topFrame.locals[loc]'hlt) := by
    unfold Miri.Interpreter.Frame.getLocal
    simp [hlt, pure, Except.pure]
  simp only [annealStepHooks, annealRunFrameStorage,
    stack_currentFrame?_singleton m.stack topFrame hframes]
  have h_beq : (loc == 0) = false := beq_false_of_ne hne
  simp only [Miri.Interpreter.Frame.storageDead, hget,
    frame_replaceLocalValue_of_lt topFrame loc hlt,
    annealLocalStorageHooks_deallocateLocal_eq _ _ _ _ hlive,
    Id.run, hframes, h_beq, Bool.false_eq_true, ↓reduceIte]
  rcases m with ⟨⟨frames⟩, ⟨mem, addr, bt⟩⟩
  rfl

/-- `StorageLive` simulation for any declared local, immediate or memory-backed:
both machines make the local live and uninitialized, and `lean-miri` frees the
allocation that a memory-backed local owned. -/
theorem step_storageLive_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRel body s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {loc : Local} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.storageLive loc, span⟩)
    (hwt : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedLM1_4Stmt body topFrame ⟨.storageLive loc, span⟩) :
    StepRel body m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  rcases hstate with
    ⟨topFrame, hframes, ht_ret, ht_retp, hfr, hcal_none, ht_stack, ht_bor, ht_prot, ht_caller,
      hdisj⟩
  rw [stepMirFn_eq_of_not_other body s hcal_none hphase]
  simp only [hbb, hstmt]
  cases hwt topFrame hframes with
  | storageLive _ decl _ hdecl =>
    obtain ⟨slot, mls, hlt_af, hlt_mf, hslot, hmls, hmls_eq, hloc⟩ := hfr.lookup_local hdecl
    have ha : evalStmt s { kind := StatementKind.storageLive loc, span := span }
        body.localDecls body.layouts =
        MirStepNode.step (advanceStmt s (s.frame.locals.set loc LocalSlot.uninit)) := by
      unfold evalStmt
      dsimp only
      rw [hslot, set?_eq_some_set hlt_af]
    rw [ha]
    have hty : ∃ ty, topFrame.body.locals[loc]? = some ty := by
      rw [hfr.body_eq, translateBody_locals_getElem? body loc, hdecl]
      exact ⟨_, rfl⟩
    have hlive : LocalAllocLive m.machine.memory (topFrame.locals[loc]'hlt_mf).value := by
      rw [hmls_eq]; exact hloc.allocLive
    have hm : Miri.Interpreter.Step.evalStatement (annealStepHooks body.localDecls body.layouts) ()
        (translateStmt ⟨.storageLive loc, span⟩) m =
        ({ stack := ⟨#[{ topFrame with
              locals := topFrame.locals.set loc
                { topFrame.locals[loc]'hlt_mf with value := .live (.immediate .uninit) } hlt_mf }]⟩
           machine := { m.machine with
              memory := deallocLocalMemory m.machine.memory (topFrame.locals[loc]'hlt_mf).value } },
          .ok ()) := by
      simp only [Miri.Interpreter.Step.evalStatement, translateStmt, translateStmtKind]
      exact annealStepHooks_storageLive_any_eq hframes hlt_mf hty hlive
    rw [miri_step_at_statement_ok _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm rfl
      hfr.location_eq]
    apply StepRel.step
    have hnew : LocalRel
        { m.machine with
          memory := deallocLocalMemory m.machine.memory (topFrame.locals[loc]'hlt_mf).value }
        decl body.layouts .uninit
        { topFrame.locals[loc]'hlt_mf with value := .live (.immediate .uninit) } := by
      rw [hmls_eq]
      exact .immediate .uninit .uninit mls.layout (LocalRel.cachedLayout_eq hloc)
        (Or.inl ⟨rfl, rfl⟩)
    have hfr' := hfr.update_local_dealloc hdisj hdecl .uninit (.live (.immediate .uninit)) hnew
    exact StateRel.mk _ rfl ht_ret ht_retp
      ⟨hfr'.body_eq, rfl, hfr'.af_locals_len, hfr'.mf_locals_size, hfr'.locals_rel⟩
      hcal_none ht_stack ht_bor ht_prot ht_caller (by
        apply MemoryAllocDisjoint.mono_immediate hdisj
        intro k
        by_cases hk : loc = k
        · subst hk
          right
          exact ⟨.uninit, (topFrame.locals[loc]'hlt_mf).layout, by
            simp only [Array.getElem?_set, ↓reduceIte]⟩
        · left
          simp only [hk, Array.getElem?_set, ↓reduceIte])

/-- `StorageDead` simulation for any declared local other than `_0`, immediate
or memory-backed: both machines make the local dead, and `lean-miri` frees the
allocation that a memory-backed local owned. -/
theorem step_storageDead_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRel body s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {loc : Local} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.storageDead loc, span⟩)
    (hwt : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedLM1_4Stmt body topFrame ⟨.storageDead loc, span⟩) :
    StepRel body m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  rcases hstate with
    ⟨topFrame, hframes, ht_ret, ht_retp, hfr, hcal_none, ht_stack, ht_bor, ht_prot, ht_caller,
      hdisj⟩
  rw [stepMirFn_eq_of_not_other body s hcal_none hphase]
  simp only [hbb, hstmt]
  cases hwt topFrame hframes with
  | storageDead _ decl _ hdecl hne =>
    obtain ⟨slot, mls, hlt_af, hlt_mf, hslot, hmls, hmls_eq, hloc⟩ := hfr.lookup_local hdecl
    have ha : evalStmt s { kind := StatementKind.storageDead loc, span := span }
        body.localDecls body.layouts =
        MirStepNode.step (advanceStmt s (s.frame.locals.set loc LocalSlot.dead)) := by
      unfold evalStmt
      dsimp only
      rw [hslot, set?_eq_some_set hlt_af]
    rw [ha]
    have hlive : LocalAllocLive m.machine.memory (topFrame.locals[loc]'hlt_mf).value := by
      rw [hmls_eq]; exact hloc.allocLive
    have hm : Miri.Interpreter.Step.evalStatement (annealStepHooks body.localDecls body.layouts) ()
        (translateStmt ⟨.storageDead loc, span⟩) m =
        ({ stack := ⟨#[{ topFrame with
              locals := topFrame.locals.set loc
                { topFrame.locals[loc]'hlt_mf with value := .dead } hlt_mf }]⟩
           machine := { m.machine with
              memory := deallocLocalMemory m.machine.memory (topFrame.locals[loc]'hlt_mf).value } },
          .ok ()) := by
      simp only [Miri.Interpreter.Step.evalStatement, translateStmt, translateStmtKind]
      exact annealStepHooks_storageDead_any_eq hframes hlt_mf hne hlive
    rw [miri_step_at_statement_ok _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm rfl
      hfr.location_eq]
    apply StepRel.step
    have hnew : LocalRel
        { m.machine with
          memory := deallocLocalMemory m.machine.memory (topFrame.locals[loc]'hlt_mf).value }
        decl body.layouts .dead { topFrame.locals[loc]'hlt_mf with value := .dead } := by
      rw [hmls_eq]
      exact .dead mls.layout (LocalRel.cachedLayout_eq hloc)
    have hfr' := hfr.update_local_dealloc hdisj hdecl .dead .dead hnew
    exact StateRel.mk _ rfl ht_ret ht_retp
      ⟨hfr'.body_eq, rfl, hfr'.af_locals_len, hfr'.mf_locals_size, hfr'.locals_rel⟩
      hcal_none ht_stack ht_bor ht_prot ht_caller (by
        apply MemoryAllocDisjoint.mono_dead hdisj
        intro k
        by_cases hk : loc = k
        · subst hk
          right
          exact ⟨(topFrame.locals[loc]'hlt_mf).layout, by
            simp only [Array.getElem?_set, ↓reduceIte]⟩
        · left
          simp only [hk, Array.getElem?_set, ↓reduceIte])

/-! ## 3. `PlaceMention` -/

/-- `PlaceMention` of an unprojected local only memoizes its layout. -/
theorem evalStatement_placeMention_eq
    {body : CapturedMir} {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {loc : Nat} {decl : LocalDecl} {span : String}
    (hframes : m.stack.frames = #[topFrame])
    (hlt : loc < topFrame.locals.size)
    (hdecl : get? body.localDecls loc = some decl)
    (hcache : ∀ l, (topFrame.locals[loc]'hlt).layout = some l →
      l = translateTy decl.ty body.layouts) :
    Miri.Interpreter.Step.evalStatement (annealStepHooks body.localDecls body.layouts) ()
      (translateStmt ⟨.placeMention ⟨loc, .nil⟩, span⟩) m =
      ({ m with stack := ⟨#[cacheFrameLocalLayout topFrame loc hlt
          (translateTy decl.ty body.layouts)]⟩ }, .ok ()) := by
  have hplace := annealEvalPlace_unprojected hframes hlt hdecl hcache
  simp only [Miri.Interpreter.Step.evalStatement, translateStmt, translateStmtKind,
    translatePlace, List.map, List.toArray, annealStepHooks, Miri.Interpreter.runRvalue]
  rw [hplace]
  rfl

/-- `PlaceMention` simulation for a live declared local: both machines step
without changing any local value. -/
theorem step_placeMention_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRel body s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {loc : Local} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.placeMention ⟨loc, .nil⟩, span⟩)
    (hwt : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedLM1_4Stmt body topFrame ⟨.placeMention ⟨loc, .nil⟩, span⟩) :
    StepRel body m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  rcases hstate with
    ⟨topFrame, hframes, ht_ret, ht_retp, hfr, hcal_none, ht_stack, ht_bor, ht_prot, ht_caller,
      hdisj⟩
  rw [stepMirFn_eq_of_not_other body s hcal_none hphase]
  simp only [hbb, hstmt]
  cases hwt topFrame hframes with
  | placeMention _ decl _ hdecl hlive =>
    obtain ⟨slot, mls, hlt_af, hlt_mf, hslot, hmls, hmls_eq, hloc⟩ := hfr.lookup_local hdecl
    have hslot_live : slot ≠ .dead := by
      intro hdead
      subst hdead
      cases hloc with
      | dead _ _ => exact hlive _ hmls rfl
      | immediate _ _ _ _ hval => rcases hval with ⟨h, _⟩ | ⟨_, h, _⟩ <;> cases h
      | indirect _ _ _ _ hne _ => exact hne rfl
    have ha : evalStmt s { kind := StatementKind.placeMention ⟨loc, .nil⟩, span := span }
        body.localDecls body.layouts = MirStepNode.step (advanceStmt s s.frame.locals) := by
      unfold evalStmt
      dsimp only
      rw [hslot]
      cases slot with
      | dead => exact absurd rfl hslot_live
      | uninit => rfl
      | init _ => rfl
    rw [ha]
    have hcache : ∀ l, (topFrame.locals[loc]'hlt_mf).layout = some l →
        l = translateTy decl.ty body.layouts := by
      rw [hmls_eq]; exact hloc.layout_eq
    rw [miri_step_at_statement_ok _ hframes hfr.body_eq hfr.location_eq hbb hstmt
      (evalStatement_placeMention_eq (span := span) hframes hlt_mf hdecl hcache) rfl
      hfr.location_eq]
    apply StepRel.step
    have hfr' := hfr.cache_local_layout hdecl hlt_mf
    exact StateRel.mk _ rfl ht_ret ht_retp
      ⟨hfr'.body_eq, rfl, hfr'.af_locals_len, hfr'.mf_locals_size, hfr'.locals_rel⟩
      hcal_none ht_stack ht_bor ht_prot ht_caller (by
        apply MemoryAllocDisjoint.mono_layout hdisj
        intro k
        by_cases hk : loc = k
        · subst hk
          exact ⟨some (translateTy decl.ty body.layouts), by
            dsimp only [cacheFrameLocalLayout]
            rw [Array.getElem?_set, hmls]
            simp [hmls_eq]⟩
        · exact ⟨(topFrame.locals[k]?).bind (fun x => x.layout), by
            dsimp only [cacheFrameLocalLayout]
            rw [Array.getElem?_set_ne _ hk]
            cases topFrame.locals[k]? <;> rfl⟩)

/-! ## 4. Destructive moves (`_d = move _s`) -/

/-- `mf` with local `idx` deinitialized to `.live (.immediate .uninit)`, keeping
its cached layout (the frame that `Frame.replaceLocalValue` returns). -/
def deinitFrameLocal
    (mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    (idx : Nat) (hlt : idx < mf.locals.size) :
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { mf with
    locals := mf.locals.set idx
      { mf.locals[idx]'hlt with value := .live (.immediate .uninit) } hlt }

/-- `cacheFrameLocalLayout` keeps the number of locals. -/
theorem cacheFrameLocalLayout_size
    (mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    {idx : Nat} (hlt : idx < mf.locals.size) (lay : Miri.Interpreter.LocalLayout) :
    (cacheFrameLocalLayout mf idx hlt lay).locals.size = mf.locals.size := by
  unfold cacheFrameLocalLayout
  rw [Array.size_set]

/-- `annealEvalOperand` on `Move` of a live unprojected local returns its
operand, memoizes its layout, and deinitializes it. -/
theorem annealEvalOperand_move_live
    {body : CapturedMir} {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {idx : Nat} {decl : LocalDecl}
    {opVal : Miri.Interpreter.Operand AnnealProv}
    {lay : Option Miri.Interpreter.LocalLayout}
    {known : Option Miri.Interpreter.LocalLayout}
    (hframes : m.stack.frames = #[topFrame])
    (hlt : idx < topFrame.locals.size)
    (hdecl : get? body.localDecls idx = some decl)
    (hmls : topFrame.locals[idx]'hlt = ⟨.live opVal, lay⟩)
    (hcache : ∀ l, lay = some l → l = translateTy decl.ty body.layouts) :
    annealEvalOperand body.localDecls body.layouts (.Move ⟨idx, #[]⟩) known m =
      .ok ⟨opVal, translateTy decl.ty body.layouts⟩
        { m with
          stack := ⟨#[deinitFrameLocal
            (cacheFrameLocalLayout topFrame idx hlt (translateTy decl.ty body.layouts)) idx
            (by rw [cacheFrameLocalLayout_size]; exact hlt)]⟩ } := by
  have hcache' : ∀ l, (topFrame.locals[idx]'hlt).layout = some l →
      l = translateTy decl.ty body.layouts := by
    rw [hmls]; exact hcache
  have hres := annealResolveAndCacheLocalLayout_eq (known := known) hframes hlt hdecl hcache'
  have hget_c := cacheFrameLocalLayout_getLocal topFrame hlt (translateTy decl.ty body.layouts)
  rw [hmls] at hget_c
  have hgop := frame_getLocalOperand_live _ hget_c
  have hlt' : idx < (cacheFrameLocalLayout topFrame idx hlt
      (translateTy decl.ty body.layouts)).locals.size := by
    rw [cacheFrameLocalLayout_size]; exact hlt
  have hrep := frame_replaceLocalValue_of_lt
    (cacheFrameLocalLayout topFrame idx hlt (translateTy decl.ty body.layouts)) idx hlt'
    (.live (.immediate .uninit))
  with_unfolding_all
    unfold annealEvalOperand
    simp only [Bool.false_eq_true, ↓reduceIte,
      get, getThe, MonadStateOf.get, EStateM.get, set, MonadStateOf.set,
      Bind.bind, EStateM.bind, Pure.pure,
      stack_currentFrame?_singleton m.stack topFrame hframes,
      Option.isNone_some, hres, hgop, hrep]
    exact rfl

/-- `annealEvalOperand` on `Move` of a dead unprojected local reports undefined
behavior after memoizing its layout. -/
theorem annealEvalOperand_move_dead
    {body : CapturedMir} {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {idx : Nat} {decl : LocalDecl}
    {lay : Option Miri.Interpreter.LocalLayout}
    {known : Option Miri.Interpreter.LocalLayout}
    (hframes : m.stack.frames = #[topFrame])
    (hlt : idx < topFrame.locals.size)
    (hdecl : get? body.localDecls idx = some decl)
    (hmls : topFrame.locals[idx]'hlt = ⟨.dead, lay⟩)
    (hcache : ∀ l, lay = some l → l = translateTy decl.ty body.layouts) :
    annealEvalOperand body.localDecls body.layouts (.Move ⟨idx, #[]⟩) known m =
      .error (.undefinedBehavior "read of dead local")
        { m with
          stack := ⟨#[cacheFrameLocalLayout topFrame idx hlt
            (translateTy decl.ty body.layouts)]⟩ } := by
  have hcache' : ∀ l, (topFrame.locals[idx]'hlt).layout = some l →
      l = translateTy decl.ty body.layouts := by
    rw [hmls]; exact hcache
  have hres := annealResolveAndCacheLocalLayout_eq (known := known) hframes hlt hdecl hcache'
  have hget_c := cacheFrameLocalLayout_getLocal topFrame hlt (translateTy decl.ty body.layouts)
  rw [hmls] at hget_c
  have hgop := frame_getLocalOperand_dead _ hget_c
  with_unfolding_all
    unfold annealEvalOperand
    simp only [Bool.false_eq_true, ↓reduceIte,
      get, getThe, MonadStateOf.get, EStateM.get, Bind.bind, EStateM.bind,
      Pure.pure, stack_currentFrame?_singleton m.stack topFrame hframes,
      Option.isNone_some, hres, hgop]
    rfl

/-- `annealReadImmediate` rejects the `.uninit` immediate. -/
theorem annealReadImmediate_uninit (lay : Miri.Interpreter.LocalLayout) (m : AnnealStepState) :
    annealReadImmediate ⟨.immediate .uninit, lay⟩ m =
      .error (.undefinedBehavior "read of uninitialized local") m := rfl

/-- Move simulation for `_d = move _s` between immediate locals of the same
non-zero-sized type. Both machines read `_s`, deinitialize it, and write the
value to `_d`; both report undefined behavior when `_s` is dead or uninitialized
or when `_d` is dead. -/
theorem evalOperand_move_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRel body s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx srcIdx : Local} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.use (.move ⟨srcIdx, .nil⟩)), span⟩)
    (hwt : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedLM1_4Stmt body topFrame
        ⟨.assign ⟨dstIdx, .nil⟩ (.use (.move ⟨srcIdx, .nil⟩)), span⟩) :
    StepRel body m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  rcases hstate with
    ⟨topFrame, hframes, hretCont, ⟨retLay, hretPlace⟩, hframe,
      hcal, hstack, hbor, hprot, hcaller, hd_tf⟩
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  simp only [hbb, hstmt]
  cases hwt topFrame hframes with
  | assignMove _ _ dstDecl srcDecl _ hdecl_dst hdecl_src hty hsz himm_src himm_dst =>
    -- `annealEvalPlace` memoizes the destination layout.
    obtain ⟨_, mls_dst0, _, hlt_dst0, _, hmls_opt, hmls_eq0, hloc_dst0⟩ :=
      hframe.lookup_local hdecl_dst
    let topFrame₀ :=
      cacheFrameLocalLayout topFrame dstIdx hlt_dst0 (translateTy dstDecl.ty body.layouts)
    have hdisj₀ : MemoryAllocDisjoint topFrame₀ := by
      apply MemoryAllocDisjoint.mono_layout hd_tf
      intro k
      by_cases hk : k = dstIdx
      · subst hk
        exists (translateTy dstDecl.ty body.layouts)
        dsimp [topFrame₀, cacheFrameLocalLayout]
        rw [Array.getElem?_set]
        simp only [↓reduceIte]
        rw [hmls_opt, hmls_eq0]
        rfl
      · exists (topFrame.locals[k]?).bind (fun x => x.layout)
        dsimp [topFrame₀, cacheFrameLocalLayout]
        rw [Array.getElem?_set_ne _ (Ne.symm hk)]
        cases topFrame.locals[k]? <;> rfl
    let m₀ : AnnealStepState := { m with stack := ⟨#[topFrame₀]⟩ }
    have hcache_dst0 : ∀ l, (topFrame.locals[dstIdx]'hlt_dst0).layout = some l →
        l = translateTy dstDecl.ty body.layouts := by
      rw [hmls_eq0]; exact hloc_dst0.layout_eq
    have hevalPlace_dst : annealEvalPlace body.localDecls body.layouts ⟨dstIdx, #[]⟩ m =
        .ok ⟨.local 0 dstIdx none topFrame.localsIdentity,
          translateTy dstDecl.ty body.layouts⟩ m₀ :=
      annealEvalPlace_unprojected hframes hlt_dst0 hdecl_dst hcache_dst0
    have hframe₀ : FrameRel body m₀.machine s.frame topFrame₀ :=
      hframe.cache_local_layout hdecl_dst hlt_dst0
    have hmono₀ : ∀ j, IsImmediateFrameLocal topFrame j → IsImmediateFrameLocal topFrame₀ j :=
      fun _ hj => hj.cache_layout hlt_dst0 _
    let destPlace : Miri.Interpreter.RuntimePlace AnnealProv :=
      ⟨.local 0 dstIdx none topFrame.localsIdentity, translateTy dstDecl.ty body.layouts⟩
    have hmem_same : { s.memory with borrows := .nil, activeProtectors := .nil } = s.memory := by
      revert hbor hprot
      generalize s.memory = mem
      intro hbor hprot
      cases mem
      dsimp only at hbor hprot
      subst hbor hprot
      rfl
    dsimp only at hmem_same
    -- The statement runs the moved operand, reads it, and writes it to `_d`.
    have hm_eval : Miri.Interpreter.Step.evalStatement
        (annealStepHooks body.localDecls body.layouts) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.use (.move ⟨srcIdx, .nil⟩)), span⟩) m =
        Miri.Interpreter.runRvalue
          ((annealEvalOperand body.localDecls body.layouts (.Move ⟨srcIdx, #[]⟩)
              (some (translateTy dstDecl.ty body.layouts)) >>= annealReadImmediate) >>=
            fun imm => annealWriteImmediate imm.imm destPlace) m₀ := by
      unfold Miri.Interpreter.Step.evalStatement translateStmt
      dsimp only [translateStmtKind, translatePlace, translateOperand, List.map, List.toArray,
        translateRvalue, annealStepHooks]
      apply runRvalue_eq_of_eq
      unfold Miri.Interpreter.evalRvalueIntoPlace annealRvalueHooks
      dsimp only [Miri.Interpreter.RvalueHooks.evalOperandAt]
      rw [EStateM.bind_eq_ok hevalPlace_dst]
      exact EStateM.bind_assoc_apply _ _ _ m₀
    -- Case on the source local.
    obtain ⟨slot_src, mls_src, hlt_af_src, hlt_src, hslot_src, hmls_src, hmls_src_eq, hloc_src⟩ :=
      hframe₀.lookup_local hdecl_src
    cases hloc_src with
    | dead cl hcl =>
      have ha_ub : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.use (.move ⟨srcIdx, .nil⟩)), span⟩
          body.localDecls body.layouts = MirStepNode.fail .ub := by
        unfold evalStmt
        simp [evalRvalue, evalOperand, hslot_src]
      have hm_err : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.use (.move ⟨srcIdx, .nil⟩)), span⟩) m =
          ({ m₀ with stack := ⟨#[cacheFrameLocalLayout topFrame₀ srcIdx hlt_src
              (translateTy srcDecl.ty body.layouts)]⟩ },
            .error (.undefinedBehavior "read of dead local")) := by
        rw [hm_eval]
        unfold Miri.Interpreter.runRvalue
        rw [EStateM.bind_eq_error (EStateM.bind_eq_error
          (annealEvalOperand_move_dead rfl hlt_src hdecl_src hmls_src_eq (fun l hl => hcl l hl)))]
      rw [ha_ub, miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq hbb
        hstmt hm_err]
      exact .ub _ _
    | indirect _ mp _ _ _ _ =>
      exact absurd rfl (hmono₀ srcIdx himm_src _ hmls_src mp)
    | immediate slot imm cl hcl hval =>
      have hlt_src' : srcIdx < (cacheFrameLocalLayout topFrame₀ srcIdx hlt_src
          (translateTy srcDecl.ty body.layouts)).locals.size := by
        rw [cacheFrameLocalLayout_size]; exact hlt_src
      let topFrame₁ := deinitFrameLocal
        (cacheFrameLocalLayout topFrame₀ srcIdx hlt_src (translateTy srcDecl.ty body.layouts))
        srcIdx hlt_src'
      have hop := annealEvalOperand_move_live
        (known := some (translateTy dstDecl.ty body.layouts))
        (rfl : m₀.stack.frames = #[topFrame₀]) hlt_src hdecl_src hmls_src_eq
        (fun l hl => hcl l hl)
      rcases hval with ⟨rfl, rfl⟩ | ⟨v, rfl, himmRel⟩
      · -- Uninitialized source: both machines report undefined behavior.
        have ha_ub : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.use (.move ⟨srcIdx, .nil⟩)), span⟩
            body.localDecls body.layouts = MirStepNode.fail .ub := by
          unfold evalStmt
          simp [evalRvalue, evalOperand, hslot_src]
        have hm_err : Miri.Interpreter.Step.evalStatement
            (annealStepHooks body.localDecls body.layouts) ()
            (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.use (.move ⟨srcIdx, .nil⟩)), span⟩) m =
            ({ m₀ with stack := ⟨#[topFrame₁]⟩ },
              .error (.undefinedBehavior "read of uninitialized local")) := by
          have hAR : (annealEvalOperand body.localDecls body.layouts (.Move ⟨srcIdx, #[]⟩)
              (some (translateTy dstDecl.ty body.layouts)) >>= annealReadImmediate) m₀ =
              .error (.undefinedBehavior "read of uninitialized local")
                { m₀ with stack := ⟨#[topFrame₁]⟩ } := by
            rw [EStateM.bind_eq_ok hop]
            rfl
          rw [hm_eval]
          unfold Miri.Interpreter.runRvalue
          rw [EStateM.bind_eq_error hAR]
        rw [ha_ub, miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq hbb
          hstmt hm_err]
        exact .ub _ _
      · -- Initialized source: both machines move the value into `_d`.
        obtain ⟨hread, _⟩ := annealReadImmediate_of_immediateRel himmRel hsz
          (translateTy srcDecl.ty body.layouts) { m₀ with stack := ⟨#[topFrame₁]⟩ }
        have hm_op : (annealEvalOperand body.localDecls body.layouts (.Move ⟨srcIdx, #[]⟩)
            (some (translateTy dstDecl.ty body.layouts)) >>= annealReadImmediate) m₀ =
            .ok ⟨imm, translateTy srcDecl.ty body.layouts⟩ { m with stack := ⟨#[topFrame₁]⟩ } := by
          rw [EStateM.bind_eq_ok hop, hread]
        have hm_write : Miri.Interpreter.Step.evalStatement
            (annealStepHooks body.localDecls body.layouts) ()
            (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.use (.move ⟨srcIdx, .nil⟩)), span⟩) m =
            Miri.Interpreter.runRvalue (annealWriteImmediate imm destPlace)
              { m with stack := ⟨#[topFrame₁]⟩ } := by
          rw [hm_eval]
          apply runRvalue_eq_of_eq
          exact EStateM.bind_eq_ok hm_op
        have ha_ok : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.use (.move ⟨srcIdx, .nil⟩)), span⟩
            body.localDecls body.layouts =
            match get? (s.frame.locals.set srcIdx .uninit) dstIdx with
            | .some .dead => MirStepNode.fail .ub
            | .some _ =>
              match set? (s.frame.locals.set srcIdx .uninit) dstIdx (.init v) with
              | .some locals₂ => MirStepNode.step (advanceStmt s locals₂ s.memory)
              | .none => MirStepNode.fail .ub
            | .none => MirStepNode.fail .ub := by
          unfold evalStmt
          dsimp only
          have huse : evalRvalue s.frame.locals (.use (.move ⟨srcIdx, .nil⟩)) s.memory
              body.localDecls body.layouts = .ok v (s.frame.locals.set srcIdx .uninit) s.memory := by
            unfold evalRvalue
            dsimp only
            rw [hbor, hcaller]
            simp [evalOperand, hslot_src, set?_eq_some_set hlt_af_src]
          rw [huse]
          dsimp only
          rw [hprot, hbor]
          dsimp only [invalidateConflictingBorrows]
          rw [hmem_same]
          rfl
        have hnew : LocalRel m.machine srcDecl body.layouts .uninit
            { (cacheFrameLocalLayout topFrame₀ srcIdx hlt_src
                (translateTy srcDecl.ty body.layouts)).locals[srcIdx]'hlt_src' with
              value := .live (.immediate .uninit) } := by
          have hlay : ((cacheFrameLocalLayout topFrame₀ srcIdx hlt_src
              (translateTy srcDecl.ty body.layouts)).locals[srcIdx]'hlt_src').layout =
              some (translateTy srcDecl.ty body.layouts) := by
            simp [cacheFrameLocalLayout]
          exact .immediate .uninit .uninit _
            (by rw [hlay]; intro l hl; exact (Option.some.inj hl).symm) (Or.inl ⟨rfl, rfl⟩)
        have hframe₁ : FrameRel body m.machine
            { s.frame with locals := s.frame.locals.set srcIdx .uninit } topFrame₁ :=
          (hframe₀.cache_local_layout hdecl_src hlt_src).update_local hdecl_src .uninit
            (.live (.immediate .uninit)) hnew
        have hdisj₁ : MemoryAllocDisjoint topFrame₁ := by
          apply MemoryAllocDisjoint.mono_immediate (tf := topFrame₀) hdisj₀
          intro k
          by_cases hk : k = srcIdx
          · subst hk
            right
            exact ⟨.uninit, some (translateTy srcDecl.ty body.layouts), by
              simp [topFrame₁, deinitFrameLocal, cacheFrameLocalLayout]⟩
          · left
            simp [topFrame₁, deinitFrameLocal, cacheFrameLocalLayout,
              Array.getElem?_set_ne _ (Ne.symm hk)]
        have hmono₁ : ∀ j, IsImmediateFrameLocal topFrame j → IsImmediateFrameLocal topFrame₁ j :=
          fun j hj => ((hmono₀ j hj).cache_layout hlt_src _).set_immediate hlt_src' .uninit
        have himmRel' : ImmediateRel dstDecl.ty body.layouts v imm := hty ▸ himmRel
        exact (write_after_rvalue_simulation_ext (tf₀ := topFrame) (topFrame₁ := topFrame₁)
          hretCont ⟨retLay, hretPlace⟩ hcal hstack hbor hprot hcaller
          hframes hframe.body_eq hframe.location_eq hmono₁ hbb hstmt hframe₁ hdisj₁
          hdecl_dst (hmono₁ dstIdx himm_dst) himmRel' ha_ok hm_write).1

/-! ## 5. Representation coalescing (`forceAllocation`) -/

/-- A successful `reserveAllocId` leaves the live allocations unchanged and
returns an `AllocId` that no live allocation uses. -/
theorem reserveAllocId_ok_live {mem mem' : AnnealMemory} {id : Miri.Memory.AllocId}
    (h : mem.reserveAllocId = (mem', .ok id)) :
    mem'.live = mem.live ∧ mem.live.any (fun entry => entry.1 == id) = false := by
  unfold Miri.Memory.MemoryState.reserveAllocId at h
  simp only [Id.run] at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · rename_i allocId _ hcont
          injection h with hmem hid
          injection hid with hid
          subst hid hmem
          refine ⟨by split <;> rfl, ?_⟩
          -- `containsId` (private) unfolds to this disjunction of public
          -- queries.
          have hc : ¬(mem.hasIssuedId allocId || mem.live.any (fun entry => entry.1 == allocId) ||
              mem.dead.any (fun entry => entry.allocId == allocId) ||
              mem.hasGlobalId allocId) = true := hcont
          simp only [Bool.or_eq_true, not_or] at hc
          exact Bool.eq_false_iff.mpr hc.1.1.2

/-! ### 5.1 `annealPlaceHooks` leaves -/

/-- `annealPlaceHooks.getFrame` returns the root frame and keeps the state. -/
theorem annealPlaceHooks_getFrame_eq {ld : List LocalDecl} {ly : LayoutTable}
    {m : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf]) :
    (annealPlaceHooks ld ly).getFrame m = .ok tf m := by
  simp only [annealPlaceHooks, get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind,
    stack_currentFrame?_singleton m.stack tf hframes, pure, EStateM.pure]

/-- `annealPlaceHooks.frameIndex` is `0` on a single-frame stack. -/
theorem annealPlaceHooks_frameIndex_eq {ld : List LocalDecl} {ly : LayoutTable}
    {m : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf]) :
    (annealPlaceHooks ld ly).frameIndex m = .ok 0 m := by
  simp only [annealPlaceHooks, get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind,
    pure, EStateM.pure, hframes]
  rfl

/-- `annealPlaceHooks.setFrame` replaces the root frame. -/
theorem annealPlaceHooks_setFrame_eq {ld : List LocalDecl} {ly : LayoutTable}
    {m : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf])
    (tf' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit) :
    (annealPlaceHooks ld ly).setFrame tf' m = .ok () { m with stack := ⟨#[tf']⟩ } := by
  rcases m with ⟨⟨frames⟩, machine⟩
  dsimp only at hframes
  subst hframes
  rfl

/-- `cacheFrameLocalLayout` is the identity when the same layout is already
cached. -/
theorem cacheFrameLocalLayout_of_cached
    (mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    {idx : Nat} (hlt : idx < mf.locals.size) {lay : Miri.Interpreter.LocalLayout}
    (hc : (mf.locals[idx]'hlt).layout = some lay) :
    cacheFrameLocalLayout mf idx hlt lay = mf := by
  unfold cacheFrameLocalLayout
  have hls : { mf.locals[idx]'hlt with layout := some lay } = mf.locals[idx]'hlt := by
    rw [← hc]
  rw [hls, array_set_self]

/-- `placeLayoutOfLocal` under `annealPlaceHooks` returns the declared layout
and memoizes it in the root frame. -/
theorem placeLayoutOfLocal_eq {body : CapturedMir} {m : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {idx : Nat} {decl : LocalDecl}
    (hframes : m.stack.frames = #[tf])
    (hlt : idx < tf.locals.size)
    (hdecl : get? body.localDecls idx = some decl)
    (hcache : ∀ l, (tf.locals[idx]'hlt).layout = some l → l = translateTy decl.ty body.layouts) :
    Miri.Interpreter.placeLayoutOfLocal (annealPlaceHooks body.localDecls body.layouts) () idx m =
      .ok (translateTy decl.ty body.layouts)
        { m with stack := ⟨#[cacheFrameLocalLayout tf idx hlt
            (translateTy decl.ty body.layouts)]⟩ } := by
  have hget : tf.getLocal idx = .ok (tf.locals[idx]'hlt) := by
    unfold Miri.Interpreter.Frame.getLocal
    simp [hlt, pure, Except.pure]
  unfold Miri.Interpreter.placeLayoutOfLocal
  simp only [bind, EStateM.bind, annealPlaceHooks_getFrame_eq hframes, hget,
    Miri.Interpreter.stackLift_ok, pure, EStateM.pure]
  cases hc : (tf.locals[idx]'hlt).layout with
  | some l =>
    have hl := hcache l hc
    subst hl
    simp only [cacheFrameLocalLayout_of_cached tf hlt hc]
    rw [stepState_with_same_singleton m tf hframes]
    rfl
  | none =>
    have hres : (annealPlaceHooks body.localDecls body.layouts).resolveLayout () idx m =
        .ok (translateTy decl.ty body.layouts) m := by
      simp only [annealPlaceHooks, lookupLocalDeclLayout, hdecl, pure, EStateM.pure]
    have hgor := frame_getOrCacheLocalLayout_eq tf hlt
      (computed := translateTy decl.ty body.layouts) (by rw [hc]; intro l hl; cases hl)
    simp only [EStateM.bind, hres, annealPlaceHooks_getFrame_eq hframes, hgor,
      Miri.Interpreter.stackLift_ok, pure, EStateM.pure, annealPlaceHooks_setFrame_eq hframes]

/-- The machine after `annealPlaceHooks.allocateStack` records the fresh
allocation `(id, alloc)` and caches its base address. -/
def stackAllocMachine (mach : AnnealMachine) (mem' : AnnealMemory) (id : Miri.Memory.AllocId)
    (alloc : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)) :
    AnnealMachine :=
  { mach with
    memory := { mem' with live := mem'.live.push (id, ⟨.stack, alloc⟩) }
    addresses := { mach.addresses with
      baseAddr := #[⟨id, annealStackBaseAddr id⟩] ++ mach.addresses.baseAddr } }

/-- The memory place that `annealPlaceHooks.allocateStack` returns for `id`. -/
def stackAllocPlace (id : Miri.Memory.AllocId) : Miri.Interpreter.MemPlace AnnealProv :=
  ⟨⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr id), some (.concrete id Miri.Memory.BorTag.one)⟩,
    .none, none⟩

/-- `stackAllocMachine` caches `annealStackBaseAddr id` as the base address of
`id`. -/
theorem lookupBaseAddr_stackAllocMachine_self (mach : AnnealMachine) (mem' : AnnealMemory)
    (id : Miri.Memory.AllocId)
    (alloc : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)) :
    (stackAllocMachine mach mem' id alloc).lookupBaseAddr id = some (annealStackBaseAddr id) := by
  simp [stackAllocMachine, AnnealMachine.lookupBaseAddr, Array.find?_append]

/-- `stackAllocMachine` keeps the base address of every other allocation. -/
theorem lookupBaseAddr_stackAllocMachine_ne (mach : AnnealMachine) (mem' : AnnealMemory)
    {id a : Miri.Memory.AllocId}
    (alloc : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree))
    (hne : a ≠ id) :
    (stackAllocMachine mach mem' id alloc).lookupBaseAddr a = mach.lookupBaseAddr a := by
  have hne' : (id == a) = false := beq_false_of_ne (Ne.symm hne)
  simp [stackAllocMachine, AnnealMachine.lookupBaseAddr, Array.find?_append, hne']

/-- Inversion of a successful `annealPlaceHooks.allocateStack`. -/
theorem annealPlaceHooks_allocateStack_inv {ld : List LocalDecl} {ly : LayoutTable}
    {m m' : AnnealStepState} {layout : Miri.Interpreter.LocalLayout}
    {r : Miri.Interpreter.MPlaceTy AnnealProv}
    (h : (annealPlaceHooks ld ly).allocateStack () layout m = .ok r m') :
    ∃ (allocation : Miri.Memory.Allocation AnnealProv Unit) (mem' : AnnealMemory)
      (id : Miri.Memory.AllocId),
      Miri.Memory.Allocation.tryNew layout.layout.size layout.layout.align.abi .Uninit
        annealZeroedStorage = .ok allocation ∧
      m.machine.memory.reserveAllocId = (mem', .ok id) ∧
      r = ⟨stackAllocPlace id, layout⟩ ∧
      m' = { m with machine := stackAllocMachine m.machine mem' id (allocation.withExtra none) } := by
  simp only [annealPlaceHooks] at h
  cases htry : Miri.Memory.Allocation.tryNew layout.layout.size layout.layout.align.abi .Uninit
      annealZeroedStorage with
  | error e =>
    simp [htry, bind, EStateM.bind, throw, throwThe, MonadExceptOf.throw, EStateM.throw] at h
  | ok allocation =>
    cases hres : m.machine.memory.reserveAllocId with
    | mk mem' reserved =>
      cases reserved with
      | error e =>
        simp [htry, hres, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, pure,
          EStateM.pure, throw, throwThe, MonadExceptOf.throw, EStateM.throw] at h
      | ok id =>
        simp [htry, hres, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, set,
          MonadStateOf.set, EStateM.set, pure, EStateM.pure] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨allocation, mem', id, rfl, rfl, rfl, rfl⟩

/-- Overwriting the last element of `xs.push a` with `b` gives `xs.push b`. -/
theorem array_push_set!_size {α : Type} (xs : Array α) (a b : α) :
    (xs.push a).set! xs.size b = xs.push b := by
  rw [Array.set!_eq_setIfInBounds]
  apply Array.ext
  · simp [Array.size_setIfInBounds]
  · intro i h₁ h₂
    rw [Array.getElem_setIfInBounds (by simpa [Array.size_setIfInBounds] using h₁)]
    simp only [Array.getElem_push]
    by_cases hi : xs.size = i
    · subst hi; simp
    · have hlt : i < xs.size := by
        simp [Array.size_setIfInBounds] at h₁; omega
      simp [hi, hlt]

/-- `findIdx?` locates a key that is absent from `xs` at the position where it
was pushed. -/
theorem findIdx?_push_fresh {β : Type} (xs : Array (Miri.Memory.AllocId × β))
    (id : Miri.Memory.AllocId) (b : β)
    (hfresh : xs.any (fun entry => entry.1 == id) = false) :
    (xs.push (id, b)).findIdx? (fun x => x.1 == id) = some xs.size := by
  rw [Array.findIdx?_push]
  have hnone : xs.findIdx? (fun x => x.1 == id) = none := by
    rw [Array.findIdx?_eq_none_iff]
    intro x hx
    obtain ⟨i, hi, hxi⟩ := Array.mem_iff_getElem.mp hx
    have := (Array.any_eq_false.mp hfresh) i hi
    subst hxi
    simpa using this
  simp [hnone]

/-- Inversion of a successful `annealPlaceHooks.writeMemoryNoValidate` of an
initialized immediate into the fresh allocation `id`: it is a scalar, and
`Allocation.writeScalar` at allocation-relative offset zero succeeded. -/
theorem annealPlaceHooks_writeMemoryNoValidate_fresh_inv {ld : List LocalDecl} {ly : LayoutTable}
    {m m₂ : AnnealStepState} {mem' : AnnealMemory} {id : Miri.Memory.AllocId}
    {a0 : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    {layout : Miri.Interpreter.LocalLayout} {value : Miri.Interpreter.Immediate AnnealProv}
    (hfresh : mem'.live.any (fun entry => entry.1 == id) = false)
    (hval : value ≠ .uninit)
    (h : (annealPlaceHooks ld ly).writeMemoryNoValidate () value ⟨stackAllocPlace id, layout⟩
      { m with machine := stackAllocMachine m.machine mem' id a0 } = .ok () m₂) :
    ∃ s alloc', value = .scalar s ∧
      Miri.Memory.Allocation.writeScalar annealTargetDataLayout
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO s.size) s a0 = .ok () alloc' ∧
      m₂ = { m with machine := stackAllocMachine m.machine mem' id alloc' } := by
  have hbase := lookupBaseAddr_stackAllocMachine_self m.machine mem' id a0
  have hidx := findIdx?_push_fresh mem'.live id
    ({ kind := .stack, allocation := a0 } : Miri.Memory.LocalAllocation AnnealProv
      (Option Miri.TreeBorrows.BorrowTree) Miri.Memory.MiriMemoryKind) hfresh
  have hlive : (stackAllocMachine m.machine mem' id a0).memory.live =
      mem'.live.push (id, ⟨.stack, a0⟩) := rfl
  simp only [annealPlaceHooks] at h
  have hoff : Miri.ABI.Size.ofBytes
      ((Miri.ABI.Size.ofBytes (annealStackBaseAddr id)).bytes - annealStackBaseAddr id) =
      Miri.ABI.Size.ZERO := by
    simp [Miri.ABI.Size.ofBytes, Miri.ABI.Size.ZERO]
  simp only [bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, stackAllocPlace,
    Option.bind, Miri.Memory.Provenance.getAllocId, hbase, hlive, hidx,
    Array.getElem?_push_size, hoff] at h
  cases value with
  | uninit => exact absurd rfl hval
  | scalarPair s₁ s₂ =>
    simp [EStateM.bind, throw, throwThe, MonadExceptOf.throw, EStateM.throw] at h
  | scalar s =>
    cases hw : Miri.Memory.Allocation.writeScalar annealTargetDataLayout
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO s.size) s a0 with
    | error e a' =>
      simp [EStateM.bind, hw, throw, throwThe, MonadExceptOf.throw, EStateM.throw] at h
    | ok u alloc' =>
      simp only [EStateM.bind, hw, pure, EStateM.pure, set, MonadStateOf.set, EStateM.set,
        array_push_set!_size] at h
      refine ⟨s, alloc', rfl, by rw [hw], ?_⟩
      injection h with _ h
      rw [← h]
      rfl

/-- `annealStackBaseAddr` satisfies every alignment of at most `2^29` bytes. -/
theorem annealStackBaseAddr_isAligned (id : Miri.Memory.AllocId) (align : Miri.ABI.Align)
    (h : align.pow2 ≤ 29) :
    (Miri.ABI.Size.ofBytes (annealStackBaseAddr id)).isAligned align = .ok true := by
  have hp : ¬ align.pow2 ≥ 64 := by omega
  unfold Miri.ABI.Size.isAligned Miri.ABI.Align.bytes
  simp only [hp, ↓reduceIte, bind, Except.bind, pure, Except.pure, Miri.ABI.Size.ofBytes]
  congr 1
  rw [beq_iff_eq]
  apply UInt64.toNat_inj.mp
  show ((annealStackBaseAddr id) &&& ((1 : UInt64) <<< (UInt64.ofNat align.pow2) - 1)).toNat = 0
  rw [UInt64.toNat_and]
  have hpow : (1 : UInt64) <<< (UInt64.ofNat align.pow2) = UInt64.ofNat (2 ^ align.pow2) := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_shiftLeft]
    have hlt : align.pow2 < 64 := by omega
    have hlt' : align.pow2 % 2 ^ 64 = align.pow2 := Nat.mod_eq_of_lt (by
      calc align.pow2 < 64 := hlt
        _ < 2 ^ 64 := by decide)
    have hlt64 : 2 ^ align.pow2 < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) (by omega)
    simp [hlt', Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt hlt64, Nat.one_shiftLeft]
  have h1 : ((1 : UInt64) <<< (UInt64.ofNat align.pow2) - 1).toNat = 2 ^ align.pow2 - 1 := by
    rw [hpow]
    have hpos : 1 ≤ 2 ^ align.pow2 := Nat.one_le_two_pow
    have hlt64 : 2 ^ align.pow2 < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) (by omega)
    rw [UInt64.toNat_sub_of_le]
    · simp [UInt64.toNat_ofNat, Nat.mod_eq_of_lt hlt64]
    · rw [UInt64.le_iff_toNat_le]
      simp [UInt64.toNat_ofNat, Nat.mod_eq_of_lt hlt64, hpos]
  have h2 : (annealStackBaseAddr id).toNat = (id.value.toNat * 2 ^ 32) % 2 ^ 64 := by
    unfold annealStackBaseAddr
    rw [UInt64.toNat_shiftLeft]
    simp [Nat.shiftLeft_eq]
  rw [h1, h2, Nat.and_two_pow_sub_one_eq_mod]
  have hdvd : 2 ^ align.pow2 ∣ 2 ^ 64 := Nat.pow_dvd_pow 2 (by omega)
  rw [Nat.mod_mod_of_dvd _ hdvd]
  apply Nat.mod_eq_zero_of_dvd
  exact Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega)) (Nat.dvd_mul_left (2 ^ 32) _)

/-! ### 5.2 Machine monotonicity -/

/-- `MemPlaceRel` depends on the machine only through the live allocation it
names and that allocation's cached base address. -/
theorem MemPlaceRel.of_live_base {mach mach' : AnnealMachine} {ty : Ty} {layouts : LayoutTable}
    {optVal : Option Value} {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hlive : ∀ e, e ∈ mach.memory.live.toList → e ∈ mach'.memory.live.toList)
    (hbase : ∀ a la, (a, la) ∈ mach.memory.live.toList →
      mach'.lookupBaseAddr a = mach.lookupBaseAddr a)
    (h : MemPlaceRel mach ty layouts optVal mp) :
    MemPlaceRel mach' ty layouts optVal mp := by
  cases h with
  | mk allocId tag baseAddr relOffset localAlloc hprov hmis hmeta hl hb hovf hptr hmut halign
      hbounds huninit hval hscalar =>
    exact .mk allocId tag baseAddr relOffset localAlloc hprov hmis hmeta (hlive _ hl)
      (by rw [hbase _ _ hl]; exact hb) hovf hptr hmut halign hbounds huninit hval hscalar

/-- `MemPlaceRel.of_live_base` lifted to `LocalRel`. -/
theorem LocalRel.of_live_base {mach mach' : AnnealMachine} {decl : LocalDecl}
    {layouts : LayoutTable} {slot : LocalSlot}
    {mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout}
    (hlive : ∀ e, e ∈ mach.memory.live.toList → e ∈ mach'.memory.live.toList)
    (hbase : ∀ a la, (a, la) ∈ mach.memory.live.toList →
      mach'.lookupBaseAddr a = mach.lookupBaseAddr a)
    (h : LocalRel mach decl layouts slot mls) :
    LocalRel mach' decl layouts slot mls := by
  cases h with
  | dead c hc => exact .dead c hc
  | immediate slot imm c hc hv => exact .immediate slot imm c hc hv
  | indirect slot mp c hc hne hmp =>
    exact .indirect slot mp c hc hne (hmp.of_live_base hlive hbase)

/-- `MemPlaceRel.of_live_base` lifted to `FrameRel`. -/
theorem FrameRel.of_live_base {body : CapturedMir} {mach mach' : AnnealMachine}
    {af : StackFrame} {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hlive : ∀ e, e ∈ mach.memory.live.toList → e ∈ mach'.memory.live.toList)
    (hbase : ∀ a la, (a, la) ∈ mach.memory.live.toList →
      mach'.lookupBaseAddr a = mach.lookupBaseAddr a)
    (h : FrameRel body mach af mf) :
    FrameRel body mach' af mf :=
  ⟨h.body_eq, h.location_eq, h.af_locals_len, h.mf_locals_size,
    fun i d sl ml hd hs hm => (h.locals_rel i d sl ml hd hs hm).of_live_base hlive hbase⟩

/-- Every allocation live before `allocateStack` stays live, keeps its base
address, and differs from the fresh allocation. -/
theorem stackAllocMachine_live_base {mach : AnnealMachine} {mem' : AnnealMemory}
    {id : Miri.Memory.AllocId}
    (alloc : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree))
    (hres : mach.memory.reserveAllocId = (mem', .ok id)) :
    (∀ e, e ∈ mach.memory.live.toList →
      e ∈ (stackAllocMachine mach mem' id alloc).memory.live.toList) ∧
    (∀ a la, (a, la) ∈ mach.memory.live.toList → a ≠ id) ∧
    (∀ a la, (a, la) ∈ mach.memory.live.toList →
      (stackAllocMachine mach mem' id alloc).lookupBaseAddr a = mach.lookupBaseAddr a) := by
  obtain ⟨hlive_eq, hfresh⟩ := reserveAllocId_ok_live hres
  have hne : ∀ a la, (a, la) ∈ mach.memory.live.toList → a ≠ id := by
    intro a la hmem heq
    subst heq
    obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hmem
    have := (Array.any_eq_false.mp hfresh) i (by simpa using hi)
    simp only [Array.getElem_toList] at hget
    rw [hget] at this
    simp at this
  refine ⟨?_, hne, ?_⟩
  · intro e he
    simp only [stackAllocMachine, Array.toList_push, List.mem_append, hlive_eq]
    exact Or.inl he
  · intro a la hmem
    exact lookupBaseAddr_stackAllocMachine_ne mach mem' alloc (hne a la hmem)

/-- `EStateM.bind x f` continues with `f` when `x` succeeds. -/
theorem EStateM.bind_apply_ok {ε σ α β : Type} {x : EStateM ε σ α} {f : α → EStateM ε σ β}
    {s s' : σ} {a : α} (h : x s = .ok a s') :
    EStateM.bind x f s = f a s' := by
  simp only [EStateM.bind, h]

/-- `EStateM.bind x f` propagates the error when `x` fails. -/
theorem EStateM.bind_apply_error {ε σ α β : Type} {x : EStateM ε σ α} {f : α → EStateM ε σ β}
    {s s' : σ} {e : ε} (h : x s = .error e s') :
    EStateM.bind x f s = .error e s' := by
  simp only [EStateM.bind, h]

/-- `annealPlaceHooks.afterLocalMovedToMemory` does nothing. -/
theorem annealPlaceHooks_afterLocalMovedToMemory_eq {ld : List LocalDecl} {ly : LayoutTable}
    (localId : Miri.MIR.LocalId) (p : Miri.Interpreter.MPlaceTy AnnealProv) (st : AnnealStepState) :
    (annealPlaceHooks ld ly).afterLocalMovedToMemory () localId p st = .ok () st := rfl

/-- `annealPlaceHooks_getFrame_eq` for an explicitly constructed state. -/
theorem annealPlaceHooks_getFrame_mk {ld : List LocalDecl} {ly : LayoutTable}
    (tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    (mach : AnnealMachine) :
    (annealPlaceHooks ld ly).getFrame ⟨⟨#[tf]⟩, mach⟩ = .ok tf ⟨⟨#[tf]⟩, mach⟩ := rfl

/-- `annealPlaceHooks_setFrame_eq` for an explicitly constructed state. -/
theorem annealPlaceHooks_setFrame_mk {ld : List LocalDecl} {ly : LayoutTable}
    (tf tf' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    (mach : AnnealMachine) :
    (annealPlaceHooks ld ly).setFrame tf' ⟨⟨#[tf]⟩, mach⟩ = .ok () ⟨⟨#[tf']⟩, mach⟩ := rfl

/-- A successful `Frame.getLocalOperand` reads a live local. -/
theorem frame_getLocalOperand_ok
    {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {idx : Nat} {op : Miri.Interpreter.Operand AnnealProv}
    (h : mf.getLocalOperand idx = .ok op) :
    ∃ hlt : idx < mf.locals.size, (mf.locals[idx]'hlt).value = .live op := by
  unfold Miri.Interpreter.Frame.getLocalOperand Miri.Interpreter.Frame.getLocal at h
  by_cases hlt : idx < mf.locals.size
  · refine ⟨hlt, ?_⟩
    simp only [hlt, ↓reduceDIte, bind, Except.bind, pure, Except.pure] at h
    unfold Miri.Interpreter.LocalState.access at h
    cases hv : (mf.locals[idx]'hlt).value with
    | dead => simp [hv, Except.mapError] at h
    | live op' =>
      simp [hv, Except.mapError] at h
      rw [h]
  · simp [hlt, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h

/-- `Frame.setLocalOperand` on a live local replaces its operand and keeps its
cached layout. -/
theorem frame_setLocalOperand_live
    {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {idx : Nat} {old : Miri.Interpreter.Operand AnnealProv}
    (hlt : idx < mf.locals.size)
    (hlive : (mf.locals[idx]'hlt).value = .live old)
    (new : Miri.Interpreter.Operand AnnealProv) :
    mf.setLocalOperand idx new =
      .ok { mf with
        locals := mf.locals.set idx { mf.locals[idx]'hlt with value := .live new } hlt } := by
  have hgo : mf.getLocalOperand idx = .ok old := by
    unfold Miri.Interpreter.Frame.getLocalOperand Miri.Interpreter.Frame.getLocal
      Miri.Interpreter.LocalState.access
    simp [hlt, hlive, bind, Except.bind, pure, Except.pure, Except.mapError]
  unfold Miri.Interpreter.Frame.setLocalOperand
  simp only [hgo, bind, Except.bind, frame_replaceLocalValue_of_lt mf idx hlt]

/-- A memory-backed local related by `FrameRel` points into a live
allocation. -/
theorem FrameRel.indirect_allocId {body : CapturedMir} {mach : AnnealMachine}
    {af : StackFrame} {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hfr : FrameRel body mach af mf) {j : Nat} {mp : Miri.Interpreter.MemPlace AnnealProv}
    {lay : Option Miri.Interpreter.LocalLayout}
    (hj : mf.locals[j]? = some ⟨.live (.indirect mp), lay⟩) :
    ∃ a la, mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId = some a ∧
      (a, la) ∈ mach.memory.live.toList := by
  obtain ⟨hlt_j, _⟩ := Array.getElem?_eq_some_iff.mp hj
  have hlt_d : j < body.localDecls.length := by rw [← hfr.mf_locals_size]; exact hlt_j
  have hdecl : get? body.localDecls j = some (body.localDecls[j]'hlt_d) :=
    List.getElem?_eq_getElem hlt_d
  obtain ⟨slot, mls, _, _, _, hmls, _, hloc⟩ := hfr.lookup_local hdecl
  rw [hj] at hmls
  cases hmls
  cases hloc with
  | indirect _ _ _ _ _ hmp =>
    obtain ⟨allocId, tag, _, _, localAlloc, hprov, _, _, hl, _⟩ := hmp
    exact ⟨allocId, localAlloc, by rw [hprov]; rfl, hl⟩

/-- A live immediate local related by `LocalRel` has a non-dead slot that is
either uninitialized (with the `.uninit` immediate) or holds a value related by
`ImmediateRel`. -/
theorem LocalRel.immediate_cases {mach : AnnealMachine} {decl : LocalDecl}
    {layouts : LayoutTable} {slot : LocalSlot}
    {imm : Miri.Interpreter.Immediate AnnealProv} {c : Option Miri.Interpreter.LocalLayout}
    (h : LocalRel mach decl layouts slot ⟨.live (.immediate imm), c⟩) :
    slot ≠ .dead ∧
      ((slot = .uninit ∧ imm = .uninit) ∨
        ∃ v, slot = .init v ∧ ImmediateRel decl.ty layouts v imm) := by
  cases h with
  | immediate _ _ _ _ hv =>
    refine ⟨?_, hv⟩
    rintro rfl
    rcases hv with ⟨h, _⟩ | ⟨_, h, _⟩ <;> cases h

/-- `MemPlaceRel` for the fresh allocation `id` holding `alloc'`, from facts
about `alloc'` alone. -/
theorem stackAlloc_memPlaceRel {mach : AnnealMachine} {mem' : AnnealMemory}
    {id : Miri.Memory.AllocId}
    {alloc' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    {ty : Ty} {layouts : LayoutTable} {optVal : Option Value}
    (hmut : alloc'.mutability = .Mut)
    (halign : (translateTy ty layouts).layout.align.abi.pow2 ≤ 29)
    (hsize : alloc'.byteSize = (translateTy ty layouts).layout.size)
    (huninit : optVal = none → (translateTy ty layouts).layout.size ≠ Miri.ABI.Size.ZERO →
      alloc'.initializationMask.isRangeInitialized
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateTy ty layouts).layout.size) ≠
          .ok (.ok ()))
    (hval : ∀ v, optVal = some v →
      (translateTy ty layouts).layout.size ≠ Miri.ABI.Size.ZERO →
      alloc'.initializationMask.isRangeInitialized
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateTy ty layouts).layout.size) =
          .ok (.ok ()))
    (hscalar : ∀ sc, optVal = some (.scalar sc) →
      (translateTy ty layouts).layout.size = translateSizeBytes sc.sizeBytes ∧
      (ty.kind = .bool → sc.sizeBytes = 1 ∧ (sc.bits = 0 ∨ sc.bits = 1)) ∧
      (ty.kind = .char → sc.sizeBytes = 4 ∧ isValidCharCode sc.bits = true) ∧
      ∃ msc, ScalarRel sc msc ∧
        alloc'.readScalar annealTargetDataLayout
          (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateTy ty layouts).layout.size)
          false = .ok (.fromScalarInt msc)) :
    MemPlaceRel (stackAllocMachine mach mem' id alloc') ty layouts optVal (stackAllocPlace id) :=
  .mk id .one (annealStackBaseAddr id) Miri.ABI.Size.ZERO ⟨.stack, alloc'⟩ rfl rfl rfl
    (by simp [stackAllocMachine])
    (lookupBaseAddr_stackAllocMachine_self mach mem' id alloc')
    (by simpa [Miri.ABI.Size.ZERO] using UInt64.toNat_lt (annealStackBaseAddr id))
    (by simp [stackAllocPlace, Miri.ABI.Size.ZERO])
    hmut
    (annealStackBaseAddr_isAligned id _ halign)
    (by simp [Miri.ABI.Size.ZERO, hsize])
    huninit hval hscalar

/-- `StateRel` after `forceAllocation` moves the immediate local `idx` into the
fresh allocation `id`, given the new local's `LocalRel.indirect`. -/
theorem stackAlloc_stateRel
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hretCont : tf.returnContinuation = .stop false)
    (hretPlace : ∃ retLay, tf.returnPlace = .frameLocal 0 0 none retLay tf.localsIdentity)
    (hfr : FrameRel body m.machine s.frame tf)
    (hcal : s.memory.activeCallee = none) (hstack : s.memory.callStack = .nil)
    (hbor : s.memory.borrows = .nil) (hprot : s.memory.activeProtectors = .nil)
    (hcaller : s.memory.callerLocals = .nil)
    (hdisj : MemoryAllocDisjoint tf)
    {idx : Nat} {decl : LocalDecl} (hdecl : get? body.localDecls idx = some decl)
    (hlt : idx < tf.locals.size)
    {slot : LocalSlot} (hslot : get? s.frame.locals idx = some slot)
    {mem' : AnnealMemory} {id : Miri.Memory.AllocId}
    (hres : m.machine.memory.reserveAllocId = (mem', .ok id))
    {alloc' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    (hlt' : idx < (cacheFrameLocalLayout tf idx hlt
      (translateTy decl.ty body.layouts)).locals.size)
    (hnew : LocalRel (stackAllocMachine m.machine mem' id alloc') decl body.layouts slot
      { (cacheFrameLocalLayout tf idx hlt
          (translateTy decl.ty body.layouts)).locals[idx]'hlt' with
        value := .live (.indirect (stackAllocPlace id)) }) :
    StateRel body s
      { stack := ⟨#[{ cacheFrameLocalLayout tf idx hlt (translateTy decl.ty body.layouts) with
          locals := (cacheFrameLocalLayout tf idx hlt
            (translateTy decl.ty body.layouts)).locals.set idx
            { (cacheFrameLocalLayout tf idx hlt
                (translateTy decl.ty body.layouts)).locals[idx]'hlt' with
              value := .live (.indirect (stackAllocPlace id)) } hlt' }]⟩
        machine := stackAllocMachine m.machine mem' id alloc' } := by
  obtain ⟨hlive, hfreshne, hbase⟩ := stackAllocMachine_live_base (mach := m.machine) alloc' hres
  have hfr₁ := (hfr.cache_local_layout hdecl hlt).of_live_base hlive hbase
  have hfr₂ := hfr₁.update_local hdecl slot (.live (.indirect (stackAllocPlace id))) hnew
  have hset : s.frame.locals.set idx slot = s.frame.locals := by
    obtain ⟨hlt_s, hget⟩ := List.getElem_of_getElem? hslot
    rw [← hget, List.set_getElem_self]
  rw [hset] at hfr₂
  refine StateRel.mk _ rfl hretCont hretPlace hfr₂ hcal hstack hbor hprot hcaller ?_
  intro i j mp_i mp_j lay_i lay_j hij hi hj
  dsimp only at hi hj
  rw [Array.getElem?_set] at hi hj
  have hcf : ∀ k, idx ≠ k → (cacheFrameLocalLayout tf idx hlt
      (translateTy decl.ty body.layouts)).locals[k]? = tf.locals[k]? := by
    intro k hk
    unfold cacheFrameLocalLayout
    rw [Array.getElem?_set_ne _ hk]
  by_cases hi_idx : idx = i
  · subst hi_idx
    have hj_idx : idx ≠ j := hij
    simp only [hj_idx, ↓reduceIte] at hj
    rw [hcf j hj_idx] at hj
    simp only [↓reduceIte] at hi
    obtain ⟨a, la, ha, hla⟩ := hfr.indirect_allocId hj
    injection hi with hi
    injection hi with hv _
    injection hv with hv
    injection hv with hv
    subst hv
    rw [ha]
    simp only [stackAllocPlace, Option.bind, Miri.Memory.Provenance.getAllocId, ne_eq,
      Option.some.injEq]
    exact fun h => hfreshne a la hla h.symm
  · simp only [hi_idx, ↓reduceIte] at hi
    rw [hcf i hi_idx] at hi
    by_cases hj_idx : idx = j
    · subst hj_idx
      simp only [↓reduceIte] at hj
      obtain ⟨a, la, ha, hla⟩ := hfr.indirect_allocId hi
      injection hj with hj
      injection hj with hv _
      injection hv with hv
      injection hv with hv
      subst hv
      rw [ha]
      simp only [stackAllocPlace, Option.bind, Miri.Memory.Provenance.getAllocId, ne_eq,
        Option.some.injEq]
      exact hfreshne a la hla
    · simp only [hj_idx, ↓reduceIte] at hj
      rw [hcf j hj_idx] at hj
      exact hdisj i j mp_i mp_j lay_i lay_j hij hi hj

/-- Representation coalescing theorem: `Miri.Interpreter.forceAllocation` under
`annealPlaceHooks` preserves `StateRel` with the same Anneal state. A memory
place and an already memory-backed local are returned unchanged; an immediate
local moves into a fresh stack allocation that holds its value, and from then on
is related to the same `LocalSlot` by `LocalRel.indirect`. In either local case
the local afterwards is memory-backed at exactly the returned place. -/
theorem forceAllocation_preserves_StateRel
    {body : CapturedMir} {s : MachineState} {m m' : AnnealStepState}
    {place : Miri.Interpreter.RuntimePlace AnnealProv}
    {mplace : Miri.Interpreter.MPlaceTy AnnealProv}
    (hstate : StateRel body s m)
    (hforce : Miri.Interpreter.forceAllocation (annealPlaceHooks body.localDecls body.layouts) ()
      place m = .ok mplace m') :
    StateRel body s m' ∧
    ∀ frameIndex localId identity,
      place.ref = .local frameIndex localId none identity →
      ∃ tf' lay, m'.stack.frames = #[tf'] ∧
        tf'.locals[localId]? = some ⟨.live (.indirect mplace.mplace), lay⟩ := by
  rcases hstate with
    ⟨tf, hframes, hretCont, hretPlace, hfr, hcal, hstack, hbor, hprot, hcaller, hdisj⟩
  rcases place with ⟨ref, pl⟩
  cases ref with
  | memory mp =>
    have hm : Miri.Interpreter.forceAllocation (annealPlaceHooks body.localDecls body.layouts) ()
        ⟨.memory mp, pl⟩ m = .ok ⟨mp, pl⟩ m := rfl
    rw [hm] at hforce
    injection hforce with h₁ h₂
    subst h₁ h₂
    exact ⟨⟨tf, hframes, hretCont, hretPlace, hfr, hcal, hstack, hbor, hprot, hcaller, hdisj⟩,
      fun _ _ _ h => nomatch h⟩
  | «local» fi idx off ident =>
    unfold Miri.Interpreter.forceAllocation at hforce
    simp only [Miri.Interpreter.requireCurrent_eq,
      Miri.Interpreter.checkLocalIdentity_debugOff (annealPlaceHooks _ _) _ rfl,
      bind, EStateM.bind, annealPlaceHooks_frameIndex_eq hframes] at hforce
    by_cases hfi : fi ≠ 0
    · have hne : (0 != fi) = true := by simp [Ne.symm hfi]
      simp [hne, throw, throwThe, MonadExceptOf.throw, EStateM.throw] at hforce
    obtain rfl : fi = 0 := Decidable.of_not_not hfi
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, pure, EStateM.pure,
      annealPlaceHooks_getFrame_eq hframes] at hforce
    cases hgo : tf.getLocalOperand idx with
    | error e =>
      rw [hgo] at hforce
      cases hforce
    | ok old =>
      rw [hgo, Miri.Interpreter.stackLift_ok] at hforce
      obtain ⟨hlt, hval⟩ := frame_getLocalOperand_ok hgo
      have hlt_d : idx < body.localDecls.length := by rw [← hfr.mf_locals_size]; exact hlt
      obtain ⟨decl, hdecl⟩ : ∃ decl, get? body.localDecls idx = some decl :=
        ⟨_, List.getElem?_eq_getElem hlt_d⟩
      obtain ⟨slot, mls, hlt_af, hlt_mf, hslot, hmls, hmls_eq, hloc⟩ := hfr.lookup_local hdecl
      cases old with
      | indirect mp =>
        cases off with
        | some o =>
          simp [annealPlaceHooks, pure, EStateM.pure, EStateM.bind, throw, throwThe,
            MonadExceptOf.throw, EStateM.throw] at hforce
        | none =>
          simp only [pure, EStateM.pure, EStateM.bind] at hforce
          injection hforce with h₁ h₂
          subst h₁ h₂
          refine ⟨⟨tf, hframes, hretCont, hretPlace, hfr, hcal, hstack, hbor, hprot, hcaller,
            hdisj⟩, ?_⟩
          intro fi' li' id' href
          injection href with _ hli _ _
          subst hli
          refine ⟨tf, (tf.locals[idx]'hlt).layout, hframes, ?_⟩
          rw [Array.getElem?_eq_getElem hlt, ← hval]
      | immediate value =>
        have hcache : ∀ l, (tf.locals[idx]'hlt).layout = some l →
            l = translateTy decl.ty body.layouts := by
          rw [hmls_eq]; exact hloc.layout_eq
        simp only [pure, EStateM.pure] at hforce
        rw [EStateM.bind_apply_ok (placeLayoutOfLocal_eq hframes hlt hdecl hcache)] at hforce
        cases hsized : (translateTy decl.ty body.layouts).layout.isSized
        · simp [hsized, EStateM.bind, throw, throwThe, MonadExceptOf.throw, EStateM.throw] at hforce
        simp only [hsized, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hforce
        cases halloc : (annealPlaceHooks body.localDecls body.layouts).allocateStack ()
            (translateTy decl.ty body.layouts)
            { m with stack := ⟨#[cacheFrameLocalLayout tf idx hlt
              (translateTy decl.ty body.layouts)]⟩ } with
        | error e s' =>
          rw [EStateM.bind_apply_error halloc] at hforce
          cases hforce
        | ok r m₂ =>
          rw [EStateM.bind_apply_ok halloc] at hforce
          obtain ⟨allocation, mem', id, htry, hres, hr, hm₂⟩ :=
            annealPlaceHooks_allocateStack_inv halloc
          subst hr hm₂
          have hlt' : idx < (cacheFrameLocalLayout tf idx hlt
              (translateTy decl.ty body.layouts)).locals.size := by
            rw [cacheFrameLocalLayout_size]; exact hlt
          have hval' : ((cacheFrameLocalLayout tf idx hlt
              (translateTy decl.ty body.layouts)).locals[idx]'hlt').value =
              .live (.immediate value) := by
            simp [cacheFrameLocalLayout, hval]
          obtain ⟨hsz_eq, hmut, halign, huninit⟩ := freshStackAlloc_spec htry
          have hlay : ((cacheFrameLocalLayout tf idx hlt
              (translateTy decl.ty body.layouts)).locals[idx]'hlt').layout =
              some (translateTy decl.ty body.layouts) := by
            simp [cacheFrameLocalLayout]
          have hc : ∀ l ∈ ((cacheFrameLocalLayout tf idx hlt
              (translateTy decl.ty body.layouts)).locals[idx]'hlt').layout,
              l = translateTy decl.ty body.layouts := by
            rw [hlay]; intro l hl; exact (Option.some.inj hl).symm
          have hmv : mls.value = .live (.immediate value) := by rw [← hmls_eq]; exact hval
          rcases mls with ⟨mv, ml⟩
          dsimp only at hmv
          subst hmv
          obtain ⟨hne, hslotv⟩ := hloc.immediate_cases
          have hfresh := (reserveAllocId_ok_live hres).2
          rw [← (reserveAllocId_ok_live hres).1] at hfresh
          cases value with
          | uninit =>
            simp only [EStateM.bind, pure, EStateM.pure, annealPlaceHooks_afterLocalMovedToMemory_eq,
              annealPlaceHooks_getFrame_mk, frame_setLocalOperand_live hlt' hval',
              Miri.Interpreter.stackLift_ok, annealPlaceHooks_setFrame_mk] at hforce
            cases off with
            | some o =>
              simp [annealPlaceHooks, EStateM.bind, throw, throwThe, MonadExceptOf.throw,
                EStateM.throw] at hforce
            | none =>
              simp only [EStateM.bind, EStateM.pure] at hforce
              injection hforce with h₁ h₂
              subst h₁ h₂
              have hnew : LocalRel (stackAllocMachine m.machine mem' id (allocation.withExtra none))
                  decl body.layouts slot
                  { (cacheFrameLocalLayout tf idx hlt
                      (translateTy decl.ty body.layouts)).locals[idx]'hlt' with
                    value := .live (.indirect (stackAllocPlace id)) } := by
                refine .indirect slot (stackAllocPlace id) _ hc hne ?_
                apply stackAlloc_memPlaceRel hmut halign hsz_eq
                · intro _ hnz; exact huninit hnz
                · intro v hv hnz
                  rcases hslotv with ⟨rfl, _⟩ | ⟨v', rfl, himm⟩
                  · cases hv
                  · cases himm with
                    | unit hzero => exact absurd hzero hnz
                · intro sc hv
                  rcases hslotv with ⟨rfl, _⟩ | ⟨v', rfl, himm⟩
                  · cases hv
                  · cases himm with
                    | unit hzero => cases hv
              refine ⟨stackAlloc_stateRel hretCont hretPlace hfr hcal hstack hbor hprot hcaller hdisj
                hdecl hlt hslot hres hlt' hnew, ?_⟩
              intro fi' li' id' href
              injection href with _ hli _ _
              subst hli
              exact ⟨_, _, rfl, Array.getElem?_set_self hlt'⟩
          | scalar sc' =>
            cases hw : (annealPlaceHooks body.localDecls body.layouts).writeMemoryNoValidate ()
                (.scalar sc') ⟨stackAllocPlace id, translateTy decl.ty body.layouts⟩
                { stack := ⟨#[cacheFrameLocalLayout tf idx hlt (translateTy decl.ty body.layouts)]⟩,
                  machine := stackAllocMachine m.machine mem' id (allocation.withExtra none) } with
            | error e s' =>
              simp only [EStateM.bind, hw] at hforce
              cases hforce
            | ok u m₃ =>
              obtain ⟨s₀, alloc', hs₀, hws, hm₃⟩ :=
                annealPlaceHooks_writeMemoryNoValidate_fresh_inv (m := { m with
                  stack := ⟨#[cacheFrameLocalLayout tf idx hlt
                    (translateTy decl.ty body.layouts)]⟩ }) hfresh (by simp) hw
              injection hs₀ with hs₀
              subst hs₀ hm₃
              simp only [EStateM.bind, hw, pure, EStateM.pure,
                annealPlaceHooks_afterLocalMovedToMemory_eq,
                annealPlaceHooks_getFrame_mk, frame_setLocalOperand_live hlt' hval',
                Miri.Interpreter.stackLift_ok, annealPlaceHooks_setFrame_mk] at hforce
              cases off with
              | some o =>
                simp [annealPlaceHooks, EStateM.bind, throw, throwThe, MonadExceptOf.throw,
                  EStateM.throw] at hforce
              | none =>
                simp only [EStateM.bind, EStateM.pure] at hforce
                injection hforce with h₁ h₂
                subst h₁ h₂
                rcases hslotv with ⟨_, himm⟩ | ⟨v, rfl, himm⟩
                · cases himm
                · cases himm with
                  | scalar sc msc hrel hsz hbool hchar =>
                    have htry' : Miri.Memory.Allocation.tryNew (translateSizeBytes sc.sizeBytes)
                        (translateTy decl.ty body.layouts).layout.align.abi .Uninit
                        annealZeroedStorage = .ok allocation := by
                      rw [← hsz]; exact htry
                    obtain ⟨alloc'', hw'', hsize'', hmut'', hinit'', hread''⟩ :=
                      freshStackAlloc_writeScalar_readScalar hrel htry'
                    have halloc_eq : alloc' = alloc'' := by
                      have h := hws.symm.trans hw''
                      injection h
                    subst halloc_eq
                    have hnew : LocalRel (stackAllocMachine m.machine mem' id alloc')
                        decl body.layouts (.init (.scalar sc))
                        { (cacheFrameLocalLayout tf idx hlt
                            (translateTy decl.ty body.layouts)).locals[idx]'hlt' with
                          value := .live (.indirect (stackAllocPlace id)) } := by
                      refine .indirect (.init (.scalar sc)) (stackAllocPlace id) _ hc hne ?_
                      apply stackAlloc_memPlaceRel hmut'' halign (by rw [hsize'', hsz])
                      · intro h; cases h
                      · intro v hv hnz; rw [hsz]; exact hinit''
                      · intro sc₂ hv
                        injection hv with hv
                        injection hv with hv
                        subst hv
                        exact ⟨hsz, hbool, hchar, msc, hrel, by rw [hsz]; exact hread''⟩
                    refine ⟨stackAlloc_stateRel hretCont hretPlace hfr hcal hstack hbor hprot hcaller
                      hdisj hdecl hlt hslot hres hlt' hnew, ?_⟩
                    intro fi' li' id' href
                    injection href with _ hli _ _
                    subst hli
                    exact ⟨_, _, rfl, Array.getElem?_set_self hlt'⟩
          | scalarPair a b =>
            cases hw : (annealPlaceHooks body.localDecls body.layouts).writeMemoryNoValidate ()
                (.scalarPair a b) ⟨stackAllocPlace id, translateTy decl.ty body.layouts⟩
                { stack := ⟨#[cacheFrameLocalLayout tf idx hlt (translateTy decl.ty body.layouts)]⟩,
                  machine := stackAllocMachine m.machine mem' id (allocation.withExtra none) } with
            | error e s' =>
              simp only [EStateM.bind, hw] at hforce
              cases hforce
            | ok u m₃ =>
              obtain ⟨s₀, alloc', hs₀, _, _⟩ :=
                annealPlaceHooks_writeMemoryNoValidate_fresh_inv (m := { m with
                  stack := ⟨#[cacheFrameLocalLayout tf idx hlt
                    (translateTy decl.ty body.layouts)]⟩ }) hfresh (by simp) hw
              cases hs₀

/-! ## 6. Composed statement simulation -/

/-- Composed `LM-1.4` statement simulation: every statement that satisfies
`WellTypedLM1_4Stmt` in the root frame (`StorageLive`, `StorageDead` other than
`_0`, `PlaceMention` of a live local, and `_d = move _s` between immediate
locals) steps in lockstep under `StepRel`. -/
theorem step_stmt_lm1_4_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRel body s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {stmt : Statement}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some stmt)
    (hwt : ∀ topFrame, m.stack.frames = #[topFrame] → WellTypedLM1_4Stmt body topFrame stmt) :
    StepRel body m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  obtain ⟨tf, hframes, _, _, _, _, _, _, _, _, _⟩ := id hstate
  cases hwt tf hframes with
  | storageLive => exact step_storageLive_simulation hstate hphase hbb hstmt hwt
  | storageDead => exact step_storageDead_simulation hstate hphase hbb hstmt hwt
  | placeMention => exact step_placeMention_simulation hstate hphase hbb hstmt hwt
  | assignMove => exact evalOperand_move_simulation hstate hphase hbb hstmt hwt

end LeanMiriSpec.Correspondence
