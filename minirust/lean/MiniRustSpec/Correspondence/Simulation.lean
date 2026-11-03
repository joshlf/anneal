/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import MiniRustSpec.Correspondence.AnnealEval

/-!
# The correspondence theorem

`step_correspondence` states that, for every fragment body and every pair of
related states, one step of Anneal's trusted MIR semantics
(`Trusted.Rustc.V2026_06_01.MirSemantics.stepMirFn`) and one step of the
ground-truth MiniRust interpretation (`MiniRustSpec.Interp.step`, which
executes the MiniRust program that MiniRust's own `minimize` tool produces
for the body) agree in the sense of `StepRel`: both continue in related
states, both perform a related function return, or both raise UB.
`MiniRustSpec.Correspondence.Run` lifts this to whole executions.
-/

namespace MiniRustSpec.Correspondence

open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.Sequence
open MiniRustSpec
open MiniRustSpec.LibSpecr
open MiniRustSpec.Interp

/-! ## Facts about the fragment check and the translation -/

theorem mapM_option_spec {α β : Type} (f : α → Option β) (xs : List α) (ys : List β)
    (h : xs.mapM f = some ys) :
    ys.length = xs.length ∧ ∀ (k : Nat) x, xs[k]? = some x → ∃ y, f x = some y ∧ ys[k]? = some y := by
  induction xs generalizing ys with
  | nil => simp at h; subst h; simp
  | cons x xs ih =>
    simp only [List.mapM_cons, Option.bind_eq_bind] at h
    cases hx : f x with
    | none => simp [hx] at h
    | some y =>
      cases hxs : xs.mapM f with
      | none => simp [hx, hxs] at h
      | some ys' =>
        simp [hx, hxs] at h
        subst h
        obtain ⟨hlen, hget⟩ := ih ys' hxs
        refine ⟨by simp [hlen], fun k x' hk => ?_⟩
        cases k with
        | zero => simp at hk; subst hk; exact ⟨y, hx, rfl⟩
        | succ k => simp at hk; simpa using hget k x' hk

theorem translateBlock_spec (decls : List LocalDecl) (bb : BasicBlockData) (tb : Gen.BasicBlock)
    (h : translateBlock decls bb = some tb) :
    tb.statements.length = bb.statements.length ∧
    (∀ (k : Nat) st, bb.statements[k]? = some st →
      ∃ st', translateStatement st = some st' ∧ tb.statements[k]? = some st') ∧
    translateTerminator decls bb.terminator = some tb.terminator := by
  simp only [translateBlock, Option.bind_eq_bind] at h
  cases hs : bb.statements.mapM translateStatement with
  | none => simp [hs] at h
  | some stmts =>
    cases ht : translateTerminator decls bb.terminator with
    | none => simp [hs, ht] at h
    | some term =>
      simp [hs, ht] at h
      subst h
      obtain ⟨hlen, hget⟩ := mapM_option_spec translateStatement bb.statements stmts hs
      exact ⟨hlen, hget, rfl⟩

/-- Facts about a body accepted by `inFragment`. -/
theorem inFragment_spec (body : CapturedMir) (h : inFragment body = true) :
    body.phase = .runtimePostCleanup ∧ body.localDecls.length = body.argCount + 1 ∧
    (∀ bb ∈ body.basicBlocks, bb.isCleanup = false ∧
      (∀ st ∈ bb.statements, statementOk body.localDecls st = true) ∧
      terminatorOk body.localDecls body.basicBlocks.length bb.terminator = true) := by
  simp only [inFragment, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.not_eq_true']
    at h
  obtain ⟨⟨⟨⟨⟨hphase, hlen⟩, _⟩, _⟩, hbbs⟩, _⟩ := h
  refine ⟨?_, hlen, fun bb hbb => ?_⟩
  · unfold CapturedMir.isRuntimePostCleanup at hphase
    split at hphase <;> simp_all
  · obtain ⟨⟨hc, hst⟩, ht⟩ := hbbs bb hbb
    exact ⟨hc, hst, ht⟩

/-! ## One MiniRust step on a related machine -/

/-- The machine after `reset_data_race_tracking` and the (unique) thread pick. -/
def resetPick (m : Mach) : Mach := { m with mem := { m.mem with accesses := [] }, active_thread := 0 }

theorem resetPick_shape {m : Mach} {ctx : Ctx} {frames : List Frame} {allocs : List Gen.Allocation}
    (h : Shape m ctx frames allocs) : Shape (resetPick m) ctx frames allocs :=
  ⟨h.threads, rfl, h.allocs⟩

theorem step_callee {m : Mach} {ctx : Ctx} {f : Gen.Function} {n blk stmt : Nat}
    {allocs : List Gen.Allocation}
    (h : Shape m ctx [ctx.caller, calleeFrame f ctx n blk stmt] allocs) (tb : Gen.BasicBlock)
    (htb : mapGet f.blocks (bbName blk) = some tb) :
    Interp.step m = (do
      let m' ← if (stmt : Int) = (tb.statements.length : Int) then
          evalTerminator (resetPick m) tb.terminator
        else do
          let st ← listIndex tb.statements (stmt : Int) "block.statements[frame.next_stmt]"
          let m' ← evalStatement (resetPick m) st
          mutateCurFrame m' (fun fr => { fr with next_stmt := fr.next_stmt + 1 })
      CM.check_data_races m'.mem m'.active_thread (setInsert m.synchronized_threads 0, m.mem.accesses)
      pure m') := by
  have hany : m.threads.any (fun t => decide (t.state = .Enabled)) = true := by
    simp [h.threads, thread1]
  have hpick : ∀ mm : Mach, mm.threads = m.threads → pickActiveThread mm = .ok 0 :=
    fun mm hmm => pick_eq (hmm.trans h.threads)
  have hcur : ∀ mm : Mach, mm.threads = m.threads → mm.active_thread = 0 →
      curFrame mm = .ok (calleeFrame f ctx n blk stmt) :=
    fun mm hmm hact => curFrame_eq ⟨hmm.trans h.threads, hact, rfl⟩
  simp only [Interp.step, hany, Bool.not_true, Bool.false_eq_true, ↓reduceIte, resetDataRaceTracking,
    h.active]
  rw [hpick { m with mem := { memory := m.mem.memory, accesses := [] }, active_thread := 0 } rfl]
  simp only [ok_bind]
  rw [hcur { m with mem := { memory := m.mem.memory, accesses := [] }, active_thread := 0 } rfl rfl]
  simp only [ok_bind, mapIndex, calleeFrame, htb]
  rfl

/-- `ConcurrentMemory::check_data_races` passes after any step that leaves
thread `0` active: the previous step's synchronized set always contains the
previously active thread, here also thread `0`. -/
theorem check_after {m m' : Mach} {ctx : Ctx} {frames : List Frame} {allocs : List Gen.Allocation}
    (h' : Shape m' ctx frames allocs) :
    CM.check_data_races m'.mem m'.active_thread (setInsert m.synchronized_threads 0, m.mem.accesses) =
      .ok () := by
  rw [h'.active]; exact check_ok _ _ _

/-! ## `Return` -/

theorem mutateCurFrame_single {m : Mach} {ctx : Ctx} {fr : Frame} {allocs : List Gen.Allocation}
    (h : Shape m ctx [fr] allocs) (g : Frame → Frame) :
    ∃ m', mutateCurFrame m g = .ok m' ∧ Shape m' ctx [g fr] allocs := by
  refine ⟨{ m with threads := [thread1 ctx [g fr]] }, ?_, ⟨rfl, h.active, h.allocs⟩⟩
  simp [mutateCurFrame, activeThread, listIndex, h.threads, h.active, thread1, listSet]

theorem evalReturn_callee {body : CapturedMir} {f : Gen.Function} {ctx : Ctx}
    {locals : List LocalSlot} {m : Mach} {blk stmt : Nat} (h : FrameOk body f ctx locals m blk stmt)
    (d : LocalDecl) (hd : body.localDecls[0]? = some d)
    (haddr : ctx.addrs.getD 0 0 % ((itOf d).size.bytes : Int) = 0)
    (r : Nat) (a : Gen.Allocation) (hp : ctx.retPtr.provenance = some (⟨(r : Int)⟩, ()))
    (hr : ctx.base[r]? = some a) (hlive : a.live = true) (haddrr : a.addr = ctx.retPtr.addr)
    (hlenr : a.data.length = (itOf d).size.bytes)
    (halr : ctx.retPtr.addr % ((itOf d).size.bytes : Int) = 0) :
    (∀ sc, locals[0]? = some (.init (.scalar sc)) →
      ∃ m', evalReturn m = .ok m' ∧
        Shape m' ctx [{ ctx.caller with next_block := ctx.nextBlock, next_stmt := 0 }]
          (ctx.base.set r { a with data := scalarBytes (itOf d) sc.bits } ++
            (localAllocs ctx body.localDecls locals).map kill)) ∧
    (locals[0]? = some .uninit → ∃ msg, evalReturn m = .error (.ub msg)) := by
  have hn0 : 0 < body.localDecls.length := (List.getElem?_eq_some_iff.mp hd).1
  have hgood := h.decl_good 0 d hd
  have hspec := translateFn_spec body f h.hf
  have hloc0 := (hspec.2.1 0 d hd).2
  have hpos := hgood.pos
  have hact : activeThread m =
      .ok (thread1 ctx [ctx.caller, calleeFrame f ctx body.localDecls.length blk stmt]) := by
    simp [activeThread, listIndex, h.shape.threads, h.shape.active]
  have hs3 : Shape { m with threads := [thread1 ctx [ctx.caller]] } ctx [ctx.caller]
      (ctx.base ++ localAllocs ctx body.localDecls locals) := ⟨rfl, h.shape.active, h.shape.allocs⟩
  have hal0 : Align.is_aligned ⟨(itOf d).size.bytes⟩ (ctx.addrs.getD 0 0) = true := by
    simp only [Align.is_aligned, haddr]; rfl
  have hlocPtr : mapGet (localsMap ctx body.localDecls.length) (localName 0) = some (localPtr ctx 0) :=
    mapGet_localsMap ctx _ 0 hn0
  have hpre : ∀ (k : Mach → Interp Mach) (load : Interp (Val × Mach)),
      typedLoad { m with threads := [thread1 ctx [ctx.caller]] } (localPtr ctx 0) (.Int (itOf d))
        ⟨(itOf d).size.bytes⟩ .None = load →
      True := fun _ _ _ => trivial
  clear hpre
  obtain ⟨_, slot0, _, hs0⟩ := h.slot_exists 0 hn0
  have hL0 := h.localAllocs_get 0 d slot0 hd hs0
  have hslot0 := h.slots 0 d slot0 hd hs0
  -- The prefix of `evalReturn` common to both cases.
  have hprefix : evalReturn m = (do
      let (retVal, m4) ← typedLoad { m with threads := [thread1 ctx [ctx.caller]] } (localPtr ctx 0)
        (.Int (itOf d)) ⟨(itOf d).size.bytes⟩ .None
      let (frame, cm) ← deallocAll (localsMap ctx body.localDecls.length).entries.length
        (calleeFrame f ctx body.localDecls.length blk stmt) m4.mem
      let m5 := { m4 with mem := cm }
      match frame.stack_pop_action with
      | .BottomOfStack => terminateActiveThread m5
      | .BackToCaller nextBlock _ callerRetPtr => do
        let t ← activeThread m5
        if t.stack.length = 0 then specPanic "assertion failed: self.active_thread().stack.len() > 0"
        else do
          let m6 ← typedStore m5 callerRetPtr retVal (.Int (itOf d)) ⟨(itOf d).size.bytes⟩ .None
          match nextBlock with
          | some nb => jumpToBlock m6 nb
          | none => ub "return from a function where caller did not specify next block") := by
    simp only [evalReturn, hact, ok_bind, thread1, List.getLast?_cons_cons, List.getLast?_singleton,
      listSet, h.shape.active, h.shape.threads]
    simp [calleeFrame, hspec.1, mapIndex, hloc0, layout_eq _ hgood, LayoutStrategy.expect_align,
      hlocPtr]
    rfl
  constructor
  · intro sc hsc
    rw [hsc] at hs0
    cases hs0
    obtain ⟨hsz, hb⟩ := hslot0
    obtain ⟨m4, hm4, hs4⟩ := typedLoad_local_init hs3 0 (itOf d) sc.bits hgood hb
      (by simpa [slotData] using hL0) _ hal0
    have hlenL : (localAllocs ctx body.localDecls locals).length = body.localDecls.length := by
      simp [localAllocs, localAllocsFrom_length, h.nlocals]
    obtain ⟨cm5, hcm5, hcm5mem⟩ := deallocAll_callee ctx
      (localsMap ctx body.localDecls.length).entries.length
      (calleeFrame f ctx body.localDecls.length blk stmt) m4.mem (List.range body.localDecls.length)
      (localAllocs ctx body.localDecls locals) (by simp [localsMap]) (by simp [calleeFrame, localsMap])
      List.nodup_range (by rw [hs4.allocs])
      (by
        intro i hi
        rw [List.mem_range] at hi
        obtain ⟨di, sloti, hdi, hsi⟩ := h.slot_exists i hi
        refine ⟨itOf di, _, (hspec.2.1 i di hdi).2, h.decl_good i di hdi,
          h.localAllocs_get i di sloti hdi hsi, rfl, rfl, rfl, slotData_length _ _, rfl⟩)
    rw [← hlenL, killAt_range] at hcm5mem
    have hs5 : Shape { m4 with mem := cm5 } ctx [ctx.caller]
        (ctx.base ++ (localAllocs ctx body.localDecls locals).map kill) :=
      ⟨hs4.threads, hs4.active, hcm5mem⟩
    have hact5 : activeThread { m4 with mem := cm5 } = .ok (thread1 ctx [ctx.caller]) := by
      simp [activeThread, listIndex, hs4.threads, hs4.active]
    have hrep := canRepresent_intFromBits (itOf d) sc.bits hgood hb
    have hst := typedStore_base hs5 ctx.retPtr r a hp hr hlive haddrr (itOf d) hgood hlenr
      (intFromBits sc.bits (itOf d)) hrep ⟨(itOf d).size.bytes⟩ (by simp only [Align.is_aligned, halr]; rfl)
    have hres : (intFromBits sc.bits (itOf d) % 2 ^ (8 * (itOf d).size.bytes)).toNat = sc.bits := by
      rw [intFromBits_emod sc.bits _ hb]; simp
    rw [hres] at hst
    have hs6 := withMem_shape (allocs' := ctx.base.set r { a with data := scalarBytes (itOf d) sc.bits } ++
        (localAllocs ctx body.localDecls locals).map kill) hs5 ⟨.Store, .None, ctx.retPtr.addr, (itOf d).size⟩
    obtain ⟨m7, hm7, hs7⟩ := mutateCurFrame_single hs6
      (fun fr => { fr with next_block := ctx.nextBlock, next_stmt := 0 })
    refine ⟨m7, ?_, hs7⟩
    rw [hprefix, hm4]
    simp only [ok_bind]
    rw [hcm5]
    simp only [ok_bind, calleeFrame, hact5, thread1, hst]
    simp [jumpToBlock, hm7]
  · intro hu
    rw [hu] at hs0
    cases hs0
    obtain ⟨msg, hmsg⟩ := typedLoad_local_uninit hs3 0 (itOf d) hgood
      (by simpa [slotData] using hL0) _ hal0
    exact ⟨msg, by rw [hprefix, hmsg]; rfl⟩

/-! ## Shapes of fragment statements and terminators -/

theorem translateStatement_some {st : MirAst.Statement} {st' : Gen.Statement}
    (h : translateStatement st = some st') :
    (∃ i rv e, st.kind = .assign ⟨i, []⟩ rv ∧ translateRvalue rv = some e ∧
      st' = .Assign (.Local (localName i)) e) ∨
    (∃ i, st.kind = .placeMention ⟨i, []⟩ ∧ st' = .PlaceMention (.Local (localName i))) := by
  obtain ⟨kind, span⟩ := st
  simp only [translateStatement] at h ⊢
  match kind, h with
  | .assign ⟨i, []⟩ rv, h =>
    cases he : translateRvalue rv with
    | none => simp [he] at h
    | some e => simp [he] at h; exact .inl ⟨i, rv, e, rfl, he, h.symm⟩
  | .assign ⟨_, _ :: _⟩ _, h => simp at h
  | .setDiscriminant _ _, h => simp at h
  | .deinit _, h => simp at h
  | .storageLive _, h => simp at h
  | .storageDead _, h => simp at h
  | .retag _ _, h => simp at h
  | .placeMention ⟨i, []⟩, h => simp at h; exact .inr ⟨i, rfl, h.symm⟩
  | .placeMention ⟨_, _ :: _⟩, h => simp at h
  | .intrinsic _, h => simp at h
  | .coverage, h => simp at h
  | .constEvalCounter, h => simp at h
  | .backwardIncompatibleDropHint _, h => simp at h
  | .nop, h => simp at h

theorem translateTerminator_some {decls : List LocalDecl} {t : MirAst.Terminator}
    {tt : Gen.Terminator} (h : translateTerminator decls t = some tt) :
    (∃ target, t.kind = .goto target ∧ tt = .Goto (bbName target)) ∨
    (∃ discr targets v it, t.kind = .switchInt discr targets ∧ translateOperand discr = some v ∧
      operandIntType decls discr = some it ∧
      tt = .Switch v (switchCases it targets.branches) (bbName targets.otherwise)) ∨
    (t.kind = .unreachable ∧ tt = .Unreachable) ∨
    (t.kind = .return_ ∧ tt = .Return) := by
  obtain ⟨kind, span⟩ := t
  simp only [translateTerminator] at h ⊢
  match kind, h with
  | .goto target, h => simp at h; exact .inl ⟨target, rfl, h.symm⟩
  | .switchInt discr targets, h =>
    cases hv : translateOperand discr with
    | none => simp [hv] at h
    | some v =>
      cases hit : operandIntType decls discr with
      | none => simp [hv, hit] at h
      | some it =>
        simp [hv, hit] at h
        exact .inr (.inl ⟨discr, targets, v, it, rfl, hv, hit, h.symm⟩)
  | .unreachable, h => simp at h; exact .inr (.inr (.inl ⟨rfl, h.symm⟩))
  | .return_, h => simp at h; exact .inr (.inr (.inr ⟨rfl, h.symm⟩))
  | .unwindResume, h => simp at h
  | .unwindTerminate, h => simp at h
  | .drop _ _ _, h => simp at h
  | .call _ _ _ _ _, h => simp at h
  | .tailCall _ _, h => simp at h
  | .assert _ _ _ _, h => simp at h
  | .inlineAsm _ _ _, h => simp at h

theorem terminatorOk_switch {decls : List LocalDecl} {nblocks : Nat} {t : MirAst.Terminator}
    {discr : Operand} {targets : SwitchTargets} {it : Gen.IntType}
    (h : terminatorOk decls nblocks t = true) (hk : t.kind = .switchInt discr targets)
    (hit : operandIntType decls discr = some it) :
    (∃ j, discr = .copy ⟨j, []⟩ ∧ j < decls.length) ∧
    (∀ p ∈ targets.branches, p.1 < 2 ^ (8 * it.size.bytes) ∧ p.2 < nblocks) ∧
    targets.otherwise < nblocks := by
  simp only [terminatorOk, hk, hit] at h
  match discr, h with
  | .copy ⟨j, []⟩, h =>
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
    obtain ⟨⟨⟨hj, hbr⟩, _⟩, ho⟩ := h
    exact ⟨⟨j, rfl, hj⟩, hbr, ho⟩
  | .copy ⟨_, _ :: _⟩, h => simp at h
  | .move _, h => simp at h
  | .constant _, h => simp at h

theorem lookupSwitchTarget_lt (bits : Nat) (branches : List (Nat × Nat)) (otherwise n : Nat)
    (hbr : ∀ p ∈ branches, p.2 < n) (ho : otherwise < n) :
    MirSemantics.lookupSwitchTarget bits branches otherwise < n := by
  induction branches with
  | nil => simpa [MirSemantics.lookupSwitchTarget] using ho
  | cons p ps ih =>
    obtain ⟨v, t⟩ := p
    simp only [MirSemantics.lookupSwitchTarget]
    cases Nat.beq bits v
    · exact ih (fun q hq => hbr q (by simp [hq]))
    · exact hbr (v, t) (by simp)

theorem listIndex_nat {α : Type} (xs : List α) (k : Nat) (x : α) (h : xs[k]? = some x) (what : String) :
    listIndex xs (k : Int) what = .ok x := by
  simp [listIndex, h]

/-! ## Introducing `StepRel` -/

theorem StepRel.tau' {body : CapturedMir} {f : Gen.Function} {ctx : Ctx} {s s' : MachineState}
    {r : Interp Mach} (m' : Mach) (hr : r = .ok m') (h : StateRel body f ctx s' m') :
    StepRel body f ctx s (.tau (.running s')) r := ⟨m', hr, h⟩

theorem StepRel.emit' {body : CapturedMir} {f : Gen.Function} {ctx : Ctx} {s : MachineState}
    {ev : MirObs} {k : PUnit → MirExecState} {r : Interp Mach} (s' : MachineState) (m' : Mach)
    (hk : k PUnit.unit = .running s') (hr : r = .ok m') (h : StateRel body f ctx s' m') :
    StepRel body f ctx s (.vis (.inr (.inl (.emit ev))) k) r := ⟨s', m', hk, hr, h⟩

theorem StepRel.ret' {body : CapturedMir} {f : Gen.Function} {ctx : Ctx} {s : MachineState}
    {v : Value} {mem : MirSemantics.Memory} {r : Interp Mach} (m' : Mach) (hr : r = .ok m')
    (h : ReturnRel body ctx s v m') :
    StepRel body f ctx s (.ret (.normal (v, mem))) r := ⟨m', hr, h⟩

theorem StepRel.ub' {body : CapturedMir} {f : Gen.Function} {ctx : Ctx} {s : MachineState}
    {r : Interp Mach} (msg : String) (hr : r = .error (.ub msg)) :
    StepRel body f ctx s (MirStepNode.fail .ub) r := ⟨msg, hr⟩

/-- Anneal's state after jumping to block `t` with unchanged locals. -/
def gotoState (s : MachineState) (t : Nat) : MachineState :=
  { s with frame := { blockIdx := t, stmtIdx := 0, locals := s.frame.locals } }

/-- Jumping to an in-range block keeps the relation (the program counters
move together; nothing else changes). -/
theorem StateRel.goto {body : CapturedMir} {f : Gen.Function} {ctx : Ctx} {s : MachineState}
    {m m' : Mach} (hrel : StateRel body f ctx s m) (t : Nat) (ht : t < body.basicBlocks.length)
    (h : Shape m' ctx [ctx.caller, calleeFrame f ctx body.localDecls.length t 0]
      (ctx.base ++ localAllocs ctx body.localDecls s.frame.locals)) :
    StateRel body f ctx (gotoState s t) m' where
  threads := h.threads
  active := h.active
  allocs := h.allocs
  blk := ht
  stmt := fun _ _ => Nat.zero_le _
  nlocals := hrel.nlocals
  slots := hrel.slots
  addrs := hrel.addrs
  ret := hrel.ret
  borrows := hrel.borrows
  callStack := hrel.callStack
  activeCallee := hrel.activeCallee
  protectors := hrel.protectors
  callerLocals := hrel.callerLocals

/-! ## The theorem -/

/-- **Correspondence theorem (one step).** For a fragment body `body`, its
`minimize`-style translation `f`, and related states, one Anneal MIR step and
one MiniRust `Machine::step` correspond in the sense of `StepRel`. -/
theorem step_correspondence (body : CapturedMir) (f : Gen.Function) (hfrag : inFragment body = true)
    (hf : translateFn body = some f) (ctx : Ctx) (s : MachineState) (m : Mach)
    (hrel : StateRel body f ctx s m) :
    StepRel body f ctx s (stepMirFn body s) (Interp.step m) := by
  obtain ⟨hphase, hnl, hbbs⟩ := inFragment_spec body hfrag
  have hspec := translateFn_spec body f hf
  obtain ⟨bb, hbb⟩ : ∃ bb, body.basicBlocks[s.frame.blockIdx]? = some bb :=
    ⟨_, List.getElem?_eq_getElem hrel.blk⟩
  obtain ⟨_, hstmts, hterm⟩ := hbbs bb (List.mem_of_getElem? hbb)
  obtain ⟨tb, htb, hgetb⟩ := hspec.2.2 _ bb hbb
  obtain ⟨hlen, hstspec, htermspec⟩ := translateBlock_spec _ bb tb htb
  have hshape : Shape m ctx
      [ctx.caller, calleeFrame f ctx body.localDecls.length s.frame.blockIdx s.frame.stmtIdx]
      (ctx.base ++ localAllocs ctx body.localDecls s.frame.locals) :=
    ⟨hrel.threads, hrel.active, hrel.allocs⟩
  have hframe : FrameOk body f ctx s.frame.locals (resetPick m) s.frame.blockIdx s.frame.stmtIdx :=
    ⟨hf, resetPick_shape hshape, hrel.nlocals, hrel.slots⟩
  have hslotsA : SlotsOk body.localDecls s.frame.locals := hrel.slots
  rw [step_callee hshape tb hgetb]
  have hstmt_le := hrel.stmt bb hbb
  rcases Nat.lt_or_ge s.frame.stmtIdx bb.statements.length with hlt | hge
  · ----------------------------------------------------------------- statement
    have hne : ((s.frame.stmtIdx : Nat) : Int) ≠ (tb.statements.length : Int) := by
      rw [hlen]; omega
    obtain ⟨st, hst⟩ : ∃ st, bb.statements[s.frame.stmtIdx]? = some st :=
      ⟨_, List.getElem?_eq_getElem hlt⟩
    obtain ⟨st', hst', htst⟩ := hstspec _ st hst
    rw [stepMirFn_stmt body s bb st hrel.activeCallee hphase hbb hst]
    have hok := hstmts st (List.mem_of_getElem? hst)
    have hstmt' : ∀ bb', body.basicBlocks[s.frame.blockIdx]? = some bb' →
        s.frame.stmtIdx + 1 ≤ bb'.statements.length := by
      intro bb' hbb'
      rw [hbb] at hbb'
      cases hbb'
      exact hlt
    rcases translateStatement_some hst' with ⟨i, rv, e, hkind, he, rfl⟩ | ⟨i, hkind, rfl⟩
    · ------------------------------------------------------------ assign
      obtain ⟨kind, span⟩ := st
      simp only at hkind
      subst hkind
      simp only [statementOk] at hok
      cases hdi : body.localDecls[i]? with
      | none => simp [hdi] at hok
      | some d =>
        have hit := (hspec.2.1 i d hdi).1
        have hok' : rvalueOk body.localDecls (itOf d) rv = true := by
          simpa [hdi, hit] using hok
        have hgood := hframe.decl_good i d hdi
        obtain ⟨hMok, hMnone⟩ := evalStatement_assign hframe i d hdi rv hok' e he
        obtain ⟨hAok, hAnone⟩ := evalStmt_assign s body.localDecls body.layouts i rv span hslotsA
          hrel.nlocals d hdi (Nat.ne_of_gt hgood.pos) hok' hrel.borrows hrel.protectors
        cases hr : rvBits s.frame.locals (itOf d) rv with
        | none =>
          rw [hAnone hr]
          obtain ⟨msg, hmsg⟩ := hMnone hr
          exact StepRel.ub' msg (by simp [hne, listIndex_nat _ _ _ htst, hmsg])
        | some r =>
          rw [hAok r hr]
          obtain ⟨m3, hm3, h3⟩ := hMok r hr
          obtain ⟨m4, hm4, h4⟩ := bumpStmt_callee h3.shape
          refine StepRel.tau' m4 (by simp [hne, listIndex_nat _ _ _ htst, hm3, hm4, check_after h4]) ?_
          have hn' : (s.frame.locals.set i (.init (.scalar ⟨r, (itOf d).size.bytes⟩))).length =
              body.localDecls.length := by
            simp [hrel.nlocals]
          exact {
            threads := h4.threads
            active := h4.active
            allocs := h4.allocs
            blk := hrel.blk
            stmt := hstmt'
            nlocals := hn'
            slots := h3.slots
            addrs := hrel.addrs
            ret := hrel.ret
            borrows := rfl
            callStack := hrel.callStack
            activeCallee := hrel.activeCallee
            protectors := hrel.protectors
            callerLocals := hrel.callerLocals }
    · ------------------------------------------------------------ placeMention
      obtain ⟨kind, span⟩ := st
      simp only at hkind
      subst hkind
      have hi : i < body.localDecls.length := by simpa [statementOk] using hok
      have hM := evalStatement_placeMention hframe i hi
      have hA := evalStmt_placeMention s body.localDecls body.layouts i span hslotsA hrel.nlocals hi
      rw [hA]
      obtain ⟨m4, hm4, h4⟩ := bumpStmt_callee hframe.shape
      refine StepRel.tau' m4 (by simp [hne, listIndex_nat _ _ _ htst, hM, hm4, check_after h4]) ?_
      exact {
        threads := h4.threads
        active := h4.active
        allocs := h4.allocs
        blk := hrel.blk
        stmt := hstmt'
        nlocals := hrel.nlocals
        slots := hrel.slots
        addrs := hrel.addrs
        ret := hrel.ret
        borrows := hrel.borrows
        callStack := hrel.callStack
        activeCallee := hrel.activeCallee
        protectors := hrel.protectors
        callerLocals := hrel.callerLocals }
  · ----------------------------------------------------------------- terminator
    have heq : s.frame.stmtIdx = bb.statements.length := by omega
    have hif : ((s.frame.stmtIdx : Nat) : Int) = (tb.statements.length : Int) := by rw [hlen, heq]
    rw [stepMirFn_term body s bb hrel.activeCallee hphase hbb heq]
    simp only [hif, ↓reduceIte]
    rcases translateTerminator_some htermspec with
      ⟨t, hk, htt⟩ | ⟨discr, targets, v, it, hk, hv, hit, htt⟩ | ⟨hk, htt⟩ | ⟨hk, htt⟩
    · -------------------------------------------------------------- goto
      have ht : t < body.basicBlocks.length := by
        simpa [terminatorOk, hk] using hterm
      obtain ⟨m3, hm3, h3⟩ := jumpToBlock_callee hframe.shape t
      have hA : evalTerminator s bb.terminator (some body) = MirStepNode.step (gotoState s t) := by
        simp [MirSemantics.evalTerminator, hk, gotoState]
      rw [hA]
      exact StepRel.tau' m3 (by simp [htt, Interp.evalTerminator, hm3, check_after h3])
        (hrel.goto t ht h3)
    · -------------------------------------------------------------- switchInt
      obtain ⟨⟨j, rfl, hj⟩, hbr, hother⟩ := terminatorOk_switch hterm hk hit
      have hokd : operandOk body.localDecls it (.copy ⟨j, []⟩) = true := by
        simp [operandOk, hj, hit]
      obtain ⟨hMok, hMnone⟩ := evalValue_operand hframe it (.copy ⟨j, []⟩) hokd v hv
      obtain ⟨hAok, hAnone⟩ := evalOperand_frag body.localDecls s.frame.locals hslotsA
        hrel.nlocals it (.copy ⟨j, []⟩) hokd s.memory.borrows s.memory.globals body.layouts
        s.memory.callerLocals
      cases hb : opBits s.frame.locals (.copy ⟨j, []⟩) with
      | none =>
        have hA : evalTerminator s bb.terminator (some body) = MirStepNode.fail .ub := by
          simp [MirSemantics.evalTerminator, hk, hAnone hb]
        rw [hA]
        obtain ⟨msg, hmsg⟩ := hMnone hb
        exact StepRel.ub' msg (by simp [htt, Interp.evalTerminator, hmsg])
      | some bits =>
        obtain ⟨hblt, m3, hm3, h3⟩ := hMok bits hb
        have hlookup := switch_lookup it bits hblt targets.branches (fun p hp => (hbr p hp).1)
          targets.otherwise
        have htgt := lookupSwitchTarget_lt bits targets.branches targets.otherwise
          body.basicBlocks.length (fun p hp => (hbr p hp).2) hother
        obtain ⟨m4, hm4, h4⟩ := jumpToBlock_callee h3.shape
          (MirSemantics.lookupSwitchTarget bits targets.branches targets.otherwise)
        have hA : evalTerminator s bb.terminator (some body) =
            MirStepNode.emitStep (.event bits)
              (gotoState s (MirSemantics.lookupSwitchTarget bits targets.branches targets.otherwise)) := by
          simp [MirSemantics.evalTerminator, hk, hAok bits hb, gotoState]
        rw [hA]
        have hM : evalTerminator (resetPick m) tb.terminator = .ok m4 := by
          rw [htt]
          simp only [Interp.evalTerminator, hm3, ok_bind]
          rw [hlookup]
          exact hm4
        exact StepRel.emit' _ m4 rfl (by simp [hM, check_after h4]) (hrel.goto _ htgt h4)
    · -------------------------------------------------------------- unreachable
      have hA : evalTerminator s bb.terminator (some body) = MirStepNode.fail .ub := by
        simp [MirSemantics.evalTerminator, hk]
      rw [hA]
      exact StepRel.ub' "reached unreachable code" (by simp [htt, Interp.evalTerminator, ub])
    · -------------------------------------------------------------- return
      have hn0 : 0 < body.localDecls.length := by omega
      obtain ⟨d0, hd0⟩ : ∃ d, body.localDecls[0]? = some d := ⟨_, List.getElem?_eq_getElem hn0⟩
      obtain ⟨r0, a0, hp, hr0, hlive, haddrr, hlenr, halr⟩ := hrel.ret d0 hd0
      have hRet := evalReturn_callee hframe d0 hd0 (hrel.addrs 0 d0 hd0) r0 a0 hp hr0 hlive haddrr
        hlenr halr
      obtain ⟨_, slot0, _, hs0⟩ := hframe.slot_exists 0 hn0
      have hslot0 := hrel.slots 0 d0 slot0 hd0 hs0
      match slot0, hslot0, hs0 with
      | .uninit, _, hs0 =>
        have hA : evalTerminator s bb.terminator (some body) = MirStepNode.fail .ub := by
          simp [MirSemantics.evalTerminator, hk, get?, hs0]
        rw [hA]
        obtain ⟨msg, hmsg⟩ := hRet.2 hs0
        exact StepRel.ub' msg (by simp [htt, Interp.evalTerminator, hmsg])
      | .init (.scalar sc), hsc, hs0 =>
        obtain ⟨hsz, _⟩ := hsc
        have hA : evalTerminator s bb.terminator (some body) =
            MirStepNode.retNormal (.scalar sc) s.memory := by
          simp [MirSemantics.evalTerminator, hk, get?, hs0, hrel.callStack]
        rw [hA]
        obtain ⟨m', hm', hs'⟩ := hRet.1 sc hs0
        have hv : Value.scalar sc = .scalar ⟨sc.bits, (itOf d0).size.bytes⟩ := by
          rw [← hsz]
        exact StepRel.ret' m' (by simp [htt, Interp.evalTerminator, hm', check_after hs'])
          ⟨sc.bits, r0, a0, d0, hd0, hv, hp, hr0, hs'.threads, hs'.allocs⟩

/-! ## Entry block (`f.start`) -/

/-- Stepping the `minimize` entry block (`f.start = bbName body.basicBlocks.length`,
whose body is `initBlock = Goto(bb0)`) jumps to `bb0` in one step while
preserving all allocations and locals. -/
theorem step_initBlock {body : CapturedMir} {f : Gen.Function} (hf : translateFn body = some f)
    {ctx : Ctx} {mInit : Mach} {allocs : List Gen.Allocation}
    (hshape : Shape mInit ctx
      [ctx.caller, calleeFrame f ctx body.localDecls.length body.basicBlocks.length 0] allocs) :
    ∃ m0, Interp.step mInit = .ok m0 ∧
      Shape m0 ctx [ctx.caller, calleeFrame f ctx body.localDecls.length 0 0] allocs := by
  obtain ⟨_, hinit⟩ := translateFn_start body f hf
  obtain ⟨m0, hm0, h0⟩ := jumpToBlock_callee (resetPick_shape hshape) 0
  refine ⟨m0, ?_, h0⟩
  rw [step_callee hshape initBlock hinit]
  simp [initBlock, Interp.evalTerminator, hm0, check_after h0]

/-- If `s` is at the start of `bb0` (`blockIdx = 0`, `stmtIdx = 0`) and related
to a machine at `bb0`, then a machine `mInit` at `f.start`
(`bbName body.basicBlocks.length`) steps in one step to a machine related to
`s`. -/
theorem step_start {body : CapturedMir} {f : Gen.Function} (hf : translateFn body = some f)
    {ctx : Ctx} {s : MachineState} {m0 mInit : Mach} (hrel : StateRel body f ctx s m0)
    (hb0 : s.frame.blockIdx = 0) (hs0 : s.frame.stmtIdx = 0)
    (hinit : Shape mInit ctx
      [ctx.caller, calleeFrame f ctx body.localDecls.length body.basicBlocks.length 0]
      (ctx.base ++ localAllocs ctx body.localDecls s.frame.locals)) :
    ∃ m', Interp.step mInit = .ok m' ∧ StateRel body f ctx s m' := by
  obtain ⟨m', hm', hshape'⟩ := step_initBlock hf hinit
  refine ⟨m', hm', ?_⟩
  have hgoto : gotoState s 0 = s := by
    cases s; rename_i fr mem; cases fr; simp [gotoState] at hb0 hs0 ⊢; exact ⟨hb0.symm, hs0.symm⟩
  rw [← hgoto]
  exact hrel.goto 0 (hb0 ▸ hrel.blk) hshape'

end MiniRustSpec.Correspondence
