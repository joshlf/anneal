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

theorem translateBlock_spec (layouts : Layout.LayoutTable) (decls : List LocalDecl)
    (bb : BasicBlockData) (tb : Gen.BasicBlock)
    (h : translateBlock layouts decls bb = some tb) :
    tb.statements.length = bb.statements.length ∧
    (∀ (k : Nat) st, bb.statements[k]? = some st →
      ∃ st', translateStatement layouts decls st = some st' ∧ tb.statements[k]? = some st') ∧
    translateTerminator layouts decls bb.terminator = some tb.terminator := by
  simp only [translateBlock, Option.bind_eq_bind] at h
  cases hs : bb.statements.mapM (translateStatement layouts decls) with
  | none => simp [hs] at h
  | some stmts =>
    cases ht : translateTerminator layouts decls bb.terminator with
    | none => simp [hs, ht] at h
    | some term =>
      simp [hs, ht] at h
      subst h
      obtain ⟨hlen, hget⟩ := mapM_option_spec (translateStatement layouts decls) bb.statements stmts hs
      exact ⟨hlen, hget, rfl⟩

/-- Facts about a body accepted by `inFragment`. -/
theorem inFragment_spec (body : CapturedMir) (h : inFragment body = true) :
    body.phase = .runtimePostCleanup ∧ body.localDecls.length = body.argCount + 1 ∧
    (∀ d ∈ body.localDecls, localDeclOk body.layouts d = true) ∧
    (body.localDecls[0]? >>= (intTypeOf ·.ty)).isSome = true ∧
    (∀ bb ∈ body.basicBlocks, bb.isCleanup = false ∧
      (∀ st ∈ bb.statements, statementOk body.layouts body.localDecls st = true) ∧
      terminatorOk body.layouts body.localDecls body.basicBlocks.length bb.terminator = true) := by
  simp only [inFragment, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.not_eq_true']
    at h
  obtain ⟨⟨⟨⟨⟨⟨hphase, hlen⟩, hret0⟩, hdecls⟩, _⟩, hbbs⟩, _⟩ := h
  refine ⟨?_, hlen, hdecls, hret0, fun bb hbb => ?_⟩
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
    (h0scalar : intTypeOf d.ty = some (itOf body.layouts d))
    (haddr : ctx.addrs.getD 0 0 % ((itOf body.layouts d).size.bytes : Int) = 0)
    (r : Nat) (a : Gen.Allocation) (hp : ctx.retPtr.provenance = some (⟨(r : Int)⟩, ()))
    (hr : ctx.base[r]? = some a) (hlive : a.live = true) (haddrr : a.addr = ctx.retPtr.addr)
    (hlenr : a.data.length = (itOf body.layouts d).size.bytes)
    (halr : ctx.retPtr.addr % ((itOf body.layouts d).size.bytes : Int) = 0) :
    (∀ sc, locals[0]? = some (.init (.scalar sc)) →
      ∃ m', evalReturn m = .ok m' ∧
        Shape m' ctx [{ ctx.caller with next_block := ctx.nextBlock, next_stmt := 0 }]
          (ctx.base.set r { a with data := scalarBytes (itOf body.layouts d) sc.bits } ++
            (localAllocs body.layouts ctx body.localDecls locals).map kill)) ∧
    (locals[0]? = some .uninit → ∃ msg, evalReturn m = .error (.ub msg)) := by
  have hn0 : 0 < body.localDecls.length := (List.getElem?_eq_some_iff.mp hd).1
  have hgood := h.decl_good 0 d hd
  have hspec := translateFn_spec body f h.hf
  have harr0 := arrayTypeOf_none_of_intTypeOf h0scalar
  have htup0 := tupleTypeOf_none_of_intTypeOf (layouts := body.layouts) h0scalar
  have htr0 : translateTy body.layouts d.ty = some (.Int (itOf body.layouts d)) := by
    simp [translateTy, h0scalar]
  have hloc0 := translateFn_local_ty h.hf 0 d _ hd htr0
  have hpos := hgood.pos
  have hact : activeThread m =
      .ok (thread1 ctx [ctx.caller, calleeFrame f ctx body.localDecls.length blk stmt]) := by
    simp [activeThread, listIndex, h.shape.threads, h.shape.active]
  have hs3 : Shape { m with threads := [thread1 ctx [ctx.caller]] } ctx [ctx.caller]
      (ctx.base ++ localAllocs body.layouts ctx body.localDecls locals) :=
    ⟨rfl, h.shape.active, h.shape.allocs⟩
  have hal0 : Align.is_aligned ⟨(itOf body.layouts d).size.bytes⟩ (ctx.addrs.getD 0 0) = true := by
    simp only [Align.is_aligned, haddr]; rfl
  have hlocPtr : mapGet (localsMap ctx body.localDecls.length) (localName 0) = some (localPtr ctx 0) :=
    mapGet_localsMap ctx _ 0 hn0
  obtain ⟨_, slot0, _, hs0⟩ := h.slot_exists 0 hn0
  have hL0 := h.localAllocs_get 0 d slot0 hd hs0
  simp only [declSlotData, harr0, htup0] at hL0
  have hslot0 := h.slots 0 d slot0 hd hs0
  simp only [DeclSlotOk, harr0, htup0] at hslot0
  -- The prefix of `evalReturn` common to both cases.
  have hprefix : evalReturn m = (do
      let (retVal, m4) ← typedLoad { m with threads := [thread1 ctx [ctx.caller]] } (localPtr ctx 0)
        (.Int (itOf body.layouts d)) ⟨(itOf body.layouts d).size.bytes⟩ .None
      let (frame, cm) ← deallocAll (localsMap ctx body.localDecls.length).entries.length
        (calleeFrame f ctx body.localDecls.length blk stmt) m4.mem
      let m5 := { m4 with mem := cm }
      match frame.stack_pop_action with
      | .BottomOfStack => terminateActiveThread m5
      | .BackToCaller nextBlock _ callerRetPtr => do
        let t ← activeThread m5
        if t.stack.length = 0 then specPanic "assertion failed: self.active_thread().stack.len() > 0"
        else do
          let m6 ← typedStore m5 callerRetPtr retVal (.Int (itOf body.layouts d)) ⟨(itOf body.layouts d).size.bytes⟩ .None
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
    obtain ⟨m4, hm4, hs4⟩ := typedLoad_local_init hs3 0 (itOf body.layouts d) sc.bits hgood hb
      (by simpa [slotData] using hL0) _ hal0
    have hlenL : (localAllocs body.layouts ctx body.localDecls locals).length = body.localDecls.length := by
      simp [localAllocs, localAllocsFrom_length, h.nlocals]
    obtain ⟨cm5, hcm5, hcm5mem⟩ := deallocAll_callee ctx
      (localsMap ctx body.localDecls.length).entries.length
      (calleeFrame f ctx body.localDecls.length blk stmt) m4.mem (List.range body.localDecls.length)
      (localAllocs body.layouts ctx body.localDecls locals) (by simp [localsMap]) (by simp [calleeFrame, localsMap])
      List.nodup_range (by rw [hs4.allocs])
      (by
        intro i hi
        rw [List.mem_range] at hi
        obtain ⟨di, sloti, hdi, hsi⟩ := h.slot_exists i hi
        obtain ⟨Ti, htri, hgeti⟩ := hspec.2.1 i di hdi
        have hsloti := h.slots i di sloti hdi hsi
        have hdlen := declSlotData_length di sloti hsloti
        have hgoodi := h.decl_good i di hdi
        refine ⟨Ti, _, hgeti, h.localAllocs_get i di sloti hdi hsi, rfl, rfl, rfl, ?_⟩
        dsimp only [localAlloc]
        rw [hdlen]
        cases ha : arrayTypeOf di.ty with
        | none =>
          cases ht : tupleTypeOf body.layouts di.ty with
          | none =>
            have hokdi := h.declsOk di (List.mem_of_getElem? hdi)
            simp only [localDeclOk, ha, ht, Bool.or_false, Option.isSome_iff_exists] at hokdi
            obtain ⟨iti, hiti⟩ := hokdi
            have hitd : itOf body.layouts di = iti := by simp [itOf, ha, ht, hiti]
            rw [hitd] at hgoodi ⊢
            have hTi : Ti = .Int iti := by
              simp [translateTy, hiti] at htri
              exact htri.symm
            subst hTi
            exact layout_eq iti hgoodi
          | some p =>
            obtain ⟨fields, size, align⟩ := p
            have hnone := intTypeOf_none_of_tupleTypeOf ht
            have hitd : itOf body.layouts di = ⟨.Unsigned, ⟨align⟩⟩ := by simp [itOf, ha, ht]
            rw [hitd]
            have hTi : Ti = (TupleSpec.tuple fields size align).toMiniRustTy := by
              simp [translateTy, hnone, ha, ht] at htri
              exact htri.symm
            subst hTi
            have hwf := h.tuple_wf i di fields size align hdi ht
            exact layout_tupleSpec (.tuple fields size align) hwf
        | some p =>
          obtain ⟨elemIt, count⟩ := p
          have hnone := intTypeOf_none_of_arrayTypeOf ha
          have hitd : itOf body.layouts di = elemIt := by simp [itOf, ha]
          rw [hitd] at hgoodi ⊢
          have hTi : Ti = .Array (.Int elemIt) (count : Int) := by
            simp [translateTy, hnone, ha] at htri
            exact htri.symm
          subst hTi
          exact layout_array_eq elemIt count hgoodi)
    rw [← hlenL, killAt_range] at hcm5mem
    have hs5 : Shape { m4 with mem := cm5 } ctx [ctx.caller]
        (ctx.base ++ (localAllocs body.layouts ctx body.localDecls locals).map kill) :=
      ⟨hs4.threads, hs4.active, hcm5mem⟩
    have hact5 : activeThread { m4 with mem := cm5 } = .ok (thread1 ctx [ctx.caller]) := by
      simp [activeThread, listIndex, hs4.threads, hs4.active]
    have hrep := canRepresent_intFromBits (itOf body.layouts d) sc.bits hgood hb
    have hst := typedStore_base hs5 ctx.retPtr r a hp hr hlive haddrr (itOf body.layouts d) hgood hlenr
      (intFromBits sc.bits (itOf body.layouts d)) hrep ⟨(itOf body.layouts d).size.bytes⟩
      (by simp only [Align.is_aligned, halr]; rfl)
    have hres : (intFromBits sc.bits (itOf body.layouts d) % 2 ^ (8 * (itOf body.layouts d).size.bytes)).toNat = sc.bits := by
      rw [intFromBits_emod sc.bits _ hb]; simp
    rw [hres] at hst
    have hs6 := withMem_shape (allocs' := ctx.base.set r { a with data := scalarBytes (itOf body.layouts d) sc.bits } ++
        (localAllocs body.layouts ctx body.localDecls locals).map kill) hs5
        ⟨.Store, .None, ctx.retPtr.addr, (itOf body.layouts d).size⟩
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
    obtain ⟨msg, hmsg⟩ := typedLoad_local_uninit hs3 0 (itOf body.layouts d) hgood
      (by simpa [slotData] using hL0) _ hal0
    exact ⟨msg, by rw [hprefix, hmsg]; rfl⟩

/-! ## Shapes of fragment statements and terminators -/

theorem translateStatement_some {layouts : Layout.LayoutTable} {decls : List LocalDecl}
    {st : MirAst.Statement} {st' : Gen.Statement}
    (h : translateStatement layouts decls st = some st') :
    (∃ dst rv pe e, st.kind = .assign dst rv ∧
      translatePlace decls dst = some pe ∧
      translateRvalue layouts decls (placeMirTy decls dst) rv = some e ∧
      st' = .Assign pe e) ∨
    (∃ i, st.kind = .placeMention ⟨i, []⟩ ∧ st' = .PlaceMention (.Local (localName i))) ∨
    (∃ i idx fieldTy rest pe,
      st.kind = .placeMention ⟨i, .field idx fieldTy :: rest⟩ ∧
      translateFieldPlace (.Local (localName i)) (.field idx fieldTy :: rest) = some pe ∧
      st' = .PlaceMention pe) := by
  obtain ⟨kind, span⟩ := st
  simp only [translateStatement] at h ⊢
  match kind, h with
  | .assign dst rv, h =>
    simp only [Option.bind_eq_bind] at h
    cases hpe : translatePlace decls dst with
    | none => simp [hpe] at h
    | some pe =>
      cases he : translateRvalue layouts decls (placeMirTy decls dst) rv with
      | none => simp [hpe, he] at h
      | some e =>
        simp [hpe, he] at h
        exact .inl ⟨dst, rv, pe, e, rfl, hpe, he, h.symm⟩
  | .setDiscriminant _ _, h => simp at h
  | .deinit _, h => simp at h
  | .storageLive _, h => simp at h
  | .storageDead _, h => simp at h
  | .retag _ _, h => simp at h
  | .placeMention ⟨i, []⟩, h => simp at h; exact .inr (.inl ⟨i, rfl, h.symm⟩)
  | .placeMention ⟨i, p :: rest⟩, h =>
    cases p with
    | field idx fieldTy =>
      simp only [Option.bind_eq_bind] at h
      cases hpe : translateFieldPlace (.Local (localName i)) (.field idx fieldTy :: rest) with
      | none => simp [hpe] at h
      | some pe =>
        simp [hpe] at h
        exact .inr (.inr ⟨i, idx, fieldTy, rest, pe, rfl, hpe, h.symm⟩)
    | _ => simp at h
  | .intrinsic _, h => simp at h
  | .coverage, h => simp at h
  | .constEvalCounter, h => simp at h
  | .backwardIncompatibleDropHint _, h => simp at h
  | .nop, h => simp at h

theorem statementOk_assign_single_nonfield {layouts : Layout.LayoutTable} {decls : List LocalDecl}
    {i : Nat} {proj : ProjectionElem} {rv : Rvalue} {span : String}
    (hnf : ∀ idx fieldTy, proj ≠ .field idx fieldTy) :
    statementOk layouts decls ⟨.assign ⟨i, [proj]⟩ rv, span⟩ =
      match decls[i]? >>= (arrayTypeOf ·.ty) with
      | some (elemIt, count) =>
        projOk decls count proj && rvalueOk layouts decls elemIt rv
      | none => false := by
  cases proj with
  | field idx fieldTy => exact False.elim (hnf idx fieldTy rfl)
  | _ => rfl

theorem translateTerminator_some {layouts : Layout.LayoutTable} {decls : List LocalDecl}
    {t : MirAst.Terminator} {tt : Gen.Terminator}
    (h : translateTerminator layouts decls t = some tt) :
    (∃ target, t.kind = .goto target ∧ tt = .Goto (bbName target)) ∨
    (∃ discr targets v it, t.kind = .switchInt discr targets ∧
      translateOperand decls discr = some v ∧
      operandIntType layouts decls discr = some it ∧
      tt = .Switch v (switchCases it targets.branches) (bbName targets.otherwise)) ∨
    (t.kind = .unreachable ∧ tt = .Unreachable) ∨
    (t.kind = .return_ ∧ tt = .Return) := by
  obtain ⟨kind, span⟩ := t
  simp only [translateTerminator] at h ⊢
  match kind, h with
  | .goto target, h => simp at h; exact .inl ⟨target, rfl, h.symm⟩
  | .switchInt discr targets, h =>
    cases hv : translateOperand decls discr with
    | none => simp [hv] at h
    | some v =>
      cases hit : operandIntType layouts decls discr with
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

theorem terminatorOk_switch {layouts : Layout.LayoutTable} {decls : List LocalDecl}
    {nblocks : Nat} {t : MirAst.Terminator}
    {discr : Operand} {targets : SwitchTargets} {it : Gen.IntType}
    (h : terminatorOk layouts decls nblocks t = true) (hk : t.kind = .switchInt discr targets)
    (hit : operandIntType layouts decls discr = some it) :
    operandOk layouts decls it discr = true ∧
    (∀ p ∈ targets.branches, p.1 < 2 ^ (8 * it.size.bytes) ∧ p.2 < nblocks) ∧
    targets.otherwise < nblocks := by
  simp only [terminatorOk, hk, hit, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨hokd, hbr⟩, _⟩, ho⟩ := h
  exact ⟨hokd, hbr, ho⟩

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
      (ctx.base ++ localAllocs body.layouts ctx body.localDecls s.frame.locals)) :
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
  obtain ⟨hphase, hnl, hdeclsOk, hret0, hbbs⟩ := inFragment_spec body hfrag
  have hspec := translateFn_spec body f hf
  obtain ⟨bb, hbb⟩ : ∃ bb, body.basicBlocks[s.frame.blockIdx]? = some bb :=
    ⟨_, List.getElem?_eq_getElem hrel.blk⟩
  obtain ⟨_, hstmts, hterm⟩ := hbbs bb (List.mem_of_getElem? hbb)
  obtain ⟨tb, htb, hgetb⟩ := hspec.2.2 _ bb hbb
  obtain ⟨hlen, hstspec, htermspec⟩ := translateBlock_spec _ _ bb tb htb
  have hshape : Shape m ctx
      [ctx.caller, calleeFrame f ctx body.localDecls.length s.frame.blockIdx s.frame.stmtIdx]
      (ctx.base ++ localAllocs body.layouts ctx body.localDecls s.frame.locals) :=
    ⟨hrel.threads, hrel.active, hrel.allocs⟩
  have hframe : FrameOk body f ctx s.frame.locals (resetPick m) s.frame.blockIdx s.frame.stmtIdx :=
    ⟨hf, resetPick_shape hshape, hrel.nlocals, hrel.slots, hrel.addrs, hdeclsOk⟩
  have hslotsA : SlotsOk body.layouts body.localDecls s.frame.locals := hrel.slots
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
    rcases translateStatement_some hst' with
      ⟨dst, rv, pe, e, hkind, hpe, he, rfl⟩ |
      ⟨i, hkind, rfl⟩ |
      ⟨i, idx, fieldTy, rest, pe, hkind, hpe, rfl⟩
    · ------------------------------------------------------------ assign
      obtain ⟨kind, span⟩ := st
      simp only at hkind
      subst hkind
      rcases dst with ⟨i, projs⟩
      cases projs with
      | nil =>
        ---------------------------------------------------------- assign root local `_i = rv`
        simp only [translatePlace, Option.some.injEq] at hpe
        subst hpe
        simp only [statementOk] at hok
        cases hdi : body.localDecls[i]? with
        | none => simp [hdi] at hok
        | some d =>
          simp only [hdi] at hok
          cases hit : intTypeOf d.ty with
          | some it =>
            simp only [hit] at hok
            have htup0 := tupleTypeOf_none_of_intTypeOf (layouts := body.layouts) hit
            have hitd : itOf body.layouts d = it := by
              simp [itOf, arrayTypeOf_none_of_intTypeOf hit, htup0, hit]
            rw [← hitd] at hit hok
            have hgood := hframe.decl_good i d hdi
            obtain ⟨hMok, hMnone⟩ := evalStatement_assign hframe i d hdi hit rv hok e he
            obtain ⟨hAok, hAnone⟩ := evalStmt_assign s body.localDecls body.layouts i rv span hslotsA
              hrel.nlocals d hdi hgood hok hrel.borrows hrel.protectors
            cases hr : rvBits body.localDecls s.frame.locals (itOf body.layouts d) body.layouts rv with
            | none =>
              rw [hAnone hr]
              obtain ⟨msg, hmsg⟩ := hMnone hr
              exact StepRel.ub' msg (by simp [hne, listIndex_nat _ _ _ htst, hmsg])
            | some r =>
              rw [hAok r hr]
              obtain ⟨m3, hm3, h3⟩ := hMok r hr
              obtain ⟨m4, hm4, h4⟩ := bumpStmt_callee h3.shape
              refine StepRel.tau' m4 (by simp [hne, listIndex_nat _ _ _ htst, hm3, hm4, check_after h4]) ?_
              have hn' : (s.frame.locals.set i (.init (.scalar ⟨r, (itOf body.layouts d).size.bytes⟩))).length =
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
          | none =>
            simp only [hit] at hok
            cases ha : arrayTypeOf d.ty with
            | some p =>
              obtain ⟨elemIt, count⟩ := p
              simp only [ha] at hok
              obtain ⟨hMok, hMnone⟩ :=
                evalStatement_assign_array hframe i d hdi elemIt count ha rv hok e he
              obtain ⟨hAok, hAnone⟩ :=
                evalStmt_assign_array s body.localDecls body.layouts i rv span hslotsA
                  hrel.nlocals d hdi elemIt count ha hok hrel.borrows hrel.protectors
              cases hel : arrayRvElems s.frame.locals elemIt rv with
              | none =>
                rw [hAnone hel]
                obtain ⟨msg, hmsg⟩ := hMnone hel
                exact StepRel.ub' msg (by simp [hne, listIndex_nat _ _ _ htst, hmsg])
              | some elems =>
                rw [hAok elems hel]
                obtain ⟨m3, hm3, h3⟩ := hMok elems hel
                obtain ⟨m4, hm4, h4⟩ := bumpStmt_callee h3.shape
                refine StepRel.tau' m4 (by simp [hne, listIndex_nat _ _ _ htst, hm3, hm4, check_after h4]) ?_
                have hn' : (s.frame.locals.set i (.init (.aggregate 0 elems))).length =
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
            | none =>
              simp only [ha] at hok
              cases ht : tupleTypeOf body.layouts d.ty with
              | none => simp [ht] at hok
              | some p =>
                obtain ⟨fields, size, align⟩ := p
                simp only [ht] at hok
                have hi : i < body.localDecls.length := (List.getElem?_eq_some_iff.mp hdi).1
                have htp : tuplePlaceSpec body.layouts body.localDecls ⟨i, []⟩ = some (fields, size, align) := by
                  simp only [tuplePlaceSpec, hi, ↓reduceIte, hdi, Option.bind_eq_bind, Option.bind_some, ht]
                have hpmir : placeMirTy body.localDecls ⟨i, []⟩ = some d.ty := by
                  simp [placeMirTy, hdi, resolveProjTy]
                rw [hpmir] at he
                obtain ⟨_, sloti, _, hsi⟩ := hframe.slot_exists i hi
                have hsloti := hrel.slots i d sloti hdi hsi
                simp only [DeclSlotOk, ha, ht] at hsloti
                match sloti, hsloti, hsi with
                | .init rootVal, _, hsi =>
                  have hpe' : translatePlace body.localDecls ⟨i, []⟩ = some (.Local (localName i)) := rfl
                  obtain ⟨hMok, hMnone⟩ :=
                    evalStatement_assign_tuple hframe ⟨i, []⟩ d.ty fields size align htp
                      (.Local (localName i)) hpe' rv hok e he rootVal hsi
                  obtain ⟨hAok, hAnone⟩ :=
                    evalStmt_assign_tuple s body.localDecls body.layouts ⟨i, []⟩ d.ty fields size align
                      htp rv span hslotsA hrel.nlocals hok rootVal hsi hrel.borrows hrel.protectors
                  cases hnv : tupleRvVal s.frame.locals fields rv with
                  | none =>
                    rw [hAnone hnv]
                    obtain ⟨msg, hmsg⟩ := hMnone hnv
                    exact StepRel.ub' msg (by simp [hne, listIndex_nat _ _ _ htst, hmsg])
                  | some newVal =>
                    obtain ⟨newRootVal, m3, hwpath, hwsem, hm3, h3⟩ := hMok newVal hnv
                    rw [hAok newVal newRootVal hnv hwpath hwsem]
                    obtain ⟨m4, hm4, h4⟩ := bumpStmt_callee h3.shape
                    refine StepRel.tau' m4 (by simp [hne, listIndex_nat _ _ _ htst, hm3, hm4, check_after h4]) ?_
                    have hn' : (s.frame.locals.set i (.init newRootVal)).length =
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
      | cons proj rest =>
        by_cases hfield : ∃ idx fieldTy, proj = .field idx fieldTy
        · -------------------------------------------------------- assign field `_i.f1...fk = rv`
          obtain ⟨idx, fieldTy, rfl⟩ := hfield
          simp only [statementOk] at hok
          cases hpit : placeIntType body.layouts body.localDecls ⟨i, .field idx fieldTy :: rest⟩ with
          | some it =>
            simp only [hpit, Bool.and_eq_true] at hok
            obtain ⟨hpok, hrvok⟩ := hok
            have hpok' := hpok
            simp only [placeOk, Bool.and_eq_true, decide_eq_true_eq] at hpok'
            obtain ⟨hi, hpok'⟩ := hpok'
            cases hdi : body.localDecls[i]? with
            | none => simp [hdi] at hpok'
            | some d =>
              simp only [hdi, Option.bind_eq_bind, Option.bind_some] at hpok'
              cases ht : tupleTypeOf body.layouts d.ty with
              | none => simp [ht] at hpok'
              | some rpair =>
                obtain ⟨rootFields, rootSize, rootAlign⟩ := rpair
                simp only [ht] at hpok'
                cases hres : resolveFieldPath body.layouts (.tuple rootFields rootSize rootAlign)
                    (.field idx fieldTy :: rest) with
                | none => simp [hres] at hpok'
                | some lpair =>
                  obtain ⟨relOff, leafSpec⟩ := lpair
                  simp only [hres] at hpok'
                  cases leafSpec with
                  | tuple _ _ _ => simp at hpok'
                  | scalar leafIt =>
                    simp only [decide_eq_true_eq] at hpok'
                    subst hpok'
                    obtain ⟨_, sloti, _, hsi⟩ := hframe.slot_exists i hi
                    have hsloti := hrel.slots i d sloti hdi hsi
                    simp only [DeclSlotOk, arrayTypeOf_none_of_tupleTypeOf ht, ht] at hsloti
                    match sloti, hsloti, hsi with
                    | .init rootVal, ⟨hrootWf, _⟩, hsi =>
                      obtain ⟨hleafWf, _⟩ := resolveFieldPath_wf hrootWf hres
                      have hgood : GoodSize leafIt.size.bytes :=
                        (goodAlignBytes_iff leafIt.size.bytes).mp hleafWf
                      obtain ⟨hMok, hMnone⟩ :=
                        evalStatement_assign_field_scalar hframe i idx fieldTy rest leafIt
                          hpok pe hpe rv hrvok e he rootVal hsi
                      obtain ⟨hAok, hAnone⟩ :=
                        evalStmt_assign_field_scalar s body.localDecls body.layouts i idx fieldTy rest
                          leafIt hgood rv span hslotsA hrel.nlocals hi hrvok rootVal hsi
                          hrel.borrows hrel.protectors
                      cases hr : rvBits body.localDecls s.frame.locals leafIt body.layouts rv with
                      | none =>
                        rw [hAnone hr]
                        obtain ⟨msg, hmsg⟩ := hMnone hr
                        exact StepRel.ub' msg (by simp [hne, listIndex_nat _ _ _ htst, hmsg])
                      | some r =>
                        obtain ⟨newRootVal, m3, _, hwsem, hm3, h3⟩ := hMok r hr
                        rw [hAok r newRootVal hr hwsem]
                        obtain ⟨m4, hm4, h4⟩ := bumpStmt_callee h3.shape
                        refine StepRel.tau' m4 (by simp [hne, listIndex_nat _ _ _ htst, hm3, hm4, check_after h4]) ?_
                        have hn' : (s.frame.locals.set i (.init newRootVal)).length =
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
          | none =>
            simp only [hpit] at hok
            cases htp : tuplePlaceSpec body.layouts body.localDecls ⟨i, .field idx fieldTy :: rest⟩ with
            | none => simp [htp] at hok
            | some tpair =>
              obtain ⟨fields, size, align⟩ := tpair
              cases hpmir : placeMirTy body.localDecls ⟨i, .field idx fieldTy :: rest⟩ with
              | none => simp [htp, hpmir] at hok
              | some dstTy =>
                simp only [htp, hpmir] at hok
                rw [hpmir] at he
                obtain ⟨d, rootFields, rootSize, rootAlign, _, hi, hdi, ht, _, _⟩ :=
                  tuplePlaceSpec_resolve htp
                obtain ⟨_, sloti, _, hsi⟩ := hframe.slot_exists i hi
                have hsloti := hrel.slots i d sloti hdi hsi
                simp only [DeclSlotOk, arrayTypeOf_none_of_tupleTypeOf ht, ht] at hsloti
                match sloti, hsloti, hsi with
                | .init rootVal, _, hsi =>
                  obtain ⟨hMok, hMnone⟩ :=
                    evalStatement_assign_tuple hframe ⟨i, .field idx fieldTy :: rest⟩ dstTy
                      fields size align htp pe hpe rv hok e he rootVal hsi
                  obtain ⟨hAok, hAnone⟩ :=
                    evalStmt_assign_tuple s body.localDecls body.layouts
                      ⟨i, .field idx fieldTy :: rest⟩ dstTy fields size align htp rv span
                      hslotsA hrel.nlocals hok rootVal hsi hrel.borrows hrel.protectors
                  cases hnv : tupleRvVal s.frame.locals fields rv with
                  | none =>
                    rw [hAnone hnv]
                    obtain ⟨msg, hmsg⟩ := hMnone hnv
                    exact StepRel.ub' msg (by simp [hne, listIndex_nat _ _ _ htst, hmsg])
                  | some newVal =>
                    obtain ⟨newRootVal, m3, hwpath, hwsem, hm3, h3⟩ := hMok newVal hnv
                    rw [hAok newVal newRootVal hnv hwpath hwsem]
                    obtain ⟨m4, hm4, h4⟩ := bumpStmt_callee h3.shape
                    refine StepRel.tau' m4 (by simp [hne, listIndex_nat _ _ _ htst, hm3, hm4, check_after h4]) ?_
                    have hn' : (s.frame.locals.set i (.init newRootVal)).length =
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
        · -------------------------------------------------------- assign indexed element `_i[proj] = rv`
          have hnf : ∀ idx fieldTy, proj ≠ .field idx fieldTy :=
            fun idx fieldTy h => hfield ⟨idx, fieldTy, h⟩
          cases rest with
          | cons p2 rest2 =>
            cases proj with
            | field idx fieldTy => exact False.elim (hnf idx fieldTy rfl)
            | _ => simp [translatePlace] at hpe
          | nil =>
            rw [statementOk_assign_single_nonfield hnf] at hok
            cases hdi : body.localDecls[i]? with
            | none => simp [hdi] at hok
            | some d =>
              simp only [hdi, Option.bind_eq_bind, Option.bind_some] at hok
              cases ha : arrayTypeOf d.ty with
              | none => simp [ha] at hok
              | some p =>
                obtain ⟨elemIt, count⟩ := p
                simp only [ha, Bool.and_eq_true] at hok
                obtain ⟨hproj, hok'⟩ := hok
                have hi : i < body.localDecls.length := (List.getElem?_eq_some_iff.mp hdi).1
                obtain ⟨_, sloti, _, hsi⟩ := hframe.slot_exists i hi
                have hsloti := hrel.slots i d sloti hdi hsi
                simp only [DeclSlotOk, ha] at hsloti
                match sloti, hsloti, hsi with
                | .init (.aggregate 0 elems), ⟨hlen, _⟩, hsi =>
                  have hgood := arrayTypeOf_good ha
                  obtain ⟨hMok, hMnone⟩ :=
                    evalStatement_assign_index hframe i d hdi elemIt count ha proj hproj pe hpe rv hok' e he
                      elems hsi
                  obtain ⟨hAok, hAnone⟩ :=
                    evalStmt_assign_index s body.localDecls body.layouts i proj rv span hslotsA
                      hrel.nlocals d hdi elemIt count ha hgood hproj hok' elems hsi hlen
                      hrel.borrows hrel.protectors
                  cases hidx : projIdx s.frame.locals count proj with
                  | none =>
                    rw [hAnone (.inl hidx)]
                    obtain ⟨msg, hmsg⟩ := hMnone (.inl hidx)
                    exact StepRel.ub' msg (by simp [hne, listIndex_nat _ _ _ htst, hmsg])
                  | some idx =>
                    cases hr : rvBits body.localDecls s.frame.locals elemIt body.layouts rv with
                    | none =>
                      rw [hAnone (.inr hr)]
                      obtain ⟨msg, hmsg⟩ := hMnone (.inr hr)
                      exact StepRel.ub' msg (by simp [hne, listIndex_nat _ _ _ htst, hmsg])
                    | some r =>
                      rw [hAok idx r hidx hr]
                      obtain ⟨m3, hm3, h3⟩ := hMok idx r hidx hr
                      obtain ⟨m4, hm4, h4⟩ := bumpStmt_callee h3.shape
                      refine StepRel.tau' m4 (by simp [hne, listIndex_nat _ _ _ htst, hm3, hm4, check_after h4]) ?_
                      have hn' : (s.frame.locals.set i
                          (.init (.aggregate 0 (elems.set idx (.scalar ⟨r, elemIt.size.bytes⟩))))).length =
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
    · ------------------------------------------------------------ placeMention (local)
      obtain ⟨kind, span⟩ := st
      simp only at hkind
      subst hkind
      have hi : i < body.localDecls.length := by simpa [statementOk] using hok
      have hM := evalStatement_placeMention hframe i hi
      have hA := evalStmt_placeMention s body.localDecls body.layouts i [] span hslotsA hrel.nlocals hi
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
    · ------------------------------------------------------------ placeMention (field path)
      obtain ⟨kind, span⟩ := st
      simp only at hkind
      subst hkind
      simp only [statementOk, Bool.and_eq_true, decide_eq_true_eq] at hok
      obtain ⟨hi, hok⟩ := hok
      cases hdi : body.localDecls[i]? with
      | none => simp [hdi] at hok
      | some d =>
        simp only [hdi, Option.bind_eq_bind, Option.bind_some] at hok
        cases ht : tupleTypeOf body.layouts d.ty with
        | none => simp [ht] at hok
        | some rpair =>
          obtain ⟨fields, size, align⟩ := rpair
          simp only [ht] at hok
          cases hres : resolveFieldPath body.layouts (.tuple fields size align)
              (.field idx fieldTy :: rest) with
          | none => simp [hres] at hok
          | some lpair =>
            obtain ⟨relOff, leafSpec⟩ := lpair
            have hM := evalStatement_placeMention_field hframe i idx fieldTy rest pe hpe d hdi
              fields size align ht relOff leafSpec hres
            have hA := evalStmt_placeMention s body.localDecls body.layouts i
              (.field idx fieldTy :: rest) span hslotsA hrel.nlocals hi
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
      obtain ⟨hokd, hbr, hother⟩ := terminatorOk_switch hterm hk hit
      obtain ⟨hMok, hMnone⟩ := evalValue_operand hframe it discr hokd v hv
      obtain ⟨hAok, hAnone⟩ := evalOperand_frag body.localDecls s.frame.locals hslotsA
        hrel.nlocals it discr hokd s.memory.borrows s.memory.globals
        s.memory.callerLocals
      cases hb : opBits s.frame.locals discr with
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
      obtain ⟨it0, hit0⟩ := Option.isSome_iff_exists.mp (by simpa [hd0] using hret0)
      have harr0 := arrayTypeOf_none_of_intTypeOf hit0
      have htup0 := tupleTypeOf_none_of_intTypeOf (layouts := body.layouts) hit0
      have hitd0 : itOf body.layouts d0 = it0 := by simp [itOf, harr0, htup0, hit0]
      rw [← hitd0] at hit0
      obtain ⟨r0, a0, hp, hr0, hlive, haddrr, hlenr, halr⟩ := hrel.ret d0 hd0
      have haddr0 := hrel.addrs 0 d0 hd0
      simp only [AddrOk, harr0, htup0] at haddr0
      have hRet := evalReturn_callee hframe d0 hd0 hit0 haddr0 r0 a0 hp hr0 hlive haddrr
        hlenr halr
      obtain ⟨_, slot0, _, hs0⟩ := hframe.slot_exists 0 hn0
      have hslot0 := hrel.slots 0 d0 slot0 hd0 hs0
      simp only [DeclSlotOk, harr0, htup0] at hslot0
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
        have hv : Value.scalar sc = .scalar ⟨sc.bits, (itOf body.layouts d0).size.bytes⟩ := by
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

/-- From `StartRel` (Anneal at `(0, 0)` and MiniRust at `f.start`), one
`Machine::step` executes `minimize`'s `initBlock` (`Goto(bb0)`) and lands in
`StateRel`. -/
theorem step_start {body : CapturedMir} {f : Gen.Function} (hf : translateFn body = some f)
    {ctx : Ctx} {s : MachineState} {mInit : Mach} (hstart : StartRel body f ctx s mInit) :
    ∃ m0, Interp.step mInit = .ok m0 ∧ StateRel body f ctx s m0 := by
  obtain ⟨hfstart, _⟩ := translateFn_start body f hf
  have hframe : { calleeFrame f ctx body.localDecls.length 0 0 with next_block := f.start } =
      calleeFrame f ctx body.localDecls.length body.basicBlocks.length 0 := by
    simp [calleeFrame, hfstart]
  have hshape : Shape mInit ctx
      [ctx.caller, calleeFrame f ctx body.localDecls.length body.basicBlocks.length 0]
      (ctx.base ++ localAllocs body.layouts ctx body.localDecls s.frame.locals) :=
    ⟨hframe ▸ hstart.threads, hstart.active, hstart.allocs⟩
  obtain ⟨m0, hm0, h0⟩ := step_initBlock hf hshape
  refine ⟨m0, hm0, {
    threads := by simpa [hstart.blk0, hstart.stmt0] using h0.threads
    active := h0.active
    allocs := h0.allocs
    blk := by rw [hstart.blk0]; exact hstart.hasBlocks
    stmt := fun _ _ => by rw [hstart.stmt0]; exact Nat.zero_le _
    nlocals := hstart.nlocals
    slots := hstart.slots
    addrs := hstart.addrs
    ret := hstart.ret
    borrows := hstart.borrows
    callStack := hstart.callStack
    activeCallee := hstart.activeCallee
    protectors := hstart.protectors
    callerLocals := hstart.callerLocals
  }⟩

theorem initLocalsAux_one_spec (layouts : Layout.LayoutTable) (ds : List LocalDecl) (vs : List Value)
    (h : argsOkAux layouts ds vs = true) :
    (initLocalsAux 1 ds vs).length = ds.length ∧
    ∀ (k : Nat) d slot, ds[k]? = some d → (initLocalsAux 1 ds vs)[k]? = some slot →
      DeclSlotOk layouts d slot := by
  induction ds generalizing vs with
  | nil =>
    cases vs with
    | nil => simp [initLocalsAux]
    | cons _ _ => simp [argsOkAux] at h
  | cons d ds ih =>
    cases vs with
    | nil => simp [argsOkAux] at h
    | cons v vs =>
      simp only [argsOkAux, Bool.and_eq_true] at h
      obtain ⟨hv, hvs⟩ := h
      obtain ⟨hlen, hslots⟩ := ih vs hvs
      have hvslot : DeclSlotOk layouts d (.init v) := by
        unfold declArgOk at hv
        unfold DeclSlotOk
        cases ha : arrayTypeOf d.ty with
        | none =>
          cases ht : tupleTypeOf layouts d.ty with
          | none =>
            simp only [ha, ht] at hv ⊢
            cases v <;> simp [argOk, SlotOk] at hv ⊢
            exact hv
          | some p =>
            obtain ⟨fields, size, align⟩ := p
            simp only [ha, ht, Bool.and_eq_true] at hv ⊢
            exact hv
        | some p =>
          obtain ⟨elemIt, count⟩ := p
          simp only [ha] at hv ⊢
          cases v with
          | aggregate vIdx elems =>
            cases vIdx with
            | zero =>
              simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hv
              refine ⟨hv.1, fun elem helem => ?_⟩
              have harg := hv.2 elem helem
              cases elem <;> simp [argOk, ElemOk] at harg ⊢
              exact harg
            | succ _ => simp at hv
          | _ => simp at hv
      have hcons : initLocalsAux 1 (d :: ds) (v :: vs) = .init v :: initLocalsAux 1 ds vs := rfl
      rw [hcons]
      refine ⟨by simp [hlen], fun k d' slot' hd' hs' => ?_⟩
      cases k with
      | zero =>
        simp at hd' hs'
        subst hd'; subst hs'
        exact hvslot
      | succ k =>
        simp at hd' hs'
        exact hslots k d' slot' hd' hs'

/-- General entry-state bridge: for any fragment `body`, well-typed `args`, and
well-formed caller context `ctx`, Anneal's `initMachineState body args`
(the initial state of `mirCallTree body args`) satisfies `StartRel` against any
MiniRust machine positioned at `f.start` with matching stack and local
allocations. -/
theorem initMachineState_startRel {body : CapturedMir} {f : Gen.Function}
    (hfrag : inFragment body = true) (ctx : Ctx) (hctx : CtxOk body ctx)
    (args : List Value) (hargs : argsOk body args = true) (mInit : Mach)
    (hthreads : mInit.threads =
      [thread1 ctx [ctx.caller,
        { calleeFrame f ctx body.localDecls.length 0 0 with next_block := f.start }]])
    (hactive : mInit.active_thread = 0)
    (hallocs : mInit.mem.memory.allocations =
      ctx.base ++ localAllocs body.layouts ctx body.localDecls (initMachineState body args).frame.locals) :
    StartRel body f ctx (initMachineState body args) mInit := by
  have hbne : body.basicBlocks ≠ [] := by
    simp only [inFragment, Bool.and_eq_true, decide_eq_true_eq] at hfrag
    exact hfrag.1.1.2
  obtain ⟨_, hdeclLen, _, hret0, _⟩ := inFragment_spec body hfrag
  cases hdecls : body.localDecls with
  | nil => simp [hdecls] at hdeclLen
  | cons d0 ds =>
    have hargs' : argsOkAux body.layouts ds args = true := by simpa [argsOk, hdecls] using hargs
    obtain ⟨hlen, hslots⟩ := initLocalsAux_one_spec body.layouts ds args hargs'
    have hinit : (initMachineState body args).frame.locals = .uninit :: initLocalsAux 1 ds args := by
      simp [initMachineState, hdecls, initLocalsAux]
    refine {
      threads := hthreads
      active := hactive
      allocs := hallocs
      blk0 := rfl
      stmt0 := rfl
      hasBlocks := by cases hbbs : body.basicBlocks with | nil => exact absurd hbbs hbne | cons _ _ => simp
      nlocals := by simp [hinit, hdecls, hlen]
      slots := by
        intro i d slot hd hs
        rw [hdecls] at hd
        rw [hinit] at hs
        cases i with
        | zero =>
          simp at hd hs
          subst hd; subst hs
          obtain ⟨it0, hit0⟩ := Option.isSome_iff_exists.mp (by simpa [hdecls] using hret0)
          simp [DeclSlotOk, arrayTypeOf_none_of_intTypeOf hit0,
            tupleTypeOf_none_of_intTypeOf hit0, SlotOk]
        | succ k =>
          simp at hd hs
          exact hslots k d slot hd hs
      addrs := hctx.addrs
      ret := hctx.ret
      borrows := rfl
      callStack := rfl
      activeCallee := rfl
      protectors := rfl
      callerLocals := rfl
    }

end MiniRustSpec.Correspondence
