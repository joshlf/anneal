-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Anneal.OpaqueCalleeTable.TableAndPruning

/-!
# `Anneal.OpaqueCalleeTable.FramesAndConeBridge`

Unconditional trusted frame lemmas (`memory.callees` / `memory.traitImpls`, including
root tail-call `tailCalleeEntryMemory` relocation and the `copy_nonoverlapping` /
`write_bytes` intrinsics), the unconditional opaque-evaluator identification, and the
bridge to `Anneal.MirLiftCore` call-cone narrowing (`callConeClosed`,
`callConeClosedPoly`).
-/

namespace Anneal.OpaqueCalleeTable

open Trusted.Effect (FailureKind Outcome)
open Trusted.ITree
open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

/-! ### Unconditional trusted frame lemma: `memory.callees` and `memory.traitImpls`

The trusted machine *reads* `Memory.callees` (callee resolution, `checkCalleeSig`) and
`Memory.traitImpls` (trait-method resolution) but never *writes* them: every `evalStmt`,
`evalTerminator`, intrinsic helper, frame push / pop, and unwind keeps both fields, and
only an external call — which ends every run below — installs an environment-supplied
memory. The lemmas in this section prove this for *every* state, statement, terminator,
and callee resolver, with no cone, monomorphism, or intrinsic side condition. They reuse
`Anneal.MirLiftCore`'s commutation lemmas for the callee-query-free fragment and handle the
remaining cases directly: function-pointer reification casts (which consult
`Memory.callees` through `checkCalleeSig`), polymorphic / trait-dispatched calls, and the
`core::intrinsics::const_eval_select` runtime callee. -/

/-- The callee frame of a machine state: its linked callee table and its registered
`TraitImplEntry` records. -/
def CalleeFrame (callees : List CapturedMir) (traitImpls : List TraitImplEntry)
    (s : MachineState) : Prop :=
  s.memory.callees = callees ∧ s.memory.traitImpls = traitImpls

/-- Every continuing (`.tau` or observation) successor of `n` keeps the callee table and the
trait impls of `s`. -/
abbrev FramesStep (s : MachineState) (n : MirStepNode) : Prop :=
  MirLiftCore.NodeSuccs (CalleeFrame s.memory.callees s.memory.traitImpls) n

/-- A step that is a fixed point of `Memory.withCalleeCtx` at `s`'s own context frames `s`. -/
theorem framesStep_of_ctx_fixed {s : MachineState} {n : MirStepNode}
    (hfix : n = MirLiftCore.MirStepNode.mapMem
      (MirLiftCore.Memory.withCalleeCtx s.memory.callees s.memory.activeCallee
        s.memory.traitImpls) n) :
    FramesStep s n :=
  MirLiftCore.nodeSuccs_of_fixed hfix fun s' hs' => by
    have hm : s'.memory = MirLiftCore.Memory.withCalleeCtx s.memory.callees
        s.memory.activeCallee s.memory.traitImpls s'.memory :=
      congrArg MachineState.memory hs'
    exact ⟨by rw [hm], by rw [hm]⟩

/-- A silent step to a state with the same callee table and trait impls frames `s`. -/
theorem framesStep_step {s st : MachineState} (hc : st.memory.callees = s.memory.callees)
    (ht : st.memory.traitImpls = s.memory.traitImpls) : FramesStep s (MirStepNode.step st) :=
  ⟨hc, ht⟩

/-- `writeIntrinsicReturn` frames its state. -/
theorem writeIntrinsicReturn_frames (s : MachineState) (locals' : List LocalSlot)
    (destination : Place) (targetBb : BasicBlockIdx) (retVal : Value) :
    FramesStep s (writeIntrinsicReturn s locals' destination targetBb retVal) :=
  framesStep_of_ctx_fixed
    (MirLiftCore.writeIntrinsicReturn_calleeCtx_preserved s locals' destination targetBb retVal)

/-- `writeIntrinsicScalarResult` frames its state. -/
theorem writeIntrinsicScalarResult_frames (s : MachineState) (locals' : List LocalSlot)
    (destination : Place) (targetBb : BasicBlockIdx) (resOpt : Option ScalarInt) :
    FramesStep s (writeIntrinsicScalarResult s locals' destination targetBb resOpt) := by
  have h := MirLiftCore.writeIntrinsicScalarResult_withCalleeCtx s.memory.callees
    s.memory.activeCallee s.memory.traitImpls s locals' destination targetBb resOpt
  rw [MirLiftCore.MachineState.withCalleeCtx_self] at h
  exact framesStep_of_ctx_fixed h

/-- Every inline (non-`const_eval_select`) compiler intrinsic frames its state. -/
theorem evalNonSelectIntrinsicCall_frames (kind : RustIntrinsicKind) (s : MachineState)
    (target : ResolvedCallTarget) (bodyLocalDecls : List LocalDecl) (bodyLayouts : LayoutTable)
    (argOps : List Operand) (argVals : List Value) (locals' : List LocalSlot)
    (destination : Place) (targetBb : BasicBlockIdx) :
    FramesStep s (evalNonSelectIntrinsicCall kind s target bodyLocalDecls bodyLayouts
      argOps argVals locals' destination targetBb) :=
  framesStep_of_ctx_fixed
    (MirLiftCore.evalNonSelectIntrinsicCall_calleeCtx_preserved kind s target bodyLocalDecls
      bodyLayouts argOps argVals locals' destination targetBb)

/-- A modeled core memory / pointer intrinsic step frames its state. -/
theorem evalCoreMemPtrIntrinsicCall?_frames {kind : RustIntrinsicKind} {s : MachineState}
    {target : ResolvedCallTarget} {bodyLocalDecls : List LocalDecl} {bodyLayouts : LayoutTable}
    {argOps : List Operand} {argVals : List Value} {locals' : List LocalSlot}
    {destination : Place} {targetOpt : Option BasicBlockIdx} {n : MirStepNode}
    (h : evalCoreMemPtrIntrinsicCall? kind s target bodyLocalDecls bodyLayouts argOps argVals
      locals' destination targetOpt = some n) :
    FramesStep s n :=
  framesStep_of_ctx_fixed
    (MirLiftCore.evalCoreMemPtrIntrinsicCall?_calleeCtx_preserved kind s target bodyLocalDecls
      bodyLayouts argOps argVals locals' destination targetOpt h)

/-- A diverging intrinsic step faults or is unsupported, so it frames its state. -/
theorem evalDivergingRustIntrinsic?_frames {s : MachineState} {target : ResolvedCallTarget}
    {bodyLocalDecls : List LocalDecl} {bodyLayouts : LayoutTable} {argOps : List Operand}
    {argVals : List Value} {locals' : List LocalSlot} {destination : Place} {n : MirStepNode}
    (h : evalDivergingRustIntrinsic? s target bodyLocalDecls bodyLayouts argOps argVals locals'
      destination = some n) :
    FramesStep s n := by
  rcases Anneal.PureMirExec.evalDivergingRustIntrinsic?_eq_none_or_fault s target bodyLocalDecls
      bodyLayouts argOps argVals locals' destination with h1 | ⟨fk, h1⟩ | h1 <;>
    rw [h1] at h
  · nomatch h
  · injection h with h; subst h; exact True.intro
  · injection h with h; subst h; exact True.intro

/-- Unwinding through saved caller frames keeps the callee table and trait impls of the
unwound memory. -/
theorem unwindFromCallStack_frames :
    ∀ (stk : List SavedCallerFrame) (m : Memory) (s' : MachineState),
      unwindFromCallStack stk m = .running s' →
        s'.memory.callees = m.callees ∧ s'.memory.traitImpls = m.traitImpls
  | [], m, _, h => by
    unfold unwindFromCallStack at h
    cases hc : m.rootUnwindCeiling <;> rw [hc] at h <;> nomatch h
  | caller :: rest, m, s', h => by
    unfold unwindFromCallStack at h
    dsimp only at h
    cases hr : caller.returnUnwind with
    | unreachable => rw [hr] at h; dsimp only at h; cases h
    | terminate => rw [hr] at h; dsimp only at h; cases h
    | continue_ =>
      rw [hr] at h
      dsimp only at h
      exact unwindFromCallStack_frames rest
        { m with
          callStack := rest
          activeCallee := some caller.callerBody
          activeProtectors := restoreCallerProtectors caller } s' h
    | cleanup bb =>
      rw [hr] at h
      dsimp only at h
      cases h
      exact ⟨rfl, rfl⟩

/-- A resolved unwind action keeps the callee table and trait impls of its state. -/
theorem applyUnwindAction_frames {s : MachineState} {l : List LocalSlot} {u : UnwindAction}
    {s' : MachineState} (h : applyUnwindAction s l s.memory u = .running s') :
    CalleeFrame s.memory.callees s.memory.traitImpls s' := by
  cases u with
  | unreachable => cases h
  | terminate => cases h
  | continue_ => exact unwindFromCallStack_frames s.memory.callStack s.memory s' h
  | cleanup bb => cases h; exact ⟨rfl, rfl⟩

/-- `TerminatorKind.return_` into a saved caller keeps the callee table and trait impls. -/
theorem calleeFrame_return {s : MachineState} {caller : SavedCallerFrame}
    {rest : List SavedCallerFrame} {retVal : Value} {locals' : List LocalSlot} {mem' : Memory}
    {F : StackFrame}
    (h_w : writeReturnDestination caller.frame.locals (MirLiftCore.ccReturnCallerMem s caller rest)
      caller.destination retVal caller.callerBody.localDecls caller.callerBody.layouts =
        .ok locals' mem') :
    CalleeFrame s.memory.callees s.memory.traitImpls { frame := F, memory := mem' } := by
  obtain ⟨hc, _, ht⟩ := MirLiftCore.writeReturnDestination_ctx_preserved h_w
  exact ⟨hc, ht⟩

/-- `internFnPtr` (function-pointer reification) only extends `Memory.fnPtrs`. -/
theorem internFnPtr_keepsCtx {mem : Memory} {defPath : DefPath} {typeArgs : List RigidTy}
    {fnSig : Option RigidTy} {allocId : AllocId} {mem' : Memory}
    (h : internFnPtr mem defPath typeArgs fnSig = (allocId, mem')) :
    mem'.callees = mem.callees ∧ mem'.activeCallee = mem.activeCallee ∧
      mem'.traitImpls = mem.traitImpls := by
  unfold internFnPtr at h
  split at h <;> (injection h with _ h₂; subst h₂; exact ⟨rfl, rfl, rfl⟩)

/-- Result-memory predicate of an rvalue evaluation: the callee context (`callees`,
`activeCallee`, `traitImpls`) of `mem` is kept. -/
def RvalueKeepsCtx (mem : Memory) : RvalueEvalResult → Prop
  | .ok _ _ mem' =>
    mem'.callees = mem.callees ∧ mem'.activeCallee = mem.activeCallee ∧
      mem'.traitImpls = mem.traitImpls
  | .ub => True
  | .unsupported => True

/-- **Every** rvalue evaluation keeps the callee context of its memory, including the
function-pointer reification casts that read `Memory.callees` through `checkCalleeSig`
(`Rvalue.calleeQueryFree rv = false`). -/
theorem evalRvalue_keepsCtx (locals : List LocalSlot) (rv : Rvalue) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    RvalueKeepsCtx mem (evalRvalue locals rv mem localDecls layouts) := by
  cases h_free : MirLiftCore.Rvalue.calleeQueryFree rv with
  | true =>
    have hfix := MirLiftCore.evalRvalue_withCalleeCtx mem.callees mem.activeCallee
      mem.traitImpls locals rv mem localDecls layouts h_free
    change evalRvalue locals rv mem localDecls layouts = _ at hfix
    revert hfix
    cases evalRvalue locals rv mem localDecls layouts with
    | ok v l m =>
      intro hfix
      injection hfix with _ _ hm
      exact ⟨by rw [hm], by rw [hm], by rw [hm]⟩
    | ub => intro _; exact True.intro
    | unsupported => intro _; exact True.intro
  | false =>
    cases rv with
    | cast kind op ty =>
      cases kind with
      | pointerCoercion ck =>
        have h' : (!isReifyFnPointerCoercion ck || stringEq ck "UnsafeFnPointer") = false := h_free
        cases h_r : isReifyFnPointerCoercion ck with
        | false => rw [h_r] at h'; nomatch h'
        | true =>
          cases h_s : stringEq ck "UnsafeFnPointer" with
          | true => rw [h_r, h_s] at h'; nomatch h'
          | false =>
            show RvalueKeepsCtx mem (evalReifyFnPointer locals op ty mem localDecls layouts ck)
            unfold evalReifyFnPointer
            simp only [h_r, h_s]
            repeat' (first
              | exact True.intro
              | exact ⟨rfl, rfl, rfl⟩
              | exact internFnPtr_keepsCtx ‹_›
              | split
              | (dsimp only))
      | _ => nomatch h_free
    | _ => nomatch h_free

/-- Assignment-destination write of `evalStmt`'s `.assign` arm, after the rvalue has
evaluated to `val` with frame locals `locals₁` and memory `mem₁` (non-dereferencing
projected destination). Agrees with the trusted arm by `evalStmt_assign_eq`. -/
def assignNonDerefStep
    (s : MachineState) (dstLoc : Local) (proj : List ProjectionElem)
    (val : Value) (locals₁ : List LocalSlot) (mem₁ : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) : MirStepNode :=
  let decls' := eraseLeadingOpaqueCastDecls localDecls layouts dstLoc proj
  match get? locals₁ dstLoc with
  | .some (.init rootVal) =>
    match
      ensureNestedFieldShells
        rootVal
        proj
        decls'
        layouts
        (placeTy decls' layouts { local_ := dstLoc, projection := .nil })
    with
    | .none => MirStepNode.fail .ub
    | .some shelledRoot =>
      match
        writeProjectedForLocal
          locals₁
          decls'
          layouts
          dstLoc
          shelledRoot
          proj
          val
      with
      | .ok rootVal' =>
        match set? locals₁ dstLoc (.init rootVal') with
        | .some locals₂ =>
          let resolvedLocalProj :=
            resolveBorrowWriteLocalProj decls' layouts locals₁ dstLoc proj
          match mem₁.activeProtectors with
          | .nil =>
            let borrows' :=
              invalidateConflictingBorrowsAtProj
                mem₁.borrows dstLoc .none resolvedLocalProj 0 0 (length mem₁.callStack)
            MirStepNode.step
              (advanceStmt s locals₂ { mem₁ with borrows := borrows' })
          | protHead :: protTail =>
            match
              hasProtectedWriteConflict
                mem₁.borrows (protHead :: protTail) dstLoc .none resolvedLocalProj 0 0
                (length mem₁.callStack)
            with
            | true => MirStepNode.fail .ub
            | false =>
              let borrows' :=
                invalidateConflictingBorrowsAtProj
                  mem₁.borrows dstLoc .none resolvedLocalProj 0 0 (length mem₁.callStack)
              MirStepNode.step
                (advanceStmt s locals₂ { mem₁ with borrows := borrows' })
        | .none => MirStepNode.fail .ub
      | .ub => MirStepNode.fail .ub
      | .unsupported => MirStepNode.unsupported
  | .some .uninit =>
    match proj with
    | hd :: tl =>
      match uninitFieldWriteShell? localDecls layouts dstLoc hd tl with
      | .some rootVal =>
        match writeProjectedForLocal locals₁ decls' layouts dstLoc rootVal (hd :: tl) val with
        | .ok rootVal' =>
          match set? locals₁ dstLoc (.init rootVal') with
          | .some locals₂ =>
            let resolvedLocalProj :=
              resolveBorrowWriteLocalProj
                decls'
                layouts
                locals₁
                dstLoc
                (hd :: tl)
            match mem₁.activeProtectors with
            | .nil =>
              let borrows' :=
                invalidateConflictingBorrowsAtProj
                  mem₁.borrows dstLoc .none resolvedLocalProj 0 0 (length mem₁.callStack)
              MirStepNode.step
                (advanceStmt s locals₂ { mem₁ with borrows := borrows' })
            | protHead :: protTail =>
              match
                hasProtectedWriteConflict
                  mem₁.borrows (protHead :: protTail) dstLoc .none resolvedLocalProj 0 0
                  (length mem₁.callStack)
              with
              | true => MirStepNode.fail .ub
              | false =>
                let borrows' :=
                  invalidateConflictingBorrowsAtProj
                    mem₁.borrows dstLoc .none resolvedLocalProj 0 0 (length mem₁.callStack)
                MirStepNode.step
                  (advanceStmt s locals₂ { mem₁ with borrows := borrows' })
          | .none => MirStepNode.fail .ub
        | .ub => MirStepNode.fail .ub
        | .unsupported => MirStepNode.unsupported
      | .none => MirStepNode.fail .ub
    | .nil => MirStepNode.fail .ub
  | .some .dead => MirStepNode.fail .ub
  | .none => MirStepNode.fail .ub

/-- Assignment-destination write of `evalStmt`'s `.assign` arm (unprojected, dereferencing,
and projected destinations), after the rvalue has evaluated to `val` with frame locals
`locals₁` and memory `mem₁`; agrees with the trusted arm by `evalStmt_assign_eq`. -/
def assignDstStep
    (s : MachineState) (dst : Place) (val : Value)
    (locals₁ : List LocalSlot) (mem₁ : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) : MirStepNode :=
  match dst.projection, stripLeadingOpaqueCast dst.projection with
  | .nil, _ =>
    match get? locals₁ dst.local_ with
    | .some .dead => MirStepNode.fail .ub
    | .some _ =>
      match set? locals₁ dst.local_ (.init val) with
      | .some locals₂ =>
        match mem₁.activeProtectors with
        | .nil =>
          let borrows' :=
            invalidateConflictingBorrows mem₁.borrows dst.local_ .none (length mem₁.callStack)
          MirStepNode.step
            (advanceStmt s locals₂ { mem₁ with borrows := borrows' })
        | protHead :: protTail =>
          match
            hasProtectedWriteConflict
              mem₁.borrows (protHead :: protTail) dst.local_ .none .nil 0 0
              (length mem₁.callStack)
          with
          | true => MirStepNode.fail .ub
          | false =>
            let borrows' :=
              invalidateConflictingBorrows mem₁.borrows dst.local_ .none (length mem₁.callStack)
            MirStepNode.step
              (advanceStmt s locals₂ { mem₁ with borrows := borrows' })
      | .none => MirStepNode.fail .ub
    | .none => MirStepNode.fail .ub
  | .deref :: restProj, _ =>
    match
      evalPlaceWrite locals₁ mem₁.borrows dst val mem₁.activeProtectors localDecls layouts
        mem₁.callStack
    with
    | .ok locals₂ =>
      match
        Bool.or
          (derefWriteTreeUB locals₁ mem₁.borrows dst)
          (derefWriteUnionProtectorUB
            localDecls layouts locals₁ mem₁.borrows mem₁.activeProtectors dst restProj
            mem₁.callStack)
      with
      | true => MirStepNode.fail .ub
      | false =>
        let borrows' :=
          invalidateDerefWriteBorrowsWithLayouts
            localDecls layouts locals₁ mem₁.borrows dst restProj mem₁.callStack
        MirStepNode.step (advanceStmt s locals₂ { mem₁ with borrows := borrows' })
    | .ub =>
      match mem₁.callStack with
      | .nil =>
        match mem₁.callerLocals with
        | .nil => MirStepNode.fail .ub
        | _ :: _ =>
          match
            evalCallerPlaceWrite
              locals₁ mem₁.callerLocals mem₁.borrows dst val mem₁.activeProtectors
          with
          | .ok callerLocals' =>
            match derefWriteTreeUB locals₁ mem₁.borrows dst with
            | true => MirStepNode.fail .ub
            | false =>
              let borrows' :=
                invalidateDerefWriteBorrows
                  locals₁ mem₁.borrows dst restProj mem₁.callerLocals
              MirStepNode.step
                (advanceStmt s locals₁
                  { mem₁ with borrows := borrows', callerLocals := callerLocals' })
          | .ub => MirStepNode.fail .ub
          | .unsupported => MirStepNode.unsupported
      | _ :: _ =>
        evalForeignFrameDerefWrite s locals₁ mem₁ dst restProj val localDecls layouts
    | .unsupported => MirStepNode.unsupported
  | .opaqueCast _ :: _, .nil =>
    match get? locals₁ dst.local_ with
    | .some .dead => MirStepNode.fail .ub
    | .some _ =>
      match set? locals₁ dst.local_ (.init val) with
      | .some locals₂ =>
        match mem₁.activeProtectors with
        | .nil =>
          let borrows' :=
            invalidateConflictingBorrows mem₁.borrows dst.local_ .none (length mem₁.callStack)
          MirStepNode.step
            (advanceStmt s locals₂ { mem₁ with borrows := borrows' })
        | protHead :: protTail =>
          match
            hasProtectedWriteConflict
              mem₁.borrows (protHead :: protTail) dst.local_ .none .nil 0 0
              (length mem₁.callStack)
          with
          | true => MirStepNode.fail .ub
          | false =>
            let borrows' :=
              invalidateConflictingBorrows mem₁.borrows dst.local_ .none (length mem₁.callStack)
            MirStepNode.step
              (advanceStmt s locals₂ { mem₁ with borrows := borrows' })
      | .none => MirStepNode.fail .ub
    | .none => MirStepNode.fail .ub
  | hd :: tl, _ =>
    assignNonDerefStep s dst.local_ (hd :: tl) val locals₁ mem₁ localDecls layouts

/-- The trusted `.assign` arm of `evalStmt` is the rvalue evaluation followed by
`assignDstStep`. -/
theorem evalStmt_assign_eq (s : MachineState) (dst : Place) (rv : Rvalue) (span : String)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalStmt s ⟨.assign dst rv, span⟩ localDecls layouts =
      match evalRvalue s.frame.locals rv s.memory localDecls layouts with
      | .ok val locals₁ mem₁ => assignDstStep s dst val locals₁ mem₁ localDecls layouts
      | .ub => MirStepNode.fail .ub
      | .unsupported => MirStepNode.unsupported := by
  unfold evalStmt
  dsimp only
  cases evalRvalue s.frame.locals rv s.memory localDecls layouts with
  | ub => rfl
  | unsupported => rfl
  | ok val locals₁ mem₁ =>
    rcases dst with ⟨dstLoc, dstProj⟩
    cases dstProj with
    | nil => rfl
    | cons hd tl => cases hd <;> rfl

/-- The assignment write frames `s` whenever the rvalue kept `s`'s callee context. -/
theorem assignDstStep_frames {s : MachineState} {dst : Place} {val : Value}
    {locals₁ : List LocalSlot} {mem₁ : Memory} {localDecls : List LocalDecl}
    {layouts : LayoutTable}
    (h : mem₁.callees = s.memory.callees ∧ mem₁.activeCallee = s.memory.activeCallee ∧
      mem₁.traitImpls = s.memory.traitImpls) :
    FramesStep s (assignDstStep s dst val locals₁ mem₁ localDecls layouts) := by
  have hforeign : ∀ restProj, FramesStep s
      (evalForeignFrameDerefWrite s locals₁ mem₁ dst restProj val localDecls layouts) := by
    intro restProj
    have hg : MirLiftCore.Memory.withCalleeCtx s.memory.callees s.memory.activeCallee
        s.memory.traitImpls mem₁ = mem₁ := by
      rw [← h.1, ← h.2.1, ← h.2.2]
    have hfix := MirLiftCore.evalForeignFrameDerefWrite_withCalleeCtx s.memory.callees
      s.memory.activeCallee s.memory.traitImpls s locals₁ mem₁ dst restProj val localDecls
      layouts
    rw [MirLiftCore.MachineState.withCalleeCtx_self, hg] at hfix
    exact framesStep_of_ctx_fixed hfix
  unfold assignDstStep assignNonDerefStep
  repeat' (first
    | exact True.intro
    | exact framesStep_step h.1 h.2.2
    | exact hforeign _
    | split
    | (dsimp only))

/-- **Statement frame lemma**: every trusted `evalStmt` step frames its state. -/
theorem evalStmt_frames (s : MachineState) (stmt : Statement) (localDecls : List LocalDecl)
    (layouts : LayoutTable) : FramesStep s (evalStmt s stmt localDecls layouts) := by
  rcases stmt with ⟨kind, span⟩
  cases kind with
  | assign dst rv =>
    rw [evalStmt_assign_eq]
    have hrv := evalRvalue_keepsCtx s.frame.locals rv s.memory localDecls layouts
    revert hrv
    cases evalRvalue s.frame.locals rv s.memory localDecls layouts with
    | ok val locals₁ mem₁ => intro hrv; exact assignDstStep_frames hrv
    | ub => intro _; exact True.intro
    | unsupported => intro _; exact True.intro
  | _ =>
    exact framesStep_of_ctx_fixed
      (MirLiftCore.evalStmt_calleeCtx_preserved s _ localDecls layouts rfl)

/-- Every trusted direct compiler-intrinsic step — including the `const_eval_select`
runtime callee, which is resolved through the trusted `lookupCallee s.memory.callees` and
entered with `pushCalleeFrame` — frames its state. -/
theorem evalDirectRustIntrinsic?_frames {s : MachineState} {currentBody : Option CapturedMir}
    {target : ResolvedCallTarget} {bodyLocalDecls : List LocalDecl} {bodyLayouts : LayoutTable}
    {argOps : List Operand} {argVals : List Value} {locals' : List LocalSlot}
    {destination : Place} {targetBb : BasicBlockIdx} {unwind : UnwindAction} {n : MirStepNode}
    (h : evalDirectRustIntrinsic? s currentBody target bodyLocalDecls bodyLayouts argOps argVals
      locals' destination targetBb unwind = some n) :
    FramesStep s n := by
  unfold evalDirectRustIntrinsic? at h
  split at h
  · nomatch h
  · injection h with h
    subst h
    repeat' (first
      | exact True.intro
      | exact framesStep_step rfl rfl
      | exact writeIntrinsicScalarResult_frames _ _ _ _ _
      | exact evalNonSelectIntrinsicCall_frames _ _ _ _ _ _ _ _ _ _
      | exact evalCoreMemPtrIntrinsicCall?_frames ‹_›
      | exact applyUnwindAction_frames ‹_›
      | (dsimp only)
      | split)
  · injection h with h
    subst h
    exact framesStep_of_ctx_fixed
      (MirLiftCore.evalCopyNonOverlappingCall_calleeCtx_preserved _ _ _ _ _ _ _ _)
  · injection h with h
    subst h
    exact framesStep_of_ctx_fixed
      (MirLiftCore.evalWriteBytesCall_calleeCtx_preserved _ _ _ _ _ _ _ _ _)
  · injection h with h
    subst h
    split
    · exact evalCoreMemPtrIntrinsicCall?_frames ‹_›
    · exact evalNonSelectIntrinsicCall_frames _ _ _ _ _ _ _ _ _ _

/-- Root tail-call entry relocation (`tailCalleeEntryMemory` / `relocateRootCallerReferents`)
keeps the callee table. -/
theorem tailCalleeEntryMemory_callees (stk : List SavedCallerFrame) (m : Memory)
    (nOld nNew : Nat) : (tailCalleeEntryMemory stk m nOld nNew).callees = m.callees := by
  cases stk <;> unfold tailCalleeEntryMemory relocateRootCallerReferents <;>
    repeat' (first | rfl | split)

/-- Root tail-call entry relocation (`tailCalleeEntryMemory` / `relocateRootCallerReferents`)
keeps the registered trait impls. -/
theorem tailCalleeEntryMemory_traitImpls (stk : List SavedCallerFrame) (m : Memory)
    (nOld nNew : Nat) : (tailCalleeEntryMemory stk m nOld nNew).traitImpls = m.traitImpls := by
  cases stk <;> unfold tailCalleeEntryMemory relocateRootCallerReferents <;>
    repeat' (first | rfl | split)

/-- Root tail-call entry relocation keeps the saved call stack. -/
theorem tailCalleeEntryMemory_callStack (stk : List SavedCallerFrame) (m : Memory)
    (nOld nNew : Nat) : (tailCalleeEntryMemory stk m nOld nNew).callStack = m.callStack := by
  cases stk <;> unfold tailCalleeEntryMemory relocateRootCallerReferents <;>
    repeat' (first | rfl | split)

/-- **Terminator frame lemma** for *every* callee resolver and pruning mode: every
`stepTerminatorWith` step frames its state. Instantiated at the memory's own list resolver
it is the trusted `evalTerminator` (`stepTerminatorWith_list_eq_trusted`). -/
theorem stepTerminatorWith_frames (prune : Bool) (resolve : CalleeResolver) (s : MachineState)
    (term : Terminator) (currentBody : Option CapturedMir) :
    FramesStep s (stepTerminatorWith prune resolve s term currentBody) := by
  have hself : CalleeFrame s.memory.callees s.memory.traitImpls s := ⟨rfl, rfl⟩
  rcases term with ⟨kind, span⟩
  cases kind with
  | goto target => exact hself
  | switchInt discr targets =>
    unfold stepTerminatorWith evalTerminator
    dsimp only
    repeat' (first | exact True.intro | exact hself | (dsimp only) | split)
  | unwindResume =>
    show FramesStep s (evalTerminator s ⟨.unwindResume, span⟩ currentBody)
    unfold evalTerminator
    dsimp only
    repeat' (first
      | exact True.intro
      | exact unwindFromCallStack_frames s.memory.callStack s.memory _ ‹_›
      | (dsimp only)
      | split)
  | unwindTerminate => exact True.intro
  | return_ =>
    show FramesStep s (evalTerminator s ⟨.return_, span⟩ currentBody)
    rw [MirLiftCore.ccEvalReturn_eq]
    unfold MirLiftCore.ccEvalReturn
    repeat' (first | exact True.intro | exact calleeFrame_return ‹_› | (dsimp only) | split)
  | unreachable => exact True.intro
  | drop place target unwind =>
    show FramesStep s (evalTerminator s ⟨.drop place target unwind, span⟩ currentBody)
    unfold evalTerminator
    dsimp only
    repeat' (first | exact True.intro | exact hself | (dsimp only) | split)
  | assert cond expected target unwind =>
    show FramesStep s (evalTerminator s ⟨.assert cond expected target unwind, span⟩ currentBody)
    unfold evalTerminator
    dsimp only
    repeat' (first | exact True.intro | exact hself | exact applyUnwindAction_frames ‹_› | (dsimp only) | split)
  | call func argOps destination target unwind =>
    cases target with
    | some targetBb =>
      unfold stepTerminatorWith
      dsimp only
      repeat' (first
        | exact True.intro
        | exact hself
        | exact writeIntrinsicReturn_frames _ _ _ _ _
        | exact evalDirectRustIntrinsic?_frames ‹_›
        | (dsimp only)
        | split)
    | none =>
      unfold stepTerminatorWith
      dsimp only
      repeat' (first
        | exact True.intro
        | exact hself
        | exact applyUnwindAction_frames ‹_›
        | exact evalDivergingRustIntrinsic?_frames ‹_›
        | (dsimp only)
        | split)
  | tailCall func argOps =>
    unfold stepTerminatorWith tailCallWith
    dsimp only
    repeat' (first
      | exact True.intro
      | exact framesStep_step rfl rfl
      | exact framesStep_step (tailCalleeEntryMemory_callees _ _ _ _)
          (tailCalleeEntryMemory_traitImpls _ _ _ _)
      | (dsimp only)
      | split)
  | _ => exact True.intro

/-- `stepMirFnWith` frames its state whenever its terminator step does. -/
theorem stepMirFnWith_frames
    {termStep : MachineState → Terminator → Option CapturedMir → MirStepNode}
    (hterm : ∀ s term cb, FramesStep s (termStep s term cb)) (body : CapturedMir)
    (s : MachineState) : FramesStep s (stepMirFnWith termStep body s) := by
  unfold stepMirFnWith
  dsimp only
  split
  · exact True.intro
  · cases h_bb : get? (s.memory.activeCallee.getD body).basicBlocks s.frame.blockIdx with
    | none => exact True.intro
    | some blk =>
      dsimp only
      cases h_st : get? blk.statements s.frame.stmtIdx with
      | some stmt => exact evalStmt_frames s stmt _ _
      | none =>
        dsimp only
        split
        · exact hterm _ _ _
        · exact True.intro

/-- **Pruned-step frame lemma**: a branch-pruned step under *any* callee resolver (in
particular any opaque table, however it relates to `s.memory.callees`) frames its state. -/
theorem stepBranchPruned_frames (resolve : CalleeResolver) (body : CapturedMir)
    (s : MachineState) : FramesStep s (stepBranchPruned resolve body s) :=
  stepMirFnWith_frames (stepTerminatorWith_frames true resolve) body s

/-- **Unconditional trusted frame lemma**: every trusted `stepMirFn` step keeps
`memory.callees` and `memory.traitImpls` in every continuing successor. -/
theorem stepMirFn_frames (body : CapturedMir) (s : MachineState) :
    FramesStep s (stepMirFn body s) := by
  rw [← stepListUnpruned_eq_trusted]
  exact stepMirFnWith_frames (stepTerminatorWith_frames false _) body s

/-- A successor exposed by `viewStepNode` satisfies every `NodeSuccs` invariant. -/
theorem nodeSuccs_of_view {P : MachineState → Prop} {n : MirStepNode} {obs : Option MirObs}
    {s' : MachineState} (hn : MirLiftCore.NodeSuccs P n)
    (hv : viewStepNode n = .cont obs (.running s')) : P s' := by
  rcases n with out | st | ⟨e, k⟩
  · nomatch hv
  · change StepView.cont none st = .cont obs (.running s') at hv
    injection hv with _ hst
    subst hst
    exact hn
  · rcases e with fk | x | c
    · cases fk with
      | fail kind => nomatch hv
    · cases x with
      | emit ev =>
        change StepView.cont (some ev) (k PUnit.unit) = .cont obs (.running s') at hv
        injection hv with _ hk
        change (match k PUnit.unit with
          | .running s' => P s'
          | _ => True) at hn
        rw [hk] at hn
        exact hn
    · cases c with
      | call req => nomatch hv

/-- Every state a fuel-bounded run of a framing step function visits keeps the initial
callee table and trait impls. -/
theorem runVisited_frames {step : MachineState → MirStepNode}
    (hstep : ∀ s, FramesStep s (step s)) :
    ∀ (fuel : Nat) (s s' : MachineState), s' ∈ runVisited step fuel s →
      CalleeFrame s.memory.callees s.memory.traitImpls s'
  | 0, _, _, h => nomatch h
  | n + 1, s, s', h => by
    unfold runVisited at h
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨rfl, rfl⟩
    · split at h
      · rename_i obs s₁ hv
        have h₁ : CalleeFrame s.memory.callees s.memory.traitImpls s₁ :=
          nodeSuccs_of_view (hstep s) hv
        have h₂ := runVisited_frames hstep n s₁ s' h
        exact ⟨h₂.1.trans h₁.1, h₂.2.trans h₁.2⟩
      · nomatch h

/-- The trusted frame condition of `evalWithOpaqueCallees_eq_trusted`, strengthened to
`memory.traitImpls`: every state the pruned opaque run visits keeps the table's callee list
and the `TraitImplEntry` records `extraTraitImpls`. -/
def OpaqueRunFramed (tbl : OpaqueCalleeTable) (extraTraitImpls : List TraitImplEntry)
    (body : CapturedMir) (fuel : Nat) (s : MachineState) : Prop :=
  ∀ s' ∈ runVisited (stepBranchPruned tbl.lookup body) fuel s,
    s'.memory.callees = tbl.toList ∧ s'.memory.traitImpls = extraTraitImpls

/-- **The frame condition holds unconditionally** from every state that links the table
(`s.memory.callees = tbl.toList`) with trait impls `extraTraitImpls`. -/
theorem opaqueRunFramed_of_init (tbl : OpaqueCalleeTable) (extraTraitImpls : List TraitImplEntry)
    (body : CapturedMir) (fuel : Nat) (s : MachineState)
    (hcallees : s.memory.callees = tbl.toList) (htraits : s.memory.traitImpls = extraTraitImpls) :
    OpaqueRunFramed tbl extraTraitImpls body fuel s := fun s' hs' =>
  have h := runVisited_frames (stepBranchPruned_frames tbl.lookup body) fuel s s' hs'
  ⟨h.1.trans hcallees, h.2.trans htraits⟩

/-- Every state the iterated trusted `stepMirFn` visits keeps the initial callee table and
trait impls (no frame hypothesis). -/
theorem trusted_runVisited_frames (body : CapturedMir) (fuel : Nat) (s s' : MachineState)
    (hs' : s' ∈ runVisited (stepMirFn body) fuel s) :
    s'.memory.callees = s.memory.callees ∧ s'.memory.traitImpls = s.memory.traitImpls :=
  runVisited_frames (stepMirFn_frames body) fuel s s' hs'

/-- Multi-step trusted agreement from the strengthened frame condition. -/
theorem evalWithOpaqueCallees_eq_trusted_of_framed (tbl : OpaqueCalleeTable)
    (extraTraitImpls : List TraitImplEntry) (body : CapturedMir) (fuel : Nat) (s : MachineState)
    (hframed : OpaqueRunFramed tbl extraTraitImpls body fuel s) :
    evalWithOpaqueCallees tbl body fuel s = runSteps (stepMirFn body) fuel s [] :=
  evalWithOpaqueCallees_eq_trusted tbl body fuel s fun s' hs' => (hframed s' hs').1

/-- **Unconditional multi-step trusted agreement**: from *every* state linking the table in
`memory.callees`, the branch-pruned opaque evaluation is the iterated trusted `stepMirFn`;
the `memory.callees` / `memory.traitImpls` frame condition of
`evalWithOpaqueCallees_eq_trusted` is discharged by `stepBranchPruned_frames`. -/
theorem evalWithOpaqueCallees_eq_trusted_unconditional (tbl : OpaqueCalleeTable)
    (body : CapturedMir) (fuel : Nat) (s : MachineState)
    (hcallees : s.memory.callees = tbl.toList) :
    evalWithOpaqueCallees tbl body fuel s = runSteps (stepMirFn body) fuel s [] :=
  evalWithOpaqueCallees_eq_trusted_of_framed tbl s.memory.traitImpls body fuel s
    (opaqueRunFramed_of_init tbl s.memory.traitImpls body fuel s hcallees rfl)

/-- `initMachineStateWithCallees` links its callee list, empty or not. -/
theorem initMachineStateWithCallees_callees (body : CapturedMir) (args : List Value)
    (callees : List CapturedMir) :
    (initMachineStateWithCallees body args callees).memory.callees = callees := by
  cases callees <;> rfl

/-- `initMachineStateWithCallees` registers the root body's trait impls, empty list or not. -/
theorem initMachineStateWithCallees_traitImpls (body : CapturedMir) (args : List Value)
    (callees : List CapturedMir) :
    (initMachineStateWithCallees body args callees).memory.traitImpls = body.traitImpls := by
  cases callees <;> rfl

/-- **Unconditional agreement from `initMachineStateWithCallees`** (every table, including
the empty one). -/
theorem evalWithOpaqueCallees_eq_trusted_initWithCallees (tbl : OpaqueCalleeTable)
    (body : CapturedMir) (args : List Value) (fuel : Nat) :
    evalWithOpaqueCallees tbl body fuel (initMachineStateWithCallees body args tbl.toList) =
      runSteps (stepMirFn body) fuel (initMachineStateWithCallees body args tbl.toList) [] :=
  evalWithOpaqueCallees_eq_trusted_unconditional tbl body fuel _
    (initMachineStateWithCallees_callees body args tbl.toList)

/-- The frame condition from `initMachineStateWithCallees`: the run keeps the table and the
root body's trait impls. -/
theorem opaqueRunFramed_initWithCallees (tbl : OpaqueCalleeTable) (body : CapturedMir)
    (args : List Value) (fuel : Nat) :
    OpaqueRunFramed tbl body.traitImpls body fuel
      (initMachineStateWithCallees body args tbl.toList) :=
  opaqueRunFramed_of_init tbl body.traitImpls body fuel _
    (initMachineStateWithCallees_callees body args tbl.toList)
    (initMachineStateWithCallees_traitImpls body args tbl.toList)

/-- **Unconditional agreement from `initMachineStateWithMemoryAndCallees`** under
`MirLiftCore.CalleeInitWf`: a non-empty table, or the empty table over a clean entry memory
(`mem.callees = []`). -/
theorem evalWithOpaqueCallees_eq_trusted_initWithMemoryAndCallees_of_wf (tbl : OpaqueCalleeTable)
    (body : CapturedMir) (args : List Value) (mem : Memory) (fuel : Nat)
    (hwf : MirLiftCore.CalleeInitWf body mem tbl.toList) :
    evalWithOpaqueCallees tbl body fuel
        (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem
          tbl.toList) =
      runSteps (stepMirFn body) fuel
        (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem
          tbl.toList) [] :=
  evalWithOpaqueCallees_eq_trusted_unconditional tbl body fuel _
    (MirLiftCore.initMachineStateWithMemoryAndCallees_callees_of_wf body args mem hwf)

/-- **Unconditional agreement from `initMachineStateWithMemoryAndCallees`** for every
non-empty table (an empty table leaves the given memory's callee list in place). -/
theorem evalWithOpaqueCallees_eq_trusted_initWithMemoryAndCallees (tbl : OpaqueCalleeTable)
    (body : CapturedMir) (args : List Value) (mem : Memory) (fuel : Nat)
    (hne : tbl.toList ≠ []) :
    evalWithOpaqueCallees tbl body fuel
        (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem
          tbl.toList) =
      runSteps (stepMirFn body) fuel
        (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem
          tbl.toList) [] :=
  evalWithOpaqueCallees_eq_trusted_initWithMemoryAndCallees_of_wf tbl body args mem fuel
    (Or.inl hne)

/-- A demanded key carries the trait impls of the state demanding it. -/
theorem demandedKey?_extraTraitImpls {body : CapturedMir} {s : MachineState} {k : CalleeKey}
    (h : demandedKey? body s = some k) : k.extraTraitImpls = s.memory.traitImpls := by
  unfold demandedKey? at h
  split at h
  · unfold terminatorKey? at h
    repeat' (first | (cases h <;> rfl) | split at h)
  · nomatch h

/-- Every demanded key is demanded at a visited state. -/
theorem mem_demandedKeys_visited {resolve : CalleeResolver} {body : CapturedMir} :
    ∀ (fuel : Nat) (s : MachineState) (k : CalleeKey), k ∈ demandedKeys resolve body fuel s →
      ∃ s' ∈ runVisited (stepBranchPruned resolve body) fuel s, demandedKey? body s' = some k
  | 0, _, _, h => nomatch h
  | n + 1, s, k, h => by
    unfold demandedKeys at h
    rcases List.mem_append.mp h with h | h
    · refine ⟨s, by unfold runVisited; exact List.Mem.head _, ?_⟩
      cases hk : demandedKey? body s with
      | none => rw [hk] at h; nomatch h
      | some k' =>
        rw [hk] at h
        rw [List.mem_singleton.mp h]
    · split at h
      · rename_i obs s₁ hv
        obtain ⟨s', hs', hk⟩ := mem_demandedKeys_visited n s₁ k h
        exact ⟨s', by unfold runVisited; rw [hv]; exact List.Mem.tail _ hs', hk⟩
      · nomatch h

/-- **Every key demanded along a pruned run (under any resolver) carries the initial
trait impls**: the `extraTraitImpls` component of the call cone is fixed by the start state. -/
theorem demandedKeys_extraTraitImpls (resolve : CalleeResolver) (body : CapturedMir)
    (fuel : Nat) (s : MachineState) :
    ∀ k ∈ demandedKeys resolve body fuel s, k.extraTraitImpls = s.memory.traitImpls := by
  intro k hk
  obtain ⟨s', hs', hk'⟩ := mem_demandedKeys_visited fuel s k hk
  rw [demandedKey?_extraTraitImpls hk']
  exact (runVisited_frames (stepBranchPruned_frames resolve body) fuel s s' hs').2

/-! ### Bridge to `Anneal.MirLiftCore` call-cone narrowing

`Anneal.MirLiftCore` narrows the trusted machine's *own* callee table: replacing
`Memory.callees = c₁` by any `c₂` with `calleesAgreeOn cone c₁ c₂` (first-match `findCallee?`
agreement on a cone of definition paths) preserves every cone-safe step, bounded run
(`runCfgWithCallees`), and callee-insensitive weakest precondition (`wpMirExecSym`,
`MirWpConverges`). An opaque table plugs into that surface through its sealed list
`tbl.toList : MirLiftCore.CalleeEnv`, with agreement stated over the sealed raw lookup:
`OpaqueCalleeTable.AgreesOn cone t₁ t₂` is exactly `calleesAgreeOn cone t₁.toList
t₂.toList` (`calleesAgreeOn_toList_iff`), so a client discharges it with the same `O(1)`
`lookupRaw` certificates it uses for stepping, never unfolding `tbl.toList`. Conversely,
`AgreesOn` narrows the opaque evaluator's demanded-key cone
(`evalWithOpaqueCallees_cone_narrow_of_agreesOn`), and every halting opaque run is a
halting `runCfgWithCallees` run (`runCfgWithCallees_of_evalWithOpaqueCallees_halted`), which
`MirLiftCore` then narrows to the smaller table. -/

/-- Raw-lookup agreement of two opaque tables on a call cone of definition paths (the
opaque-table form of `MirLiftCore.calleesAgreeOn`). -/
def OpaqueCalleeTable.AgreesOn (cone : List DefPath) (t₁ t₂ : OpaqueCalleeTable) : Prop :=
  ∀ dp, dp ∈ cone → t₁.lookupRaw dp = t₂.lookupRaw dp

theorem OpaqueCalleeTable.AgreesOn.refl (cone : List DefPath) (t : OpaqueCalleeTable) :
    OpaqueCalleeTable.AgreesOn cone t t := fun _ _ => rfl

theorem OpaqueCalleeTable.AgreesOn.symm {cone : List DefPath} {t₁ t₂ : OpaqueCalleeTable}
    (h : OpaqueCalleeTable.AgreesOn cone t₁ t₂) : OpaqueCalleeTable.AgreesOn cone t₂ t₁ :=
  fun dp hdp => (h dp hdp).symm

theorem OpaqueCalleeTable.AgreesOn.trans {cone : List DefPath} {t₁ t₂ t₃ : OpaqueCalleeTable}
    (h₁₂ : OpaqueCalleeTable.AgreesOn cone t₁ t₂) (h₂₃ : OpaqueCalleeTable.AgreesOn cone t₂ t₃) :
    OpaqueCalleeTable.AgreesOn cone t₁ t₃ :=
  fun dp hdp => (h₁₂ dp hdp).trans (h₂₃ dp hdp)

/-- **`AgreesOn` is `MirLiftCore.calleesAgreeOn` on the sealed lists.** -/
theorem calleesAgreeOn_toList_iff (cone : List DefPath) (t₁ t₂ : OpaqueCalleeTable) :
    MirLiftCore.calleesAgreeOn cone t₁.toList t₂.toList ↔ OpaqueCalleeTable.AgreesOn cone t₁ t₂ := by
  constructor
  · intro h dp hdp
    rw [OpaqueCalleeTable.lookupRaw_eq, OpaqueCalleeTable.lookupRaw_eq]
    exact h dp hdp
  · intro h dp hdp
    have := h dp hdp
    rw [OpaqueCalleeTable.lookupRaw_eq, OpaqueCalleeTable.lookupRaw_eq] at this
    exact this

/-- `AgreesOn` gives `MirLiftCore.calleesAgreeOn` on the sealed lists. -/
theorem calleesAgreeOn_of_agreesOn {cone : List DefPath} {t₁ t₂ : OpaqueCalleeTable}
    (h : OpaqueCalleeTable.AgreesOn cone t₁ t₂) :
    MirLiftCore.calleesAgreeOn cone t₁.toList t₂.toList :=
  (calleesAgreeOn_toList_iff cone t₁ t₂).mpr h

/-- A single raw-lookup hit certifies that a sealed table is non-empty (the side condition
of `MirLiftCore`'s entry-state narrowing lemmas), without unfolding `tbl.toList`. -/
theorem toList_ne_nil_of_lookupRaw {tbl : OpaqueCalleeTable} {dp : DefPath} {c : CapturedMir}
    (h : tbl.lookupRaw dp = some c) : tbl.toList ≠ [] := by
  intro hnil
  rw [OpaqueCalleeTable.lookupRaw_eq, hnil] at h
  nomatch h

/-- Canonical cone narrowing of an opaque table: the bodies of `tbl` whose `defPath` lies in
`cone` (`MirLiftCore.coneBodies`), sealed again. -/
def OpaqueCalleeTable.narrowToCone (cone : List DefPath) (tbl : OpaqueCalleeTable) :
    OpaqueCalleeTable :=
  OpaqueCalleeTable.ofList (MirLiftCore.coneBodies cone tbl.toList)

/-- The canonical narrowing agrees with the table on its cone. -/
theorem lookupRaw_narrowToCone {cone : List DefPath} {dp : DefPath} (tbl : OpaqueCalleeTable)
    (hdp : dp ∈ cone) : (tbl.narrowToCone cone).lookupRaw dp = tbl.lookupRaw dp := by
  unfold OpaqueCalleeTable.narrowToCone
  rw [OpaqueCalleeTable.lookupRaw_eq, OpaqueCalleeTable.lookupRaw_eq,
    OpaqueCalleeTable.toList_ofList]
  exact MirLiftCore.findCallee?_coneBodies tbl.toList hdp

/-- `narrowToCone` always agrees with the table on its cone. -/
theorem agreesOn_narrowToCone (cone : List DefPath) (tbl : OpaqueCalleeTable) :
    OpaqueCalleeTable.AgreesOn cone tbl (tbl.narrowToCone cone) :=
  fun _ hdp => (lookupRaw_narrowToCone tbl hdp).symm

/-- A monomorphic key whose path lies in the cone resolves identically in agreeing tables. -/
theorem lookupKey_eq_of_agreesOn_mono {cone : List DefPath} {t₁ t₂ : OpaqueCalleeTable}
    {k : CalleeKey} (h : OpaqueCalleeTable.AgreesOn cone t₁ t₂) (hk : k.defPath ∈ cone)
    (hmono : k.typeArgs = []) : t₁.lookupKey k = t₂.lookupKey k := by
  obtain ⟨L, dp, tys, ti⟩ := k
  simp only at hk hmono
  subst hmono
  rw [OpaqueCalleeTable.lookupKey_eq, OpaqueCalleeTable.lookupKey_eq,
    OpaqueCalleeTable.lookup_eq, OpaqueCalleeTable.lookup_eq]
  exact MirLiftCore.lookupCallee_nil_eq_of_findCallee_eq L ti
    ((calleesAgreeOn_of_agreesOn h) dp hk)

/-- A (possibly polymorphic) key whose path lies in the cone and has no registered
`TraitImplEntry` in either table (stated over the sealed `traitImpls`) resolves identically
in agreeing tables. -/
theorem lookupKey_eq_of_agreesOn_free {cone : List DefPath} {t₁ t₂ : OpaqueCalleeTable}
    {k : CalleeKey} (h : OpaqueCalleeTable.AgreesOn cone t₁ t₂) (hk : k.defPath ∈ cone)
    (h₁ : hasTraitImplForDefPath (k.extraTraitImpls ++ t₁.traitImpls) k.defPath = false)
    (h₂ : hasTraitImplForDefPath (k.extraTraitImpls ++ t₂.traitImpls) k.defPath = false) :
    t₁.lookupKey k = t₂.lookupKey k := by
  obtain ⟨L, dp, tys, ti⟩ := k
  simp only at hk h₁ h₂
  rw [OpaqueCalleeTable.traitImpls_eq] at h₁ h₂
  rw [OpaqueCalleeTable.lookupKey_eq, OpaqueCalleeTable.lookupKey_eq,
    OpaqueCalleeTable.lookup_eq, OpaqueCalleeTable.lookup_eq]
  exact MirLiftCore.lookupCallee_eq_of_findCallee_eq_of_no_traitImpl L tys ti
    ((calleesAgreeOn_of_agreesOn h) dp hk) h₁ h₂

/-- **Cone narrowing of the opaque evaluator from `calleesAgreeOn`**: if every key the
full-table run demands is a monomorphic call into `cone`, raw-lookup agreement on `cone`
(equivalently `MirLiftCore.calleesAgreeOn cone narrowTbl.toList fullTbl.toList`) gives an
identical run. -/
theorem evalWithOpaqueCallees_cone_narrow_of_agreesOn (cone : List DefPath)
    (narrowTbl fullTbl : OpaqueCalleeTable) (body : CapturedMir) (fuel : Nat) (s : MachineState)
    (h : OpaqueCalleeTable.AgreesOn cone narrowTbl fullTbl)
    (hkeys : ∀ k ∈ demandedKeys fullTbl.lookup body fuel s, k.defPath ∈ cone ∧ k.typeArgs = []) :
    evalWithOpaqueCallees narrowTbl body fuel s = evalWithOpaqueCallees fullTbl body fuel s :=
  evalWithOpaqueCallees_cone_narrow narrowTbl fullTbl body fuel s fun k hk =>
    lookupKey_eq_of_agreesOn_mono h (hkeys k hk).1 (hkeys k hk).2

/-- **Cone narrowing of the opaque evaluator from `AgreesOn`, generic callees included**: if
every key the full-table run demands calls into `cone` and no `dp ∈ cone` is subject to
`TraitImplEntry` dispatch in either table (checked once per cone over the start state's trait
impls and the sealed `traitImpls`), raw-lookup agreement on `cone` alone gives an identical run,
for monomorphic and polymorphic (`CapturedMir.instantiate`) calls alike. Every demanded key
carries the start state's trait impls (`demandedKeys_extraTraitImpls`), so no per-key
certificate is needed. -/
theorem evalWithOpaqueCallees_cone_narrow_of_agreesOn_poly (cone : List DefPath)
    (narrowTbl fullTbl : OpaqueCalleeTable) (body : CapturedMir) (fuel : Nat) (s : MachineState)
    (h : OpaqueCalleeTable.AgreesOn cone narrowTbl fullTbl)
    (hno₁ : ∀ dp, dp ∈ cone →
      hasTraitImplForDefPath (s.memory.traitImpls ++ narrowTbl.traitImpls) dp = false)
    (hno₂ : ∀ dp, dp ∈ cone →
      hasTraitImplForDefPath (s.memory.traitImpls ++ fullTbl.traitImpls) dp = false)
    (hkeys : ∀ k ∈ demandedKeys fullTbl.lookup body fuel s, k.defPath ∈ cone) :
    evalWithOpaqueCallees narrowTbl body fuel s = evalWithOpaqueCallees fullTbl body fuel s :=
  evalWithOpaqueCallees_cone_narrow narrowTbl fullTbl body fuel s fun k hk => by
    have hextra := demandedKeys_extraTraitImpls fullTbl.lookup body fuel s k hk
    have hdp := hkeys k hk
    refine lookupKey_eq_of_agreesOn_free h hdp ?_ ?_
    · rw [hextra]
      exact hno₁ _ hdp
    · rw [hextra]
      exact hno₂ _ hdp

/-- **Narrow-run cone narrowing of the opaque evaluator from `AgreesOn`**: steps only
`narrowTbl.lookup` in `demandedKeys`, never unfolding `fullTbl` to collect demanded keys. -/
theorem evalWithOpaqueCallees_cone_narrow_of_narrow_agreesOn (cone : List DefPath)
    (narrowTbl fullTbl : OpaqueCalleeTable) (body : CapturedMir) (fuel : Nat) (s : MachineState)
    (h : OpaqueCalleeTable.AgreesOn cone narrowTbl fullTbl)
    (hkeys : ∀ k ∈ demandedKeys narrowTbl.lookup body fuel s, k.defPath ∈ cone ∧ k.typeArgs = []) :
    evalWithOpaqueCallees narrowTbl body fuel s = evalWithOpaqueCallees fullTbl body fuel s :=
  evalWithOpaqueCallees_cone_narrow_of_narrow narrowTbl fullTbl body fuel s fun k hk =>
    lookupKey_eq_of_agreesOn_mono h (hkeys k hk).1 (hkeys k hk).2

/-- **Narrow-run cone narrowing of the opaque evaluator from `AgreesOn`, generic callees included**:
like `evalWithOpaqueCallees_cone_narrow_of_agreesOn_poly`, except `hkeys` is checked along
`demandedKeys narrowTbl.lookup` so `fullTbl` is never stepped during key collection. -/
theorem evalWithOpaqueCallees_cone_narrow_of_narrow_agreesOn_poly (cone : List DefPath)
    (narrowTbl fullTbl : OpaqueCalleeTable) (body : CapturedMir) (fuel : Nat) (s : MachineState)
    (h : OpaqueCalleeTable.AgreesOn cone narrowTbl fullTbl)
    (hno₁ : ∀ dp, dp ∈ cone →
      hasTraitImplForDefPath (s.memory.traitImpls ++ narrowTbl.traitImpls) dp = false)
    (hno₂ : ∀ dp, dp ∈ cone →
      hasTraitImplForDefPath (s.memory.traitImpls ++ fullTbl.traitImpls) dp = false)
    (hkeys : ∀ k ∈ demandedKeys narrowTbl.lookup body fuel s, k.defPath ∈ cone) :
    evalWithOpaqueCallees narrowTbl body fuel s = evalWithOpaqueCallees fullTbl body fuel s :=
  evalWithOpaqueCallees_cone_narrow_of_narrow narrowTbl fullTbl body fuel s fun k hk => by
    have hextra := demandedKeys_extraTraitImpls narrowTbl.lookup body fuel s k hk
    have hdp := hkeys k hk
    refine lookupKey_eq_of_agreesOn_free h hdp ?_ ?_
    · rw [hextra]
      exact hno₁ _ hdp
    · rw [hextra]
      exact hno₂ _ hdp

theorem hasTraitImplForDefPath_filter (defPath : DefPath) :
    ∀ (impls : List TraitImplEntry),
      hasTraitImplForDefPath impls defPath =
        !(impls.filter (fun e => stringEq e.traitRef.defPath defPath)).isEmpty
  | [] => rfl
  | entry :: rest => by
    unfold hasTraitImplForDefPath
    cases h : stringEq entry.traitRef.defPath defPath with
    | true => simp [h]
    | false =>
      simp only [List.filter_cons, h, Bool.false_eq_true, ite_false]
      exact hasTraitImplForDefPath_filter defPath rest

theorem collectMatchingTraitImplsWith_filter_defPath
    (lookupRaw : DefPath → Option CapturedMir) (defPath : DefPath) (typeArgs : List RigidTy) :
    ∀ (impls : List TraitImplEntry) (acc : List (TraitImplEntry × Option (List RigidTy))),
      collectMatchingTraitImplsWith lookupRaw impls defPath typeArgs acc =
        collectMatchingTraitImplsWith lookupRaw
          (impls.filter (fun e => stringEq e.traitRef.defPath defPath)) defPath typeArgs acc
  | [], _ => rfl
  | entry :: rest, acc => by
    cases h : stringEq entry.traitRef.defPath defPath with
    | false =>
      simp only [List.filter_cons, h, Bool.false_eq_true, ite_false]
      rw [collectMatchingTraitImplsWith_cons_ne_path h]
      exact collectMatchingTraitImplsWith_filter_defPath lookupRaw defPath typeArgs rest acc
    | true =>
      simp only [List.filter_cons, h, ite_true]
      unfold collectMatchingTraitImplsWith
      simp only [h, ite_true]
      cases entry.traitRef.args with
      | nil =>
        exact collectMatchingTraitImplsWith_filter_defPath lookupRaw defPath typeArgs rest acc
      | cons a as =>
        dsimp only
        cases matchRigidTyPrefix (a :: as) typeArgs [] with
        | none =>
          exact collectMatchingTraitImplsWith_filter_defPath lookupRaw defPath typeArgs rest acc
        | some p =>
          exact collectMatchingTraitImplsWith_filter_defPath lookupRaw defPath typeArgs rest _

theorem collectMatchingTraitImplsWith_congr
    {r₁ r₂ : DefPath → Option CapturedMir} (defPath : DefPath) (typeArgs : List RigidTy) :
    ∀ (impls : List TraitImplEntry) (acc : List (TraitImplEntry × Option (List RigidTy))),
      (∀ e ∈ impls, stringEq e.traitRef.defPath defPath = true → r₁ e.implPath = r₂ e.implPath) →
      collectMatchingTraitImplsWith r₁ impls defPath typeArgs acc =
        collectMatchingTraitImplsWith r₂ impls defPath typeArgs acc
  | [], _, _ => rfl
  | entry :: rest, acc, h => by
    unfold collectMatchingTraitImplsWith
    by_cases hd : stringEq entry.traitRef.defPath defPath = true
    · simp only [hd, ite_true]
      have heq := h entry (List.Mem.head _) hd
      have hrest : ∀ e ∈ rest, stringEq e.traitRef.defPath defPath = true →
          r₁ e.implPath = r₂ e.implPath :=
        fun e hm => h e (List.Mem.tail _ hm)
      cases entry.traitRef.args with
      | nil => exact collectMatchingTraitImplsWith_congr defPath typeArgs rest acc hrest
      | cons a as =>
        dsimp only
        cases matchRigidTyPrefix (a :: as) typeArgs [] with
        | none => exact collectMatchingTraitImplsWith_congr defPath typeArgs rest acc hrest
        | some p =>
          dsimp only
          rw [heq]
          exact collectMatchingTraitImplsWith_congr defPath typeArgs rest _ hrest
    · simp only [hd, Bool.false_eq_true, ite_false]
      exact collectMatchingTraitImplsWith_congr defPath typeArgs rest acc
        (fun e hm => h e (List.Mem.tail _ hm))

theorem upsertMatchingTraitImpl_forall {P : TraitImplEntry → Prop} {entry : TraitImplEntry}
    (he : P entry) (opt : Option (List RigidTy)) :
    ∀ (acc : List (TraitImplEntry × Option (List RigidTy))),
      (∀ p ∈ acc, P p.1) → ∀ p ∈ upsertMatchingTraitImpl entry opt acc, P p.1
  | [], _, p, hp => by
    simp only [upsertMatchingTraitImpl, List.mem_singleton] at hp
    subst hp
    exact he
  | (existing, exOpt) :: rest, hacc, p, hp => by
    unfold upsertMatchingTraitImpl at hp
    cases hs : stringEq existing.implPath entry.implPath with
    | true =>
      rw [hs] at hp
      cases exOpt <;> cases opt
      all_goals
        dsimp only at hp
        rcases List.mem_cons.mp hp with rfl | hrest
        · first | exact he | exact hacc _ (List.Mem.head _)
        · exact hacc p (List.Mem.tail _ hrest)
    | false =>
      rw [hs] at hp
      dsimp only at hp
      rcases List.mem_cons.mp hp with rfl | hrest
      · exact hacc _ (List.Mem.head _)
      · exact upsertMatchingTraitImpl_forall he opt rest
          (fun q hq => hacc q (List.Mem.tail _ hq)) p hrest

theorem collectMatchingTraitImplsWith_forall {P : TraitImplEntry → Prop}
    (r : DefPath → Option CapturedMir) (defPath : DefPath) (typeArgs : List RigidTy) :
    ∀ (impls : List TraitImplEntry) (acc : List (TraitImplEntry × Option (List RigidTy))),
      (∀ e ∈ impls, stringEq e.traitRef.defPath defPath = true → P e) →
      (∀ p ∈ acc, P p.1) →
      ∀ p ∈ collectMatchingTraitImplsWith r impls defPath typeArgs acc, P p.1
  | [], _, _, hacc, p, hp => hacc p hp
  | entry :: rest, acc, himpls, hacc, p, hp => by
    unfold collectMatchingTraitImplsWith at hp
    by_cases hd : stringEq entry.traitRef.defPath defPath = true
    · simp only [hd, ite_true] at hp
      have hrest : ∀ e ∈ rest, stringEq e.traitRef.defPath defPath = true → P e :=
        fun e hm => himpls e (List.Mem.tail _ hm)
      cases hargs : entry.traitRef.args with
      | nil =>
        rw [hargs] at hp
        exact collectMatchingTraitImplsWith_forall r defPath typeArgs rest acc hrest hacc p hp
      | cons a as =>
        rw [hargs] at hp
        dsimp only at hp
        cases hm : matchRigidTyPrefix (a :: as) typeArgs [] with
        | none =>
          rw [hm] at hp
          exact collectMatchingTraitImplsWith_forall r defPath typeArgs rest acc hrest hacc p hp
        | some pr =>
          rw [hm] at hp
          exact collectMatchingTraitImplsWith_forall r defPath typeArgs rest _ hrest
            (upsertMatchingTraitImpl_forall (himpls entry (List.Mem.head _) hd) _ acc hacc) p hp
    · simp only [hd, Bool.false_eq_true, ite_false] at hp
      exact collectMatchingTraitImplsWith_forall r defPath typeArgs rest acc
        (fun e hm => himpls e (List.Mem.tail _ hm)) hacc p hp

theorem filterMostSpecificTraitImpls_mem
    (allMatches : List (TraitImplEntry × Option (List RigidTy))) :
    ∀ (ms : List (TraitImplEntry × Option (List RigidTy)))
      {p : TraitImplEntry × Option (List RigidTy)},
      p ∈ filterMostSpecificTraitImpls allMatches ms → p ∈ ms
  | [], _, hp => nomatch hp
  | (entry, opt) :: rest, p, hp => by
    unfold filterMostSpecificTraitImpls at hp
    cases hs : isTraitImplInstanceOfAll entry.traitRef.args allMatches with
    | true =>
      rw [hs] at hp
      rcases List.mem_cons.mp hp with rfl | hr
      · exact List.Mem.head _
      · exact List.Mem.tail _ (filterMostSpecificTraitImpls_mem allMatches rest hr)
    | false =>
      rw [hs] at hp
      exact List.Mem.tail _ (filterMostSpecificTraitImpls_mem allMatches rest hp)

/-- **Full key congruence under `AgreesOn` (monomorphic, generic, and trait-dispatched callees)**:
whenever `t₁` and `t₂` agree on `cone` (`k.defPath ∈ cone`), carry matching `TraitImplEntry`
lists for `k.defPath`, and every matching `TraitImplEntry` has `implPath ∈ cone`,
`t₁.lookupKey k = t₂.lookupKey k`. -/
theorem lookupKey_eq_of_agreesOn_with_traits {cone : List DefPath} {t₁ t₂ : OpaqueCalleeTable}
    {k : CalleeKey} (h : OpaqueCalleeTable.AgreesOn cone t₁ t₂) (hk : k.defPath ∈ cone)
    (htraits : t₁.traitImpls.filter (fun e => stringEq e.traitRef.defPath k.defPath) =
      t₂.traitImpls.filter (fun e => stringEq e.traitRef.defPath k.defPath))
    (himpls : ∀ e ∈ k.extraTraitImpls ++ t₁.traitImpls,
      stringEq e.traitRef.defPath k.defPath = true → e.implPath ∈ cone) :
    t₁.lookupKey k = t₂.lookupKey k := by
  obtain ⟨L, dp, tys, ti⟩ := k
  simp only at hk htraits himpls
  have hall_flt :
      (ti ++ t₁.traitImpls).filter (fun e => stringEq e.traitRef.defPath dp) =
        (ti ++ t₂.traitImpls).filter (fun e => stringEq e.traitRef.defPath dp) := by
    simp only [List.filter_append, htraits]
  have hhas :
      hasTraitImplForDefPath (ti ++ flatMapTraitImpls t₁.toList) dp =
        hasTraitImplForDefPath (ti ++ flatMapTraitImpls t₂.toList) dp := by
    rw [← OpaqueCalleeTable.traitImpls_eq, ← OpaqueCalleeTable.traitImpls_eq,
      hasTraitImplForDefPath_filter, hasTraitImplForDefPath_filter, hall_flt]
  have hfind_dp : findCallee? t₁.toList dp = findCallee? t₂.toList dp :=
    (calleesAgreeOn_of_agreesOn h) dp hk
  rw [OpaqueCalleeTable.lookupKey_eq, OpaqueCalleeTable.lookupKey_eq,
    OpaqueCalleeTable.lookup_eq, OpaqueCalleeTable.lookup_eq]
  suffices hres : resolveCalleeBodyAndArgs? t₁.toList dp tys ti =
      resolveCalleeBodyAndArgs? t₂.toList dp tys ti by
    simp only [lookupCallee, hres]
  cases tys with
  | nil => simp only [resolveCalleeBodyAndArgs?, hfind_dp]
  | cons firstArg restArgs =>
    by_cases hp : rigidTyTag firstArg = 0
    · cases firstArg <;> first
        | contradiction
        | simp only [resolveCalleeBodyAndArgs?, hfind_dp, hhas]
    · have hcol :
          collectMatchingTraitImpls t₁.toList (ti ++ flatMapTraitImpls t₁.toList) dp
              (firstArg :: restArgs) =
            collectMatchingTraitImpls t₂.toList (ti ++ flatMapTraitImpls t₂.toList) dp
              (firstArg :: restArgs) := by
        rw [← OpaqueCalleeTable.traitImpls_eq, ← OpaqueCalleeTable.traitImpls_eq,
          collectMatchingTraitImpls_eq_with, collectMatchingTraitImpls_eq_with,
          collectMatchingTraitImplsWith_filter_defPath t₁.lookupRaw,
          collectMatchingTraitImplsWith_filter_defPath t₂.lookupRaw, ← hall_flt]
        apply collectMatchingTraitImplsWith_congr dp (firstArg :: restArgs)
        intro e he hd
        exact h e.implPath (himpls e (List.mem_filter.mp he).1 hd)
      have hmem_cone : ∀ p ∈ collectMatchingTraitImpls t₁.toList
          (ti ++ flatMapTraitImpls t₁.toList) dp (firstArg :: restArgs),
          p.1.implPath ∈ cone := by
        rw [← OpaqueCalleeTable.traitImpls_eq, collectMatchingTraitImpls_eq_with]
        exact collectMatchingTraitImplsWith_forall t₁.lookupRaw dp (firstArg :: restArgs)
          (ti ++ t₁.traitImpls) [] himpls (fun _ hm => nomatch hm)
      have htail :
          (let allTraitImpls := ti ++ flatMapTraitImpls t₁.toList
            let matchedImpls :=
              collectMatchingTraitImpls t₁.toList allTraitImpls dp (firstArg :: restArgs)
            match matchedImpls with
            | [] =>
              match findCallee? t₁.toList dp with
              | none => none
              | some c =>
                match Bool.and (hasTraitImplForDefPath allTraitImpls dp)
                    (Bool.not (allParamsInCallerLayouts 0 firstArg)) with
                | true => none
                | false => some (c, firstArg :: restArgs)
            | _ :: _ =>
              match filterMostSpecificTraitImpls matchedImpls matchedImpls with
              | (winnerEntry, some implTypeArgs) :: [] =>
                match findCallee? t₁.toList winnerEntry.implPath with
                | some c =>
                  let effectiveTypeArgs :=
                    match stringEq winnerEntry.implPath dp with
                    | true => firstArg :: restArgs
                    | false => implTypeArgs
                  if effectiveTypeArgs.length == c.typeParamCount then
                    some (c, effectiveTypeArgs)
                  else none
                | none => none
              | _ => none) =
          (let allTraitImpls := ti ++ flatMapTraitImpls t₂.toList
            let matchedImpls :=
              collectMatchingTraitImpls t₂.toList allTraitImpls dp (firstArg :: restArgs)
            match matchedImpls with
            | [] =>
              match findCallee? t₂.toList dp with
              | none => none
              | some c =>
                match Bool.and (hasTraitImplForDefPath allTraitImpls dp)
                    (Bool.not (allParamsInCallerLayouts 0 firstArg)) with
                | true => none
                | false => some (c, firstArg :: restArgs)
            | _ :: _ =>
              match filterMostSpecificTraitImpls matchedImpls matchedImpls with
              | (winnerEntry, some implTypeArgs) :: [] =>
                match findCallee? t₂.toList winnerEntry.implPath with
                | some c =>
                  let effectiveTypeArgs :=
                    match stringEq winnerEntry.implPath dp with
                    | true => firstArg :: restArgs
                    | false => implTypeArgs
                  if effectiveTypeArgs.length == c.typeParamCount then
                    some (c, effectiveTypeArgs)
                  else none
                | none => none
              | _ => none) := by
        dsimp only
        rw [← hcol]
        cases hm : collectMatchingTraitImpls t₁.toList (ti ++ flatMapTraitImpls t₁.toList) dp
            (firstArg :: restArgs) with
        | nil => simp only [hfind_dp, hhas]
        | cons m ms =>
          dsimp only
          cases hw : filterMostSpecificTraitImpls (m :: ms) (m :: ms) with
          | nil => rfl
          | cons w ws =>
            rcases w with ⟨winnerEntry, optArgs⟩
            cases optArgs with
            | none => rfl
            | some implTypeArgs =>
              cases ws with
              | cons _ _ => rfl
              | nil =>
                have hw_mem : (winnerEntry, some implTypeArgs) ∈ (m :: ms) :=
                  filterMostSpecificTraitImpls_mem (m :: ms) (m :: ms)
                    (by rw [hw]; exact List.Mem.head _)
                have hw_cone : winnerEntry.implPath ∈ cone :=
                  hmem_cone _ (by rw [hm]; exact hw_mem)
                have hfind_w : findCallee? t₁.toList winnerEntry.implPath =
                    findCallee? t₂.toList winnerEntry.implPath :=
                  (calleesAgreeOn_of_agreesOn h) _ hw_cone
                simp only [hfind_w]
      cases firstArg <;> first | exact absurd rfl hp | exact htail

/-- **Narrow-run cone narrowing of the opaque evaluator from `AgreesOn`, including both generic
and trait-dispatched callees**: steps only `narrowTbl` in `demandedKeys` and checks trait-impl
filter equality + `implPath ∈ cone` over the sealed `traitImpls`. -/
theorem evalWithOpaqueCallees_cone_narrow_of_narrow_agreesOn_with_traits (cone : List DefPath)
    (narrowTbl fullTbl : OpaqueCalleeTable) (body : CapturedMir) (fuel : Nat) (s : MachineState)
    (h : OpaqueCalleeTable.AgreesOn cone narrowTbl fullTbl)
    (htraits : ∀ dp, dp ∈ cone →
      narrowTbl.traitImpls.filter (fun e => stringEq e.traitRef.defPath dp) =
        fullTbl.traitImpls.filter (fun e => stringEq e.traitRef.defPath dp))
    (himpls : ∀ dp, dp ∈ cone → ∀ e ∈ s.memory.traitImpls ++ narrowTbl.traitImpls,
      stringEq e.traitRef.defPath dp = true → e.implPath ∈ cone)
    (hkeys : ∀ k ∈ demandedKeys narrowTbl.lookup body fuel s, k.defPath ∈ cone) :
    evalWithOpaqueCallees narrowTbl body fuel s = evalWithOpaqueCallees fullTbl body fuel s :=
  evalWithOpaqueCallees_cone_narrow_of_narrow narrowTbl fullTbl body fuel s fun k hk => by
    have hextra := demandedKeys_extraTraitImpls narrowTbl.lookup body fuel s k hk
    have hdp := hkeys k hk
    refine lookupKey_eq_of_agreesOn_with_traits h hdp (htraits _ hdp) ?_
    rw [hextra]
    exact himpls _ hdp

/-- A halting iterated trusted run is a halting `MirFuelFree.runMirExecBounded` run (one more
unit of fuel absorbs the final `.tau (.halted _)` step). -/
theorem runMirExecBounded_of_runSteps_halted (body : CapturedMir) :
    ∀ (fuel : Nat) (s : MachineState) (tr : List MirObs) (out : MirOutcome) (tr' : List MirObs),
      runSteps (stepMirFn body) fuel s tr = .halted out tr' →
        MirFuelFree.runMirExecBounded (fuel + 1) body (.running s) = some out
  | 0, _, _, _, _, h => nomatch h
  | n + 1, s, tr, out, tr', h => by
    unfold runSteps at h
    unfold MirFuelFree.runMirExecBounded
    show (match stepMirFn body s with
      | .ret out => some out
      | .tau st' => MirFuelFree.runMirExecBounded (n + 1) body st'
      | .vis (.inr (.inl _)) k => MirFuelFree.runMirExecBounded (n + 1) body (k PUnit.unit)
      | .vis (.inl _) _ => none
      | .vis (.inr (.inr _)) _ => none) = some out
    revert h
    rcases stepMirFn body s with out' | st | ⟨e, k⟩
    · intro h
      change RunResult.halted out' tr = .halted out tr' at h
      injection h with h
      rw [h]
    · rcases st with s' | out' | fk
      · intro h
        exact runMirExecBounded_of_runSteps_halted body n s' _ out tr' h
      · intro h
        change RunResult.halted out' (tr ++ none.toList) = .halted out tr' at h
        injection h with h
        rw [h]
        rfl
      · intro h
        nomatch h
    · rcases e with fk | x | c
      · cases fk with
        | fail kind => intro h; nomatch h
      · cases x with
        | emit ev =>
          intro h
          show MirFuelFree.runMirExecBounded (n + 1) body (k PUnit.unit) = some out
          have hview : viewStepNode (.vis (.inr (.inl (.emit ev))) k) =
              StepView.cont (some ev) (k PUnit.unit) := rfl
          rw [hview] at h
          revert h
          cases k PUnit.unit with
          | running s' =>
            intro h
            exact runMirExecBounded_of_runSteps_halted body n s' _ out tr' h
          | halted out' =>
            intro h
            injection h with h
            rw [h]
            rfl
          | faulted fk =>
            intro h
            nomatch h
      · cases c with
        | call req => intro h; nomatch h

/-- **Opaque evaluation → `MirLiftCore.runCfgWithCallees`** under `MirLiftCore.CalleeInitWf`
(also covering the empty table over a clean entry memory). -/
theorem runCfgWithCallees_of_evalWithOpaqueCallees_halted_of_wf (tbl : OpaqueCalleeTable)
    (body : CapturedMir) (args : List Value) (mem : Memory) (fuel : Nat) (out : MirOutcome)
    (tr : List MirObs) (hwf : MirLiftCore.CalleeInitWf body mem tbl.toList)
    (h : evalWithOpaqueCallees tbl body fuel
      (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem
        tbl.toList) = .halted out tr) :
    MirLiftCore.runCfgWithCallees (fuel + 1) body args mem tbl.toList = some out := by
  rw [evalWithOpaqueCallees_eq_trusted_initWithMemoryAndCallees_of_wf tbl body args mem fuel hwf]
    at h
  exact runMirExecBounded_of_runSteps_halted body fuel _ [] out tr h

/-- **Opaque evaluation → `MirLiftCore.runCfgWithCallees`**: a halting branch-pruned opaque
run from the multi-callee entry state of a non-empty table is a halting
`runCfgWithCallees` run with the sealed list, which `MirLiftCore` narrows further
(`runCfgWithCallees_cone_narrow_of_agreesOn`). -/
theorem runCfgWithCallees_of_evalWithOpaqueCallees_halted (tbl : OpaqueCalleeTable)
    (body : CapturedMir) (args : List Value) (mem : Memory) (fuel : Nat) (out : MirOutcome)
    (tr : List MirObs) (hne : tbl.toList ≠ [])
    (h : evalWithOpaqueCallees tbl body fuel
      (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem
        tbl.toList) = .halted out tr) :
    MirLiftCore.runCfgWithCallees (fuel + 1) body args mem tbl.toList = some out :=
  runCfgWithCallees_of_evalWithOpaqueCallees_halted_of_wf tbl body args mem fuel out tr
    (Or.inl hne) h

/-- **`runCfgWithCallees` narrowing between opaque tables** (`MirLiftCore.runCfgWithCallees_cone_narrow`
with agreement over `lookupRaw`). -/
theorem runCfgWithCallees_cone_narrow_of_agreesOn (cone : List DefPath) (fuel : Nat)
    (body : CapturedMir) (args : List Value) (mem : Memory) {t₁ t₂ : OpaqueCalleeTable}
    (h₁ : t₁.toList ≠ []) (h₂ : t₂.toList ≠ []) (h_agree : OpaqueCalleeTable.AgreesOn cone t₁ t₂)
    (h_reach : MirLiftCore.ConeReach body (MirLiftCore.StepConeSafe cone body) fuel
      (.running (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem
        t₁.toList))) :
    MirLiftCore.runCfgWithCallees fuel body args mem t₂.toList =
      (MirLiftCore.runCfgWithCallees fuel body args mem t₁.toList).map
        (MirLiftCore.MirOutcome.mapMem (MirLiftCore.Memory.withCallees t₂.toList)) :=
  MirLiftCore.runCfgWithCallees_cone_narrow cone fuel body args mem h₁ h₂
    (calleesAgreeOn_of_agreesOn h_agree) h_reach

/-- **Syntactic `runCfgWithCallees` narrowing between opaque tables** under the decidable
`MirLiftCore.CallConeClosed` check (no `ConeReach` obligation). -/
theorem runCfgWithCallees_cone_narrow_of_agreesOn_closed (cone : List DefPath) (fuel : Nat)
    (body : CapturedMir) (args : List Value) (mem : Memory) {t₁ t₂ : OpaqueCalleeTable}
    (h₁ : t₁.toList ≠ []) (h₂ : t₂.toList ≠ []) (h_agree : OpaqueCalleeTable.AgreesOn cone t₁ t₂)
    (h_closed : MirLiftCore.CallConeClosed cone body t₁.toList = true)
    (h_ac : mem.activeCallee = none) (h_cs : mem.callStack = []) :
    MirLiftCore.runCfgWithCallees fuel body args mem t₂.toList =
      (MirLiftCore.runCfgWithCallees fuel body args mem t₁.toList).map
        (MirLiftCore.MirOutcome.mapMem (MirLiftCore.Memory.withCallees t₂.toList)) :=
  MirLiftCore.runCfgWithCallees_cone_narrow_of_closed cone fuel body args mem h₁ h₂
    (calleesAgreeOn_of_agreesOn h_agree) h_closed h_ac h_cs

/-- **`wpMirExecSym` narrowing between opaque tables**: every callee-insensitive
postcondition transfers between the multi-callee entry states of agreeing tables. -/
theorem wpMirExecSym_cone_narrow_of_agreesOn (cone : List DefPath) (fuel : Nat)
    (body : CapturedMir) (args : List Value) (mem : Memory) {t₁ t₂ : OpaqueCalleeTable}
    (h₁ : t₁.toList ≠ []) (h₂ : t₂.toList ≠ []) (h_agree : OpaqueCalleeTable.AgreesOn cone t₁ t₂)
    (post : MirOutcome → Prop)
    (h_post : ∀ out,
      post (MirLiftCore.MirOutcome.mapMem (MirLiftCore.Memory.withCallees t₂.toList) out) ↔ post out)
    (h_reach : MirLiftCore.ConeReach body (MirLiftCore.StepConeSafe cone body) fuel
      (.running (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem
        t₁.toList))) :
    Anneal.Rustc.V2026_06_01.SymbolicEval.wpMirExecSym fuel body
        (.running (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem
          t₂.toList)) post ↔
      Anneal.Rustc.V2026_06_01.SymbolicEval.wpMirExecSym fuel body
        (.running (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem
          t₁.toList)) post :=
  MirLiftCore.wpMirExecSym_cone_narrow_init cone fuel body args mem h₁ h₂
    (calleesAgreeOn_of_agreesOn h_agree) post h_post h_reach

/-- **`MirWpConverges` narrowing between opaque tables.** -/
theorem mirWpConverges_cone_narrow_of_agreesOn (cone : List DefPath) (body : CapturedMir)
    (args : List Value) (mem : Memory) {t₁ t₂ : OpaqueCalleeTable}
    (h₁ : t₁.toList ≠ []) (h₂ : t₂.toList ≠ []) (h_agree : OpaqueCalleeTable.AgreesOn cone t₁ t₂)
    (post : MirOutcome → Prop)
    (h_post : ∀ out,
      post (MirLiftCore.MirOutcome.mapMem (MirLiftCore.Memory.withCallees t₂.toList) out) ↔ post out)
    (h_reach : ∀ fuel, MirLiftCore.ConeReach body (MirLiftCore.StepConeSafe cone body) fuel
      (.running (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem
        t₁.toList))) :
    MirFuelFree.MirWpConverges body
        (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem
          t₂.toList) post ↔
      MirFuelFree.MirWpConverges body
        (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem
          t₁.toList) post :=
  MirLiftCore.mirWpConverges_cone_narrow_init cone body args mem h₁ h₂
    (calleesAgreeOn_of_agreesOn h_agree) post h_post h_reach

/-- A single raw-lookup hit discharges `MirLiftCore.CalleeInitWf` for a sealed table. -/
theorem calleeInitWf_of_lookupRaw {tbl : OpaqueCalleeTable} {dp : DefPath} {c : CapturedMir}
    (body : CapturedMir) (mem : Memory) (h : tbl.lookupRaw dp = some c) :
    MirLiftCore.CalleeInitWf body mem tbl.toList :=
  Or.inl (toList_ne_nil_of_lookupRaw h)

/-- **Syntactic `runCfgWithCallees` narrowing between opaque tables, down to the empty table**
(`MirLiftCore.runCfgWithCallees_cone_narrow_of_closed_wf` with agreement over `lookupRaw`). -/
theorem runCfgWithCallees_cone_narrow_of_agreesOn_closed_wf (cone : List DefPath) (fuel : Nat)
    (body : CapturedMir) (args : List Value) (mem : Memory) {t₁ t₂ : OpaqueCalleeTable}
    (h₁ : MirLiftCore.CalleeInitWf body mem t₁.toList)
    (h₂ : MirLiftCore.CalleeInitWf body mem t₂.toList)
    (h_agree : OpaqueCalleeTable.AgreesOn cone t₁ t₂)
    (h_closed : MirLiftCore.CallConeClosed cone body t₁.toList = true)
    (h_ac : mem.activeCallee = none) (h_cs : mem.callStack = []) :
    MirLiftCore.runCfgWithCallees fuel body args mem t₂.toList =
      (MirLiftCore.runCfgWithCallees fuel body args mem t₁.toList).map
        (MirLiftCore.MirOutcome.mapMem (MirLiftCore.Memory.withCallees t₂.toList)) :=
  MirLiftCore.runCfgWithCallees_cone_narrow_of_closed_wf cone fuel body args mem h₁ h₂
    (calleesAgreeOn_of_agreesOn h_agree) h_closed h_ac h_cs

/-- **Syntactic `wpMirExecSym` narrowing between opaque tables, down to the empty table.** -/
theorem wpMirExecSym_cone_narrow_of_agreesOn_closed_wf (cone : List DefPath) (fuel : Nat)
    (body : CapturedMir) (args : List Value) (mem : Memory) {t₁ t₂ : OpaqueCalleeTable}
    (h₁ : MirLiftCore.CalleeInitWf body mem t₁.toList)
    (h₂ : MirLiftCore.CalleeInitWf body mem t₂.toList)
    (h_agree : OpaqueCalleeTable.AgreesOn cone t₁ t₂)
    (h_closed : MirLiftCore.CallConeClosed cone body t₁.toList = true)
    (h_ac : mem.activeCallee = none) (h_cs : mem.callStack = [])
    (post : MirOutcome → Prop)
    (h_post : ∀ out,
      post (MirLiftCore.MirOutcome.mapMem (MirLiftCore.Memory.withCallees t₂.toList) out) ↔ post out) :
    Anneal.Rustc.V2026_06_01.SymbolicEval.wpMirExecSym fuel body
        (.running (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem
          t₂.toList)) post ↔
      Anneal.Rustc.V2026_06_01.SymbolicEval.wpMirExecSym fuel body
        (.running (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem
          t₁.toList)) post :=
  MirLiftCore.wpMirExecSym_cone_narrow_of_closed_wf cone fuel body args mem h₁ h₂
    (calleesAgreeOn_of_agreesOn h_agree) h_closed h_ac h_cs post h_post

/-- **Syntactic `MirWpConverges` narrowing between opaque tables, down to the empty table.** -/
theorem mirWpConverges_cone_narrow_of_agreesOn_closed_wf (cone : List DefPath)
    (body : CapturedMir) (args : List Value) (mem : Memory) {t₁ t₂ : OpaqueCalleeTable}
    (h₁ : MirLiftCore.CalleeInitWf body mem t₁.toList)
    (h₂ : MirLiftCore.CalleeInitWf body mem t₂.toList)
    (h_agree : OpaqueCalleeTable.AgreesOn cone t₁ t₂)
    (h_closed : MirLiftCore.CallConeClosed cone body t₁.toList = true)
    (h_ac : mem.activeCallee = none) (h_cs : mem.callStack = [])
    (post : MirOutcome → Prop)
    (h_post : ∀ out,
      post (MirLiftCore.MirOutcome.mapMem (MirLiftCore.Memory.withCallees t₂.toList) out) ↔ post out) :
    MirFuelFree.MirWpConverges body
        (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem
          t₂.toList) post ↔
      MirFuelFree.MirWpConverges body
        (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem
          t₁.toList) post :=
  MirLiftCore.mirWpConverges_cone_narrow_of_closed_wf cone body args mem h₁ h₂
    (calleesAgreeOn_of_agreesOn h_agree) h_closed h_ac h_cs post h_post

/-- The `MirLiftCore` trait-impl side condition stated over the sealed `traitImpls`. -/
theorem noTraitImplInCone_toList {cone : List DefPath} {ti : List TraitImplEntry}
    {tbl : OpaqueCalleeTable}
    (h : ∀ dp, dp ∈ cone → hasTraitImplForDefPath (ti ++ tbl.traitImpls) dp = false) :
    ∀ dp, dp ∈ cone → hasTraitImplForDefPath (ti ++ flatMapTraitImpls tbl.toList) dp = false := by
  rw [← OpaqueCalleeTable.traitImpls_eq]
  exact h

/-- **Polymorphic syntactic `runCfgWithCallees` narrowing between opaque tables**
(`MirLiftCore.runCfgWithCallees_cone_narrow_of_closed_poly_wf`): generic callees and
polymorphic inline intrinsics in the cone, with the narrowed table's trait-impl side condition
stated over the sealed `traitImpls`. -/
theorem runCfgWithCallees_cone_narrow_of_agreesOn_closed_poly_wf (cone : List DefPath)
    (fuel : Nat) (body : CapturedMir) (args : List Value) (mem : Memory)
    {t₁ t₂ : OpaqueCalleeTable}
    (h₁ : MirLiftCore.CalleeInitWf body mem t₁.toList)
    (h₂ : MirLiftCore.CalleeInitWf body mem t₂.toList)
    (h_agree : OpaqueCalleeTable.AgreesOn cone t₁ t₂)
    (h_closed : MirLiftCore.CallConeClosedPoly cone body t₁.toList body.traitImpls = true)
    (h_no₂ : ∀ dp, dp ∈ cone →
      hasTraitImplForDefPath (body.traitImpls ++ t₂.traitImpls) dp = false)
    (h_ac : mem.activeCallee = none) (h_cs : mem.callStack = []) :
    MirLiftCore.runCfgWithCallees fuel body args mem t₂.toList =
      (MirLiftCore.runCfgWithCallees fuel body args mem t₁.toList).map
        (MirLiftCore.MirOutcome.mapMem (MirLiftCore.Memory.withCallees t₂.toList)) :=
  MirLiftCore.runCfgWithCallees_cone_narrow_of_closed_poly_wf cone fuel body args mem h₁ h₂
    (calleesAgreeOn_of_agreesOn h_agree) h_closed (noTraitImplInCone_toList h_no₂) h_ac h_cs

/-- **Polymorphic syntactic `wpMirExecSym` narrowing between opaque tables.** -/
theorem wpMirExecSym_cone_narrow_of_agreesOn_closed_poly_wf (cone : List DefPath) (fuel : Nat)
    (body : CapturedMir) (args : List Value) (mem : Memory) {t₁ t₂ : OpaqueCalleeTable}
    (h₁ : MirLiftCore.CalleeInitWf body mem t₁.toList)
    (h₂ : MirLiftCore.CalleeInitWf body mem t₂.toList)
    (h_agree : OpaqueCalleeTable.AgreesOn cone t₁ t₂)
    (h_closed : MirLiftCore.CallConeClosedPoly cone body t₁.toList body.traitImpls = true)
    (h_no₂ : ∀ dp, dp ∈ cone →
      hasTraitImplForDefPath (body.traitImpls ++ t₂.traitImpls) dp = false)
    (h_ac : mem.activeCallee = none) (h_cs : mem.callStack = [])
    (post : MirOutcome → Prop)
    (h_post : ∀ out,
      post (MirLiftCore.MirOutcome.mapMem (MirLiftCore.Memory.withCallees t₂.toList) out) ↔ post out) :
    Anneal.Rustc.V2026_06_01.SymbolicEval.wpMirExecSym fuel body
        (.running (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem
          t₂.toList)) post ↔
      Anneal.Rustc.V2026_06_01.SymbolicEval.wpMirExecSym fuel body
        (.running (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem
          t₁.toList)) post :=
  MirLiftCore.wpMirExecSym_cone_narrow_of_closed_poly_wf cone fuel body args mem h₁ h₂
    (calleesAgreeOn_of_agreesOn h_agree) h_closed (noTraitImplInCone_toList h_no₂) h_ac h_cs
    post h_post

/-- **Polymorphic syntactic `MirWpConverges` narrowing between opaque tables.** -/
theorem mirWpConverges_cone_narrow_of_agreesOn_closed_poly_wf (cone : List DefPath)
    (body : CapturedMir) (args : List Value) (mem : Memory) {t₁ t₂ : OpaqueCalleeTable}
    (h₁ : MirLiftCore.CalleeInitWf body mem t₁.toList)
    (h₂ : MirLiftCore.CalleeInitWf body mem t₂.toList)
    (h_agree : OpaqueCalleeTable.AgreesOn cone t₁ t₂)
    (h_closed : MirLiftCore.CallConeClosedPoly cone body t₁.toList body.traitImpls = true)
    (h_no₂ : ∀ dp, dp ∈ cone →
      hasTraitImplForDefPath (body.traitImpls ++ t₂.traitImpls) dp = false)
    (h_ac : mem.activeCallee = none) (h_cs : mem.callStack = [])
    (post : MirOutcome → Prop)
    (h_post : ∀ out,
      post (MirLiftCore.MirOutcome.mapMem (MirLiftCore.Memory.withCallees t₂.toList) out) ↔ post out) :
    MirFuelFree.MirWpConverges body
        (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem
          t₂.toList) post ↔
      MirFuelFree.MirWpConverges body
        (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem
          t₁.toList) post :=
  MirLiftCore.mirWpConverges_cone_narrow_of_closed_poly_wf cone body args mem h₁ h₂
    (calleesAgreeOn_of_agreesOn h_agree) h_closed (noTraitImplInCone_toList h_no₂) h_ac h_cs
    post h_post

/-! #### `tbl.toList`-free syntactic call-cone closure (`callConeClosed` & `callConeClosedPoly`)

`MirLiftCore.CallConeClosed` and `MirLiftCore.CallConeClosedPoly` scan `coneBodies cone tbl.toList`
and `flatMapTraitImpls tbl.toList`, which (a) forces `tbl.toList` to be unfolded across all `M`
callees at the use site and (b) inspects *shadowed* duplicate `DefPath` entries in `tbl.toList`
that `findCallee?` / `lookupRaw` can never return.

`OpaqueCalleeTable.callConeClosed` and `OpaqueCalleeTable.callConeClosedPoly` instead query only
`tbl.lookupRaw dp` for `dp ∈ cone` and the sealed `tbl.traitImpls`, so a client discharges cone
closure in `O(|cone|)` rewrites using the same `lookupRaw` and `traitImpls` certificates it uses
for stepping — never unfolding `tbl.toList`, invariant under `OpaqueCalleeTable.AgreesOn cone`,
and strictly more general when `tbl` contains shadowed duplicate entries. -/

/-- **`tbl.toList`-free syntactic call-cone closure**: checks `root` and the first-match body
`tbl.lookupRaw dp` for each `dp ∈ cone`. -/
def OpaqueCalleeTable.callConeClosed (cone : List DefPath) (root : CapturedMir)
    (tbl : OpaqueCalleeTable) : Bool :=
  MirLiftCore.bodyCallsInCone cone root &&
    cone.all (fun dp =>
      match tbl.lookupRaw dp with
      | some b => MirLiftCore.bodyCallsInCone cone b
      | none => true)

/-- **`tbl.toList`-free polymorphic syntactic call-cone closure**: checks `root`, the first-match
body `tbl.lookupRaw dp` for each `dp ∈ cone`, and absence of trait-impl dispatch over the sealed
`tbl.traitImpls`. -/
def OpaqueCalleeTable.callConeClosedPoly (cone : List DefPath) (root : CapturedMir)
    (tbl : OpaqueCalleeTable) (ti : List TraitImplEntry := []) : Bool :=
  MirLiftCore.bodyCallsInConePoly cone root &&
    cone.all (fun dp =>
      (match tbl.lookupRaw dp with
       | some b => MirLiftCore.bodyCallsInConePoly cone b
       | none => true) &&
      !hasTraitImplForDefPath (ti ++ tbl.traitImpls) dp)

theorem listAll_congr {α : Type} {f g : α → Bool} :
    ∀ {xs : List α}, (∀ x ∈ xs, f x = g x) → xs.all f = xs.all g
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.all_cons, h x (List.Mem.head _),
      listAll_congr (fun y hy => h y (List.Mem.tail _ hy))]

/-- `callConeClosed` is invariant under `OpaqueCalleeTable.AgreesOn cone` (unlike
`MirLiftCore.CallConeClosed`, which also scans shadowed duplicate entries in `coneBodies`). -/
theorem callConeClosed_congr_of_agreesOn {cone : List DefPath} {t₁ t₂ : OpaqueCalleeTable}
    (root : CapturedMir) (h : OpaqueCalleeTable.AgreesOn cone t₁ t₂) :
    t₁.callConeClosed cone root = t₂.callConeClosed cone root := by
  unfold OpaqueCalleeTable.callConeClosed
  congr 1
  exact listAll_congr fun dp hdp => by rw [h dp hdp]

/-- `callConeClosedPoly` is invariant under `OpaqueCalleeTable.AgreesOn cone` and agreement of
`hasTraitImplForDefPath` on `cone`. -/
theorem callConeClosedPoly_congr_of_agreesOn {cone : List DefPath} {t₁ t₂ : OpaqueCalleeTable}
    (root : CapturedMir) (ti : List TraitImplEntry) (h : OpaqueCalleeTable.AgreesOn cone t₁ t₂)
    (ht : ∀ dp, dp ∈ cone →
      hasTraitImplForDefPath (ti ++ t₁.traitImpls) dp =
        hasTraitImplForDefPath (ti ++ t₂.traitImpls) dp) :
    t₁.callConeClosedPoly cone root ti = t₂.callConeClosedPoly cone root ti := by
  unfold OpaqueCalleeTable.callConeClosedPoly
  congr 1
  exact listAll_congr fun dp hdp => by rw [h dp hdp, ht dp hdp]

/-- `MirLiftCore.CallConeClosed` implies `OpaqueCalleeTable.callConeClosed` (the converse can fail
when `tbl.toList` contains a shadowed duplicate entry with `defPath ∈ cone`). -/
theorem callConeClosed_of_mirLiftCore {cone : List DefPath} {root : CapturedMir}
    {tbl : OpaqueCalleeTable} (h : MirLiftCore.CallConeClosed cone root tbl.toList = true) :
    tbl.callConeClosed cone root = true := by
  unfold MirLiftCore.CallConeClosed at h
  rw [Bool.and_eq_true] at h
  unfold OpaqueCalleeTable.callConeClosed
  rw [Bool.and_eq_true]
  refine ⟨h.1, List.all_eq_true.mpr fun dp hdp => ?_⟩
  cases hraw : tbl.lookupRaw dp with
  | none => rfl
  | some b =>
    rw [OpaqueCalleeTable.lookupRaw_eq] at hraw
    obtain ⟨hm, hd⟩ := MirLiftCore.findCallee?_spec hraw
    apply List.all_eq_true.mp h.2 b
    unfold MirLiftCore.coneBodies
    rw [List.mem_filter]
    exact ⟨hm, MirLiftCore.inCone_iff.mpr (hd ▸ hdp)⟩

/-- `MirLiftCore.CallConeClosedPoly` implies `OpaqueCalleeTable.callConeClosedPoly`. -/
theorem callConeClosedPoly_of_mirLiftCore {cone : List DefPath} {root : CapturedMir}
    {tbl : OpaqueCalleeTable} {ti : List TraitImplEntry}
    (h : MirLiftCore.CallConeClosedPoly cone root tbl.toList ti = true) :
    tbl.callConeClosedPoly cone root ti = true := by
  unfold MirLiftCore.CallConeClosedPoly at h
  simp only [Bool.and_eq_true] at h
  unfold OpaqueCalleeTable.callConeClosedPoly
  rw [Bool.and_eq_true]
  refine ⟨h.1.1, List.all_eq_true.mpr fun dp hdp => ?_⟩
  rw [Bool.and_eq_true, OpaqueCalleeTable.traitImpls_eq]
  refine ⟨?_, List.all_eq_true.mp h.2 dp hdp⟩
  cases hraw : tbl.lookupRaw dp with
  | none => rfl
  | some b =>
    rw [OpaqueCalleeTable.lookupRaw_eq] at hraw
    obtain ⟨hm, hd⟩ := MirLiftCore.findCallee?_spec hraw
    apply List.all_eq_true.mp h.1.2 b
    unfold MirLiftCore.coneBodies
    rw [List.mem_filter]
    exact ⟨hm, MirLiftCore.inCone_iff.mpr (hd ▸ hdp)⟩

/-- `b` is the root body or the first-match body `tbl.lookupRaw dp = some b` for some `dp ∈ cone`. -/
def InConeLookup (cone : List DefPath) (root : CapturedMir) (tbl : OpaqueCalleeTable)
    (b : CapturedMir) : Prop :=
  b = root ∨ ∃ dp, dp ∈ cone ∧ tbl.lookupRaw dp = some b

/-- Reachable-state invariant of a `callConeClosed` execution over `tbl`. -/
def ClosedInvLookup (cone : List DefPath) (root : CapturedMir) (tbl : OpaqueCalleeTable)
    (s : MachineState) : Prop :=
  s.memory.callees = tbl.toList ∧
    InConeLookup cone root tbl (s.memory.activeCallee.getD root) ∧
    ∀ f, f ∈ s.memory.callStack → InConeLookup cone root tbl f.callerBody

theorem bodyCallsInCone_of_inConeLookup {cone : List DefPath} {root : CapturedMir}
    {tbl : OpaqueCalleeTable} {b : CapturedMir}
    (h_closed : tbl.callConeClosed cone root = true)
    (hb : InConeLookup cone root tbl b) : MirLiftCore.bodyCallsInCone cone b = true := by
  unfold OpaqueCalleeTable.callConeClosed at h_closed
  rw [Bool.and_eq_true] at h_closed
  rcases hb with rfl | ⟨dp, hdp, hraw⟩
  · exact h_closed.1
  · have h := List.all_eq_true.mp h_closed.2 dp hdp
    rw [hraw] at h
    exact h

theorem stepConeSafe_of_closedInvLookup {cone : List DefPath} {root : CapturedMir}
    {tbl : OpaqueCalleeTable} {s : MachineState}
    (h_closed : tbl.callConeClosed cone root = true)
    (h_inv : ClosedInvLookup cone root tbl s) : MirLiftCore.StepConeSafe cone root s := by
  intro blk h_bb
  have h_body := bodyCallsInCone_of_inConeLookup h_closed h_inv.2.1
  unfold MirLiftCore.bodyCallsInCone at h_body
  have h_blk := List.all_eq_true.mp h_body blk (List.mem_of_getElem? h_bb)
  rw [Bool.and_eq_true] at h_blk
  exact ⟨fun stmt h_st => List.all_eq_true.mp h_blk.1 stmt (List.mem_of_getElem? h_st),
    MirLiftCore.termConeSafe_of_termCallsInCone h_blk.2⟩

theorem closedInvLookup_of_callerBodies {cone : List DefPath} {root : CapturedMir}
    {tbl : OpaqueCalleeTable} {s s' : MachineState}
    (h_inv : ClosedInvLookup cone root tbl s)
    (hc : s'.memory.callees = s.memory.callees)
    (hac : s'.memory.activeCallee = s.memory.activeCallee)
    (hb : MirLiftCore.CallerBodiesEq s.memory.callStack s'.memory.callStack) :
    ClosedInvLookup cone root tbl s' := by
  refine ⟨hc.trans h_inv.1, hac ▸ h_inv.2.1, ?_⟩
  intro f hf
  obtain ⟨f₀, hf₀, he⟩ := hb.mem hf
  exact he ▸ h_inv.2.2 f₀ hf₀

theorem nodeSuccs_closedInvLookup_of_ctx {cone : List DefPath} {root : CapturedMir}
    {tbl : OpaqueCalleeTable} {s : MachineState} {n : MirStepNode}
    (h_inv : ClosedInvLookup cone root tbl s)
    (hfix : n = MirLiftCore.MirStepNode.mapMem
      (MirLiftCore.Memory.withCalleeCtx s.memory.callees s.memory.activeCallee
        s.memory.traitImpls) n)
    (hb : MirLiftCore.NodeSuccs
      (fun s' => MirLiftCore.CallerBodiesEq s.memory.callStack s'.memory.callStack) n) :
    MirLiftCore.NodeSuccs (ClosedInvLookup cone root tbl) n := by
  refine MirLiftCore.NodeSuccs.mono ?_
    (MirLiftCore.NodeSuccs.and
      (MirLiftCore.nodeSuccs_of_fixed (P := fun s' => s' = MirLiftCore.MachineState.mapMem
        (MirLiftCore.Memory.withCalleeCtx s.memory.callees s.memory.activeCallee
          s.memory.traitImpls) s')
        hfix (fun _ h => h))
      hb)
  rintro s' ⟨hs', hb'⟩
  have hm : s'.memory =
      MirLiftCore.Memory.withCalleeCtx s.memory.callees s.memory.activeCallee
        s.memory.traitImpls s'.memory :=
    congrArg MachineState.memory hs'
  exact closedInvLookup_of_callerBodies h_inv (by rw [hm]) (by rw [hm]) hb'

theorem closedInvLookup_return {cone : List DefPath} {root : CapturedMir}
    {tbl : OpaqueCalleeTable} {s : MachineState} {caller : SavedCallerFrame}
    {rest : List SavedCallerFrame} {retVal : Value} {locals' : List LocalSlot} {mem' : Memory}
    {F : StackFrame}
    (h_inv : ClosedInvLookup cone root tbl s) (h_cs : s.memory.callStack = caller :: rest)
    (h_w : writeReturnDestination caller.frame.locals (MirLiftCore.ccReturnCallerMem s caller rest)
      caller.destination retVal caller.callerBody.localDecls caller.callerBody.layouts =
        .ok locals' mem') :
    ClosedInvLookup cone root tbl { frame := F, memory := mem' } := by
  obtain ⟨hc, hac, _⟩ := MirLiftCore.writeReturnDestination_ctx_preserved h_w
  have hb := MirLiftCore.writeReturnDestination_callerBodies h_w
  refine ⟨hc.trans h_inv.1, ?_, ?_⟩
  · show InConeLookup cone root tbl (mem'.activeCallee.getD root)
    rw [hac]
    exact h_inv.2.2 caller (by rw [h_cs]; exact List.Mem.head _)
  · intro f hf
    obtain ⟨f₀, hf₀, he⟩ := hb.mem hf
    exact he ▸ h_inv.2.2 f₀ (by rw [h_cs]; exact List.Mem.tail _ hf₀)

theorem closedInvLookup_unwindFromCallStack {cone : List DefPath} {root : CapturedMir}
    {tbl : OpaqueCalleeTable} :
    ∀ (stk : List SavedCallerFrame) (m : Memory), m.callees = tbl.toList →
      (∀ f, f ∈ stk → InConeLookup cone root tbl f.callerBody) →
      ∀ s', unwindFromCallStack stk m = .running s' → ClosedInvLookup cone root tbl s'
  | [], m, _, _, _, h => by
    unfold unwindFromCallStack at h
    cases hr : m.rootUnwindCeiling <;> (rw [hr] at h; cases h)
  | caller :: rest, m, hc, hf, s', h => by
    unfold unwindFromCallStack at h
    dsimp only at h
    cases hr : caller.returnUnwind with
    | unreachable => rw [hr] at h; dsimp only at h; cases h
    | terminate => rw [hr] at h; dsimp only at h; cases h
    | continue_ =>
      rw [hr] at h
      dsimp only at h
      exact closedInvLookup_unwindFromCallStack rest
        { m with
          callStack := rest
          activeCallee := some caller.callerBody
          activeProtectors := restoreCallerProtectors caller }
        hc (fun f hm => hf f (List.Mem.tail _ hm)) s' h
    | cleanup bb =>
      rw [hr] at h
      dsimp only at h
      cases h
      exact ⟨hc, hf caller (List.Mem.head _), fun f hm => hf f (List.Mem.tail _ hm)⟩

private theorem nodeSuccs_unwindMatchLookup {cone : List DefPath} {root : CapturedMir}
    {tbl : OpaqueCalleeTable} (st : MirExecState)
    (h : ∀ s', st = .running s' → ClosedInvLookup cone root tbl s') :
    MirLiftCore.NodeSuccs (ClosedInvLookup cone root tbl)
      (match (generalizing := false) st with
        | .running nextState => MirStepNode.step nextState
        | .halted out => MirStepNode.retOutcome out
        | .faulted fk => MirStepNode.fail fk) := by
  cases st with
  | running s' => exact h s' rfl
  | halted _ => trivial
  | faulted _ => trivial

private theorem nodeSuccs_applyUnwindLookup {cone : List DefPath} {root : CapturedMir}
    {tbl : OpaqueCalleeTable} {s : MachineState} (h_inv : ClosedInvLookup cone root tbl s)
    (l : List LocalSlot) (u : UnwindAction) :
    MirLiftCore.NodeSuccs (ClosedInvLookup cone root tbl)
      (match applyUnwindAction s l s.memory u with
        | .running nextState => MirStepNode.step nextState
        | .halted out => MirStepNode.retOutcome out
        | .faulted fk => MirStepNode.fail fk) := by
  refine nodeSuccs_unwindMatchLookup _ ?_
  intro s' hs'
  cases u with
  | unreachable => cases hs'
  | terminate => cases hs'
  | continue_ =>
    exact closedInvLookup_unwindFromCallStack s.memory.callStack s.memory h_inv.1 h_inv.2.2 s' hs'
  | cleanup bb =>
    cases hs'
    exact h_inv

private theorem inConeLookup_of_lookup {cone : List DefPath} {root : CapturedMir}
    {tbl : OpaqueCalleeTable} {L : LayoutTable} {dp : DefPath} {ti : List TraitImplEntry}
    {b : CapturedMir} (h_dp : dp ∈ cone) (h_lk : lookupCallee tbl.toList L dp [] ti = some b) :
    InConeLookup cone root tbl b :=
  Or.inr ⟨dp, h_dp,
    (OpaqueCalleeTable.lookupRaw_eq tbl dp).trans (MirLiftCore.lookupCallee_nil_eq_some h_lk)⟩

private theorem closedInvLookup_push {cone : List DefPath} {root : CapturedMir}
    {tbl : OpaqueCalleeTable} {s : MachineState} {saved : SavedCallerFrame} {b : CapturedMir}
    {F : StackFrame} (h_inv : ClosedInvLookup cone root tbl s)
    (h_saved : InConeLookup cone root tbl saved.callerBody)
    (h_b : InConeLookup cone root tbl b) :
    ClosedInvLookup cone root tbl
      { frame := F,
        memory := { s.memory with
          callStack := saved :: s.memory.callStack
          activeCallee := some b } } := by
  refine ⟨h_inv.1, h_b, ?_⟩
  intro f hf
  cases hf with
  | head => exact h_saved
  | tail _ hf => exact h_inv.2.2 f hf

theorem nodeSuccs_evalDirectRustIntrinsic?_lookup {cone : List DefPath}
    {root : CapturedMir} {tbl : OpaqueCalleeTable} {s : MachineState}
    (h_inv : ClosedInvLookup cone root tbl s) (currentBody : Option CapturedMir)
    (target : ResolvedCallTarget) (bodyLocalDecls : List LocalDecl) (bodyLayouts : LayoutTable)
    (argOps : List Operand) (argVals : List Value) (locals' : List LocalSlot)
    (destination : Place) (targetBb : BasicBlockIdx) (unwind : UnwindAction)
    (h_cl : MirLiftCore.isNonSelectIntrinsicOpt (classifyRustIntrinsic? target.defPath) = true)
    (fallback : MirStepNode) (h_fb : MirLiftCore.NodeSuccs (ClosedInvLookup cone root tbl) fallback) :
    MirLiftCore.NodeSuccs (ClosedInvLookup cone root tbl)
      (match evalDirectRustIntrinsic? s currentBody target bodyLocalDecls bodyLayouts
          argOps argVals locals' destination targetBb unwind with
       | some stepNode => stepNode
       | none => fallback) := by
  unfold evalDirectRustIntrinsic?
  cases h_k : classifyRustIntrinsic? target.defPath with
  | none => exact h_fb
  | some kind =>
    rw [h_k] at h_cl
    have h_step : ∀ (k : RustIntrinsicKind),
        MirLiftCore.NodeSuccs (ClosedInvLookup cone root tbl)
          (match evalCoreMemPtrIntrinsicCall? k s target bodyLocalDecls bodyLayouts
              argOps argVals locals' destination (.some targetBb) with
           | some sn => sn
           | none => evalNonSelectIntrinsicCall k s target bodyLocalDecls bodyLayouts
               argOps argVals locals' destination targetBb) := by
      intro k
      cases h_cm : evalCoreMemPtrIntrinsicCall? k s target bodyLocalDecls bodyLayouts
          argOps argVals locals' destination (.some targetBb) with
      | some sn =>
        exact nodeSuccs_closedInvLookup_of_ctx h_inv
          (MirLiftCore.evalCoreMemPtrIntrinsicCall?_calleeCtx_preserved k s target bodyLocalDecls bodyLayouts
            argOps argVals locals' destination (.some targetBb) h_cm)
          (MirLiftCore.evalCoreMemPtrIntrinsicCall?_callerBodies k s target bodyLocalDecls bodyLayouts
            argOps argVals locals' destination (.some targetBb) h_cm)
      | none =>
        exact nodeSuccs_closedInvLookup_of_ctx h_inv
          (MirLiftCore.evalNonSelectIntrinsicCall_calleeCtx_preserved k s target bodyLocalDecls bodyLayouts
            argOps argVals locals' destination targetBb)
          (MirLiftCore.evalNonSelectIntrinsicCall_callerBodies k s target bodyLocalDecls bodyLayouts
            argOps argVals locals' destination targetBb)
    cases h_sp : (match kind with
      | .constEvalSelect | .copyNonOverlapping | .writeBytes => true
      | _ => false) with
    | true =>
      cases kind with
      | constEvalSelect => cases h_cl
      | copyNonOverlapping =>
        exact nodeSuccs_closedInvLookup_of_ctx h_inv
          (MirLiftCore.evalCopyNonOverlappingCall_calleeCtx_preserved s bodyLocalDecls bodyLayouts
            argOps argVals locals' destination targetBb)
          (MirLiftCore.evalCopyNonOverlappingCall_callerBodies s bodyLocalDecls bodyLayouts
            argOps argVals locals' destination targetBb)
      | writeBytes =>
        exact nodeSuccs_closedInvLookup_of_ctx h_inv
          (MirLiftCore.evalWriteBytesCall_calleeCtx_preserved s target bodyLocalDecls bodyLayouts
            argOps argVals locals' destination targetBb)
          (MirLiftCore.evalWriteBytesCall_callerBodies s target bodyLocalDecls bodyLayouts
            argOps argVals locals' destination targetBb)
      | _ => cases h_sp
    | false =>
      have h_eq :
          evalDirectRustIntrinsic? s currentBody target bodyLocalDecls bodyLayouts
            argOps argVals locals' destination targetBb unwind =
          some (match evalCoreMemPtrIntrinsicCall? kind s target bodyLocalDecls bodyLayouts
              argOps argVals locals' destination (.some targetBb) with
           | some sn => sn
           | none => evalNonSelectIntrinsicCall kind s target bodyLocalDecls bodyLayouts
               argOps argVals locals' destination targetBb) := by
        unfold evalDirectRustIntrinsic?; rw [h_k]
        cases kind <;> first | (cases h_sp; done) | rfl
      unfold evalDirectRustIntrinsic? at h_eq
      rw [h_k] at h_eq
      rw [h_eq]
      exact h_step kind

theorem nodeSuccs_evalTerminatorLookup {cone : List DefPath} {root : CapturedMir}
    {tbl : OpaqueCalleeTable} {s : MachineState} {term : Terminator}
    (h_inv : ClosedInvLookup cone root tbl s)
    (h_term : MirLiftCore.TermConeSafe cone s (s.memory.activeCallee.getD root) term) :
    MirLiftCore.NodeSuccs (ClosedInvLookup cone root tbl)
      (evalTerminator s term (some (s.memory.activeCallee.getD root))) := by
  have h_cur : InConeLookup cone root tbl (s.memory.activeCallee.getD root) := h_inv.2.1
  rcases term with ⟨kind, span⟩
  cases kind with
  | goto target => exact h_inv
  | switchInt discr targets =>
    unfold evalTerminator; dsimp only
    repeat' (first | trivial | exact h_inv | split)
  | unwindResume =>
    unfold evalTerminator; dsimp only
    exact nodeSuccs_unwindMatchLookup _
      (closedInvLookup_unwindFromCallStack s.memory.callStack s.memory h_inv.1 h_inv.2.2)
  | unwindTerminate => trivial
  | return_ =>
    rw [MirLiftCore.ccEvalReturn_eq]
    unfold MirLiftCore.ccEvalReturn
    repeat' (first | trivial | exact closedInvLookup_return h_inv ‹_› ‹_› | split)
  | unreachable => trivial
  | drop place target unwind =>
    unfold evalTerminator; dsimp only
    repeat' (first | trivial | exact h_inv | split)
  | assert cond expected target unwind =>
    unfold evalTerminator; dsimp only
    repeat' (first | trivial | exact h_inv | exact nodeSuccs_applyUnwindLookup h_inv _ _ | split)
  | call func argOps destination target unwind =>
    have hq : MirLiftCore.CallTargetInCone cone s (s.memory.activeCallee.getD root) func
        (length argOps) := h_term
    cases target with
    | some targetBb =>
      unfold evalTerminator; dsimp only
      cases h_res : resolveCallTarget s func (length argOps)
          (bodyLocalDeclsOf (some (s.memory.activeCallee.getD root)))
          (s.memory.activeCallee.getD root).layouts with
      | ub => trivial
      | unsupported => trivial
      | ok tgt localsAfterFunc =>
        obtain ⟨h_dp, h_ta, h_cl⟩ := hq tgt localsAfterFunc h_res
        dsimp only
        cases evalOperandsWithBodyCast localsAfterFunc argOps s.memory.borrows s.memory.globals
            (s.memory.activeCallee.getD root).layouts s.memory.callerLocals
            (bodyLocalDeclsOf (some (s.memory.activeCallee.getD root))) s.memory.callStack with
        | ub => trivial
        | unsupported => trivial
        | ok argVals locals' =>
          dsimp only
          rw [h_ta]
          cases h_lk : lookupCallee s.memory.callees (s.memory.activeCallee.getD root).layouts
              tgt.defPath [] s.memory.traitImpls with
          | some calleeBody =>
            dsimp only
            cases checkCalleeTargetCompatible tgt calleeBody (length argVals) with
            | false => trivial
            | true =>
              rw [h_inv.1] at h_lk
              exact closedInvLookup_push h_inv h_cur (inConeLookup_of_lookup h_dp h_lk)
          | none =>
            dsimp only
            repeat' (first
              | trivial | exact h_inv
              | exact nodeSuccs_closedInvLookup_of_ctx h_inv
                  (MirLiftCore.writeIntrinsicReturn_calleeCtx_preserved _ _ _ _ _)
                  (MirLiftCore.writeIntrinsicReturn_callerBodies _ _ _ _ _)
              | exact nodeSuccs_evalDirectRustIntrinsic?_lookup h_inv _ _ _ _ _ _ _ _ _ _ h_cl _
                  (by
                    repeat' (first
                      | trivial | exact h_inv
                      | exact nodeSuccs_closedInvLookup_of_ctx h_inv
                          (MirLiftCore.writeIntrinsicReturn_calleeCtx_preserved _ _ _ _ _)
                          (MirLiftCore.writeIntrinsicReturn_callerBodies _ _ _ _ _)
                      | split))
              | split)
    | none =>
      unfold evalTerminator; dsimp only
      cases h_res : resolveCallTarget s func (length argOps)
          (bodyLocalDeclsOf (some (s.memory.activeCallee.getD root)))
          (s.memory.activeCallee.getD root).layouts with
      | ub => trivial
      | unsupported => trivial
      | ok tgt localsAfterFunc =>
        obtain ⟨h_dp, h_ta, h_cl⟩ := hq tgt localsAfterFunc h_res
        dsimp only
        cases evalOperandsWithBodyCast localsAfterFunc argOps s.memory.borrows s.memory.globals
            (s.memory.activeCallee.getD root).layouts s.memory.callerLocals
            (bodyLocalDeclsOf (some (s.memory.activeCallee.getD root))) s.memory.callStack with
        | ub => trivial
        | unsupported => trivial
        | ok argVals locals' =>
          dsimp only
          rw [h_ta]
          cases h_lk : lookupCallee s.memory.callees (s.memory.activeCallee.getD root).layouts
              tgt.defPath [] s.memory.traitImpls with
          | some calleeBody =>
            dsimp only
            cases checkCalleeTargetCompatible tgt calleeBody (length argVals) with
            | false => trivial
            | true =>
              rw [h_inv.1] at h_lk
              exact closedInvLookup_push h_inv h_cur (inConeLookup_of_lookup h_dp h_lk)
          | none =>
            dsimp only
            rcases Anneal.PureMirExec.evalDivergingRustIntrinsic?_eq_none_or_fault s tgt
                (bodyLocalDeclsOf (some (s.memory.activeCallee.getD root)))
                (s.memory.activeCallee.getD root).layouts argOps argVals locals' destination with
              h_di | ⟨fk, h_di⟩ | h_di <;>
              (rw [h_di]; repeat' (first | trivial | exact nodeSuccs_applyUnwindLookup h_inv _ _ | split))
  | tailCall func argOps =>
    have hq : MirLiftCore.CallTargetInCone cone s (s.memory.activeCallee.getD root) func
        (length argOps) := h_term
    unfold evalTerminator; dsimp only
    unfold evalTailCallTerminator; dsimp only
    cases h_res : resolveCallTarget s func (length argOps)
        (bodyLocalDeclsOf (some (s.memory.activeCallee.getD root)))
        (s.memory.activeCallee.getD root).layouts with
    | ub => trivial
    | unsupported => trivial
    | ok tgt localsAfterFunc =>
      obtain ⟨h_dp, h_ta, _⟩ := hq tgt localsAfterFunc h_res
      dsimp only
      cases evalOperandsWithBodyCast localsAfterFunc argOps s.memory.borrows s.memory.globals
          (s.memory.activeCallee.getD root).layouts s.memory.callerLocals
          (bodyLocalDeclsOf (some (s.memory.activeCallee.getD root))) s.memory.callStack with
      | ub => trivial
      | unsupported => trivial
      | ok argVals locals' =>
        dsimp only
        cases hasFrameDeallocProtectorConflict s.memory.borrows s.memory.activeProtectors
            (length s.memory.callStack) (length s.frame.locals) with
        | true => trivial
        | false =>
          dsimp only
          rw [h_ta]
          cases h_lk : lookupCallee s.memory.callees (s.memory.activeCallee.getD root).layouts
              tgt.defPath [] s.memory.traitImpls with
          | none => trivial
          | some calleeBody =>
            dsimp only
            rw [h_inv.1] at h_lk
            cases checkCalleeTargetCompatible tgt calleeBody (length argVals) with
            | false => trivial
            | true =>
              dsimp only [MirLiftCore.NodeSuccs]
              refine ⟨(tailCalleeEntryMemory_callees _ _ _ _).trans h_inv.1,
                inConeLookup_of_lookup h_dp h_lk, ?_⟩
              dsimp only [enterTailCalleeFrame]
              rw [tailCalleeEntryMemory_callStack]
              intro f hf
              rcases Anneal.PureMirExec.narrowCallStackForTailCallee_mem hf with
                ⟨f₀, hf₀, _, hcb⟩
              rw [hcb.2.2]
              exact h_inv.2.2 f₀ hf₀
  | _ => trivial

theorem nodeSuccs_stepMirFnLookup {cone : List DefPath} {root : CapturedMir}
    {tbl : OpaqueCalleeTable} {s : MachineState}
    (h_closed : tbl.callConeClosed cone root = true)
    (h_inv : ClosedInvLookup cone root tbl s) :
    MirLiftCore.NodeSuccs (ClosedInvLookup cone root tbl) (stepMirFn root s) := by
  have h_safe := stepConeSafe_of_closedInvLookup h_closed h_inv
  unfold stepMirFn; dsimp only
  split
  · trivial
  · cases h_bb : get? (s.memory.activeCallee.getD root).basicBlocks s.frame.blockIdx with
    | none => trivial
    | some blk =>
      obtain ⟨h_stmt, h_term⟩ := h_safe blk h_bb
      dsimp only
      cases h_st : get? blk.statements s.frame.stmtIdx with
      | some stmt =>
        dsimp only
        exact nodeSuccs_closedInvLookup_of_ctx h_inv
          (MirLiftCore.evalStmt_calleeCtx_preserved s stmt _ _ (h_stmt stmt h_st))
          (MirLiftCore.evalStmt_callerBodies s stmt _ _)
      | none =>
        dsimp only
        by_cases h_end : (s.frame.stmtIdx == length blk.statements) = true
        · simp only [h_end, ite_true]
          exact nodeSuccs_evalTerminatorLookup h_inv h_term
        · simp only [h_end, Bool.false_eq_true, ite_false]
          trivial

/-- **`tbl.toList`-free syntactic closure implies `MirLiftCore.ConeReach`** for every fuel bound. -/
theorem coneReach_of_closedInvLookup {cone : List DefPath} {root : CapturedMir}
    {tbl : OpaqueCalleeTable} (h_closed : tbl.callConeClosed cone root = true) :
    ∀ (fuel : Nat) (s : MachineState), ClosedInvLookup cone root tbl s →
      MirLiftCore.ConeReach root (MirLiftCore.StepConeSafe cone root) fuel (.running s)
  | 0, _, _ => trivial
  | fuel + 1, s, h_inv => by
    refine ⟨stepConeSafe_of_closedInvLookup h_closed h_inv, ?_⟩
    have h_succ := nodeSuccs_stepMirFnLookup h_closed h_inv
    revert h_succ
    cases stepMirFn root s with
    | ret _ => intro _; trivial
    | tau st' =>
      cases st' with
      | running s' => intro h; exact coneReach_of_closedInvLookup h_closed fuel s' h
      | halted _ => intro _; cases fuel <;> trivial
      | faulted _ => intro _; cases fuel <;> trivial
    | vis e k =>
      rcases e with fk | obs | ⟨req⟩
      · intro _; trivial
      · intro h
        show MirLiftCore.ConeReach root _ fuel (k PUnit.unit)
        revert h
        show (match k PUnit.unit with
          | .running s' => ClosedInvLookup cone root tbl s'
          | _ => True) → _
        cases k PUnit.unit with
        | running s' => intro h; exact coneReach_of_closedInvLookup h_closed fuel s' h
        | halted _ => intro _; cases fuel <;> trivial
        | faulted _ => intro _; cases fuel <;> trivial
      · intro _; trivial

theorem initMachineStateWithMemoryAndCallees_activeCallee (body : CapturedMir) (args : List Value)
    (mem : Memory) (c : List CapturedMir) :
    (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem c).memory.activeCallee =
      mem.activeCallee := by
  cases c <;> rfl

theorem initMachineStateWithMemoryAndCallees_callStack (body : CapturedMir) (args : List Value)
    (mem : Memory) (c : List CapturedMir) :
    (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem c).memory.callStack =
      mem.callStack := by
  cases c <;> rfl

theorem closedInvLookup_init_of_wf (cone : List DefPath) (body : CapturedMir) (args : List Value)
    (mem : Memory) {tbl : OpaqueCalleeTable} (h₁ : MirLiftCore.CalleeInitWf body mem tbl.toList)
    (h_ac : mem.activeCallee = none) (h_cs : mem.callStack = []) :
    ClosedInvLookup cone body tbl
      (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem tbl.toList) := by
  refine ⟨MirLiftCore.initMachineStateWithMemoryAndCallees_callees_of_wf body args mem h₁, ?_, ?_⟩
  · show InConeLookup cone body tbl
      ((Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem
        tbl.toList).memory.activeCallee.getD body)
    rw [initMachineStateWithMemoryAndCallees_activeCallee, h_ac]
    exact Or.inl rfl
  · intro f hf
    rw [initMachineStateWithMemoryAndCallees_callStack, h_cs] at hf
    cases hf

/-- **`tbl.toList`-free syntactic `runCfgWithCallees` narrowing between opaque tables**
(discharged via `t₁.callConeClosed`, which queries only `t₁.lookupRaw` on `cone`). -/
theorem runCfgWithCallees_cone_narrow_of_callConeClosed_wf (cone : List DefPath) (fuel : Nat)
    (body : CapturedMir) (args : List Value) (mem : Memory) {t₁ t₂ : OpaqueCalleeTable}
    (h₁ : MirLiftCore.CalleeInitWf body mem t₁.toList)
    (h₂ : MirLiftCore.CalleeInitWf body mem t₂.toList)
    (h_agree : OpaqueCalleeTable.AgreesOn cone t₁ t₂)
    (h_closed : t₁.callConeClosed cone body = true)
    (h_ac : mem.activeCallee = none) (h_cs : mem.callStack = []) :
    MirLiftCore.runCfgWithCallees fuel body args mem t₂.toList =
      (MirLiftCore.runCfgWithCallees fuel body args mem t₁.toList).map
        (MirLiftCore.MirOutcome.mapMem (MirLiftCore.Memory.withCallees t₂.toList)) := by
  unfold MirLiftCore.runCfgWithCallees
  rw [MirLiftCore.initMachineStateWithMemoryAndCallees_withCallees_of_wf body args mem h₁ h₂]
  refine MirLiftCore.runMirExecBounded_cone_narrow cone body t₂.toList fuel _
    (coneReach_of_closedInvLookup h_closed fuel _
      (closedInvLookup_init_of_wf cone body args mem h₁ h_ac h_cs)) ?_
  intro s hs
  cases hs
  rw [MirLiftCore.initMachineStateWithMemoryAndCallees_callees_of_wf body args mem h₁]
  exact calleesAgreeOn_of_agreesOn h_agree

/-- **`tbl.toList`-free syntactic `wpMirExecSym` narrowing between opaque tables.** -/
theorem wpMirExecSym_cone_narrow_of_callConeClosed_wf (cone : List DefPath) (fuel : Nat)
    (body : CapturedMir) (args : List Value) (mem : Memory) {t₁ t₂ : OpaqueCalleeTable}
    (h₁ : MirLiftCore.CalleeInitWf body mem t₁.toList)
    (h₂ : MirLiftCore.CalleeInitWf body mem t₂.toList)
    (h_agree : OpaqueCalleeTable.AgreesOn cone t₁ t₂)
    (h_closed : t₁.callConeClosed cone body = true)
    (h_ac : mem.activeCallee = none) (h_cs : mem.callStack = [])
    (post : MirOutcome → Prop)
    (h_post : ∀ out,
      post (MirLiftCore.MirOutcome.mapMem (MirLiftCore.Memory.withCallees t₂.toList) out) ↔ post out) :
    Anneal.Rustc.V2026_06_01.SymbolicEval.wpMirExecSym fuel body
        (.running (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem
          t₂.toList)) post ↔
      Anneal.Rustc.V2026_06_01.SymbolicEval.wpMirExecSym fuel body
        (.running (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem
          t₁.toList)) post := by
  rw [MirLiftCore.initMachineStateWithMemoryAndCallees_withCallees_of_wf body args mem h₁ h₂]
  refine MirLiftCore.wpMirExecSym_cone_narrow cone body t₂.toList post h_post fuel _
    (coneReach_of_closedInvLookup h_closed fuel _
      (closedInvLookup_init_of_wf cone body args mem h₁ h_ac h_cs)) ?_
  intro s hs
  cases hs
  rw [MirLiftCore.initMachineStateWithMemoryAndCallees_callees_of_wf body args mem h₁]
  exact calleesAgreeOn_of_agreesOn h_agree

/-- **`tbl.toList`-free syntactic `MirWpConverges` narrowing between opaque tables.** -/
theorem mirWpConverges_cone_narrow_of_callConeClosed_wf (cone : List DefPath)
    (body : CapturedMir) (args : List Value) (mem : Memory) {t₁ t₂ : OpaqueCalleeTable}
    (h₁ : MirLiftCore.CalleeInitWf body mem t₁.toList)
    (h₂ : MirLiftCore.CalleeInitWf body mem t₂.toList)
    (h_agree : OpaqueCalleeTable.AgreesOn cone t₁ t₂)
    (h_closed : t₁.callConeClosed cone body = true)
    (h_ac : mem.activeCallee = none) (h_cs : mem.callStack = [])
    (post : MirOutcome → Prop)
    (h_post : ∀ out,
      post (MirLiftCore.MirOutcome.mapMem (MirLiftCore.Memory.withCallees t₂.toList) out) ↔ post out) :
    MirFuelFree.MirWpConverges body
        (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem
          t₂.toList) post ↔
      MirFuelFree.MirWpConverges body
        (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem
          t₁.toList) post := by
  rw [MirLiftCore.initMachineStateWithMemoryAndCallees_withCallees_of_wf body args mem h₁ h₂]
  refine MirLiftCore.mirWpConverges_cone_narrow cone body t₂.toList post h_post _
    (fun fuel =>
      coneReach_of_closedInvLookup h_closed fuel _
        (closedInvLookup_init_of_wf cone body args mem h₁ h_ac h_cs)) ?_
  rw [MirLiftCore.initMachineStateWithMemoryAndCallees_callees_of_wf body args mem h₁]
  exact calleesAgreeOn_of_agreesOn h_agree

/-- `b` is the root body or an instantiation `b₀.instantiate subst` of a first-match body
`tbl.lookupRaw dp = some b₀` for some `dp ∈ cone`. -/
def InConeLookupPoly (cone : List DefPath) (root : CapturedMir) (tbl : OpaqueCalleeTable)
    (b : CapturedMir) : Prop :=
  b = root ∨ ∃ dp, dp ∈ cone ∧ ∃ b₀ subst, tbl.lookupRaw dp = some b₀ ∧ b = b₀.instantiate subst

/-- Reachable-state invariant of a `callConeClosedPoly` execution over `tbl`. -/
def ClosedInvLookupPoly (cone : List DefPath) (root : CapturedMir) (tbl : OpaqueCalleeTable)
    (ti : List TraitImplEntry) (s : MachineState) : Prop :=
  s.memory.callees = tbl.toList ∧ s.memory.traitImpls = ti ∧
    InConeLookupPoly cone root tbl (s.memory.activeCallee.getD root) ∧
    ∀ f, f ∈ s.memory.callStack → InConeLookupPoly cone root tbl f.callerBody

theorem bodyCallsInConePoly_of_inConeLookupPoly {cone : List DefPath} {root : CapturedMir}
    {tbl : OpaqueCalleeTable} {ti : List TraitImplEntry} {b : CapturedMir}
    (h_closed : tbl.callConeClosedPoly cone root ti = true)
    (hb : InConeLookupPoly cone root tbl b) : MirLiftCore.bodyCallsInConePoly cone b = true := by
  unfold OpaqueCalleeTable.callConeClosedPoly at h_closed
  rw [Bool.and_eq_true] at h_closed
  rcases hb with rfl | ⟨dp, hdp, b₀, subst, hraw, rfl⟩
  · exact h_closed.1
  · have h := List.all_eq_true.mp h_closed.2 dp hdp
    rw [Bool.and_eq_true, hraw] at h
    exact MirLiftCore.bodyCallsInConePoly_instantiate subst h.1

theorem noTraitImpl_of_callConeClosedPoly_lookup {cone : List DefPath} {root : CapturedMir}
    {tbl : OpaqueCalleeTable} {ti : List TraitImplEntry} {dp : DefPath}
    (h_closed : tbl.callConeClosedPoly cone root ti = true) (h_dp : dp ∈ cone) :
    hasTraitImplForDefPath (ti ++ flatMapTraitImpls tbl.toList) dp = false := by
  unfold OpaqueCalleeTable.callConeClosedPoly at h_closed
  rw [Bool.and_eq_true] at h_closed
  have h := List.all_eq_true.mp h_closed.2 dp h_dp
  rw [Bool.and_eq_true, OpaqueCalleeTable.traitImpls_eq] at h
  cases htr : hasTraitImplForDefPath (ti ++ flatMapTraitImpls tbl.toList) dp with
  | false => rfl
  | true => rw [htr] at h; cases h.2

theorem stepConeSafePoly_of_closedInvLookupPoly {cone : List DefPath} {root : CapturedMir}
    {tbl t₂ : OpaqueCalleeTable} {ti : List TraitImplEntry} {s : MachineState}
    (h_closed : tbl.callConeClosedPoly cone root ti = true)
    (h_no₂ : ∀ dp, dp ∈ cone → hasTraitImplForDefPath (ti ++ t₂.traitImpls) dp = false)
    (h_inv : ClosedInvLookupPoly cone root tbl ti s) :
    MirLiftCore.StepConeSafePoly cone t₂.toList root s := by
  intro blk h_bb
  have h_body := bodyCallsInConePoly_of_inConeLookupPoly h_closed h_inv.2.2.1
  unfold MirLiftCore.bodyCallsInConePoly at h_body
  have h_blk := List.all_eq_true.mp h_body blk (List.mem_of_getElem? h_bb)
  rw [Bool.and_eq_true] at h_blk
  refine ⟨fun stmt h_st => List.all_eq_true.mp h_blk.1 stmt (List.mem_of_getElem? h_st), ?_⟩
  have h_tc := h_blk.2
  revert h_tc
  rcases blk.terminator with ⟨kind, span⟩
  intro h_tc
  cases kind with
  | call func argOps _ _ _ =>
    intro tgt l h_res
    unfold MirLiftCore.termCallsInConePoly MirLiftCore.directCallInConePoly at h_tc
    dsimp only at h_tc
    cases h_fn : MirLiftCore.extractFnDefPath? func with
    | none => rw [h_fn] at h_tc; cases h_tc
    | some dp =>
      rw [h_fn, Bool.and_eq_true] at h_tc
      have h_cd := MirLiftCore.extractCalleeDefPath?_of_extractFnDefPath? h_fn
      unfold resolveCallTarget at h_res
      rw [h_cd] at h_res
      cases h_res
      have h_dp : dp ∈ cone := MirLiftCore.inCone_iff.mp h_tc.1
      rw [h_inv.1, h_inv.2.1]
      exact ⟨h_dp, noTraitImpl_of_callConeClosedPoly_lookup h_closed h_dp,
        noTraitImplInCone_toList h_no₂ dp h_dp, h_tc.2⟩
  | tailCall func argOps =>
    intro tgt l h_res
    unfold MirLiftCore.termCallsInConePoly MirLiftCore.directCallInConePoly at h_tc
    dsimp only at h_tc
    cases h_fn : MirLiftCore.extractFnDefPath? func with
    | none => rw [h_fn] at h_tc; cases h_tc
    | some dp =>
      rw [h_fn, Bool.and_eq_true] at h_tc
      have h_cd := MirLiftCore.extractCalleeDefPath?_of_extractFnDefPath? h_fn
      unfold resolveCallTarget at h_res
      rw [h_cd] at h_res
      cases h_res
      have h_dp : dp ∈ cone := MirLiftCore.inCone_iff.mp h_tc.1
      rw [h_inv.1, h_inv.2.1]
      exact ⟨h_dp, noTraitImpl_of_callConeClosedPoly_lookup h_closed h_dp,
        noTraitImplInCone_toList h_no₂ dp h_dp, h_tc.2⟩
  | _ => trivial

theorem closedInvLookupPoly_of_callerBodies {cone : List DefPath} {root : CapturedMir}
    {tbl : OpaqueCalleeTable} {ti : List TraitImplEntry} {s s' : MachineState}
    (h_inv : ClosedInvLookupPoly cone root tbl ti s)
    (hc : s'.memory.callees = s.memory.callees)
    (hti : s'.memory.traitImpls = s.memory.traitImpls)
    (hac : s'.memory.activeCallee = s.memory.activeCallee)
    (hb : MirLiftCore.CallerBodiesEq s.memory.callStack s'.memory.callStack) :
    ClosedInvLookupPoly cone root tbl ti s' := by
  refine ⟨hc.trans h_inv.1, hti.trans h_inv.2.1, hac ▸ h_inv.2.2.1, ?_⟩
  intro f hf
  obtain ⟨f₀, hf₀, he⟩ := hb.mem hf
  exact he ▸ h_inv.2.2.2 f₀ hf₀

theorem nodeSuccs_closedInvLookupPoly_of_ctx {cone : List DefPath} {root : CapturedMir}
    {tbl : OpaqueCalleeTable} {ti : List TraitImplEntry} {s : MachineState} {n : MirStepNode}
    (h_inv : ClosedInvLookupPoly cone root tbl ti s)
    (hfix : n = MirLiftCore.MirStepNode.mapMem
      (MirLiftCore.Memory.withCalleeCtx s.memory.callees s.memory.activeCallee
        s.memory.traitImpls) n)
    (hb : MirLiftCore.NodeSuccs
      (fun s' => MirLiftCore.CallerBodiesEq s.memory.callStack s'.memory.callStack) n) :
    MirLiftCore.NodeSuccs (ClosedInvLookupPoly cone root tbl ti) n := by
  refine MirLiftCore.NodeSuccs.mono ?_
    (MirLiftCore.NodeSuccs.and
      (MirLiftCore.nodeSuccs_of_fixed (P := fun s' => s' = MirLiftCore.MachineState.mapMem
        (MirLiftCore.Memory.withCalleeCtx s.memory.callees s.memory.activeCallee
          s.memory.traitImpls) s')
        hfix (fun _ h => h))
      hb)
  rintro s' ⟨hs', hb'⟩
  have hm : s'.memory =
      MirLiftCore.Memory.withCalleeCtx s.memory.callees s.memory.activeCallee
        s.memory.traitImpls s'.memory :=
    congrArg MachineState.memory hs'
  exact closedInvLookupPoly_of_callerBodies h_inv (by rw [hm]) (by rw [hm]) (by rw [hm]) hb'

theorem closedInvLookupPoly_return {cone : List DefPath} {root : CapturedMir}
    {tbl : OpaqueCalleeTable} {ti : List TraitImplEntry} {s : MachineState}
    {caller : SavedCallerFrame} {rest : List SavedCallerFrame} {retVal : Value}
    {locals' : List LocalSlot} {mem' : Memory} {F : StackFrame}
    (h_inv : ClosedInvLookupPoly cone root tbl ti s) (h_cs : s.memory.callStack = caller :: rest)
    (h_w : writeReturnDestination caller.frame.locals (MirLiftCore.ccReturnCallerMem s caller rest)
      caller.destination retVal caller.callerBody.localDecls caller.callerBody.layouts =
        .ok locals' mem') :
    ClosedInvLookupPoly cone root tbl ti { frame := F, memory := mem' } := by
  obtain ⟨hc, hac, hti⟩ := MirLiftCore.writeReturnDestination_ctx_preserved h_w
  have hb := MirLiftCore.writeReturnDestination_callerBodies h_w
  refine ⟨hc.trans h_inv.1, hti.trans h_inv.2.1, ?_, ?_⟩
  · show InConeLookupPoly cone root tbl (mem'.activeCallee.getD root)
    rw [hac]
    exact h_inv.2.2.2 caller (by rw [h_cs]; exact List.Mem.head _)
  · intro f hf
    obtain ⟨f₀, hf₀, he⟩ := hb.mem hf
    exact he ▸ h_inv.2.2.2 f₀ (by rw [h_cs]; exact List.Mem.tail _ hf₀)

theorem closedInvLookupPoly_unwindFromCallStack {cone : List DefPath} {root : CapturedMir}
    {tbl : OpaqueCalleeTable} {ti : List TraitImplEntry} :
    ∀ (stk : List SavedCallerFrame) (m : Memory), m.callees = tbl.toList → m.traitImpls = ti →
      (∀ f, f ∈ stk → InConeLookupPoly cone root tbl f.callerBody) →
      ∀ s', unwindFromCallStack stk m = .running s' → ClosedInvLookupPoly cone root tbl ti s'
  | [], m, _, _, _, _, h => by
    unfold unwindFromCallStack at h
    cases hr : m.rootUnwindCeiling <;> (rw [hr] at h; cases h)
  | caller :: rest, m, hc, hti, hf, s', h => by
    unfold unwindFromCallStack at h
    dsimp only at h
    cases hr : caller.returnUnwind with
    | unreachable => rw [hr] at h; dsimp only at h; cases h
    | terminate => rw [hr] at h; dsimp only at h; cases h
    | continue_ =>
      rw [hr] at h
      dsimp only at h
      exact closedInvLookupPoly_unwindFromCallStack rest
        { m with
          callStack := rest
          activeCallee := some caller.callerBody
          activeProtectors := restoreCallerProtectors caller }
        hc hti (fun f hm => hf f (List.Mem.tail _ hm)) s' h
    | cleanup bb =>
      rw [hr] at h
      dsimp only at h
      cases h
      exact ⟨hc, hti, hf caller (List.Mem.head _), fun f hm => hf f (List.Mem.tail _ hm)⟩

private theorem nodeSuccs_unwindMatchLookupPoly {cone : List DefPath} {root : CapturedMir}
    {tbl : OpaqueCalleeTable} {ti : List TraitImplEntry} (st : MirExecState)
    (h : ∀ s', st = .running s' → ClosedInvLookupPoly cone root tbl ti s') :
    MirLiftCore.NodeSuccs (ClosedInvLookupPoly cone root tbl ti)
      (match (generalizing := false) st with
        | .running nextState => MirStepNode.step nextState
        | .halted out => MirStepNode.retOutcome out
        | .faulted fk => MirStepNode.fail fk) := by
  cases st with
  | running s' => exact h s' rfl
  | halted _ => trivial
  | faulted _ => trivial

private theorem nodeSuccs_applyUnwindLookupPoly {cone : List DefPath} {root : CapturedMir}
    {tbl : OpaqueCalleeTable} {ti : List TraitImplEntry} {s : MachineState}
    (h_inv : ClosedInvLookupPoly cone root tbl ti s) (l : List LocalSlot) (u : UnwindAction) :
    MirLiftCore.NodeSuccs (ClosedInvLookupPoly cone root tbl ti)
      (match applyUnwindAction s l s.memory u with
        | .running nextState => MirStepNode.step nextState
        | .halted out => MirStepNode.retOutcome out
        | .faulted fk => MirStepNode.fail fk) := by
  refine nodeSuccs_unwindMatchLookupPoly _ ?_
  intro s' hs'
  cases u with
  | unreachable => cases hs'
  | terminate => cases hs'
  | continue_ =>
    exact closedInvLookupPoly_unwindFromCallStack s.memory.callStack s.memory h_inv.1 h_inv.2.1
      h_inv.2.2.2 s' hs'
  | cleanup bb =>
    cases hs'
    exact h_inv

private theorem inConeLookupPoly_of_lookup {cone : List DefPath} {root : CapturedMir}
    {tbl : OpaqueCalleeTable} {L : LayoutTable} {dp : DefPath} {typeArgs : List RigidTy}
    {ti : List TraitImplEntry} {calleeBody : CapturedMir}
    (h_dp : dp ∈ cone)
    (h_no : hasTraitImplForDefPath (ti ++ flatMapTraitImpls tbl.toList) dp = false)
    (h_lk : lookupCallee tbl.toList L dp typeArgs ti = some calleeBody) :
    InConeLookupPoly cone root tbl calleeBody := by
  obtain ⟨b₀, subst, hf, hinst⟩ := MirLiftCore.lookupCallee_eq_some_of_no_traitImpl h_no h_lk
  exact Or.inr ⟨dp, h_dp, b₀, subst, (OpaqueCalleeTable.lookupRaw_eq tbl dp).trans hf, hinst⟩

private theorem closedInvLookupPoly_push {cone : List DefPath} {root : CapturedMir}
    {tbl : OpaqueCalleeTable} {ti : List TraitImplEntry} {s : MachineState}
    {saved : SavedCallerFrame} {b : CapturedMir} {F : StackFrame}
    (h_inv : ClosedInvLookupPoly cone root tbl ti s)
    (h_saved : InConeLookupPoly cone root tbl saved.callerBody)
    (h_b : InConeLookupPoly cone root tbl b) :
    ClosedInvLookupPoly cone root tbl ti
      { frame := F,
        memory := { s.memory with
          callStack := saved :: s.memory.callStack
          activeCallee := some b } } := by
  refine ⟨h_inv.1, h_inv.2.1, h_b, ?_⟩
  intro f hf
  cases hf with
  | head => exact h_saved
  | tail _ hf => exact h_inv.2.2.2 f hf

theorem nodeSuccs_evalDirectRustIntrinsic?_lookupPoly {cone : List DefPath}
    {root : CapturedMir} {tbl : OpaqueCalleeTable} {ti : List TraitImplEntry} {s : MachineState}
    (h_inv : ClosedInvLookupPoly cone root tbl ti s) (currentBody : Option CapturedMir)
    (target : ResolvedCallTarget) (bodyLocalDecls : List LocalDecl) (bodyLayouts : LayoutTable)
    (argOps : List Operand) (argVals : List Value) (locals' : List LocalSlot)
    (destination : Place) (targetBb : BasicBlockIdx) (unwind : UnwindAction)
    (h_cl : MirLiftCore.isNonSelectIntrinsicOpt (classifyRustIntrinsic? target.defPath) = true)
    (fallback : MirStepNode)
    (h_fb : MirLiftCore.NodeSuccs (ClosedInvLookupPoly cone root tbl ti) fallback) :
    MirLiftCore.NodeSuccs (ClosedInvLookupPoly cone root tbl ti)
      (match evalDirectRustIntrinsic? s currentBody target bodyLocalDecls bodyLayouts
          argOps argVals locals' destination targetBb unwind with
       | some stepNode => stepNode
       | none => fallback) := by
  unfold evalDirectRustIntrinsic?
  cases h_k : classifyRustIntrinsic? target.defPath with
  | none => exact h_fb
  | some kind =>
    rw [h_k] at h_cl
    have h_step : ∀ (k : RustIntrinsicKind),
        MirLiftCore.NodeSuccs (ClosedInvLookupPoly cone root tbl ti)
          (match evalCoreMemPtrIntrinsicCall? k s target bodyLocalDecls bodyLayouts
              argOps argVals locals' destination (.some targetBb) with
           | some sn => sn
           | none => evalNonSelectIntrinsicCall k s target bodyLocalDecls bodyLayouts
               argOps argVals locals' destination targetBb) := by
      intro k
      cases h_cm : evalCoreMemPtrIntrinsicCall? k s target bodyLocalDecls bodyLayouts
          argOps argVals locals' destination (.some targetBb) with
      | some sn =>
        exact nodeSuccs_closedInvLookupPoly_of_ctx h_inv
          (MirLiftCore.evalCoreMemPtrIntrinsicCall?_calleeCtx_preserved k s target bodyLocalDecls bodyLayouts
            argOps argVals locals' destination (.some targetBb) h_cm)
          (MirLiftCore.evalCoreMemPtrIntrinsicCall?_callerBodies k s target bodyLocalDecls bodyLayouts
            argOps argVals locals' destination (.some targetBb) h_cm)
      | none =>
        exact nodeSuccs_closedInvLookupPoly_of_ctx h_inv
          (MirLiftCore.evalNonSelectIntrinsicCall_calleeCtx_preserved k s target bodyLocalDecls bodyLayouts
            argOps argVals locals' destination targetBb)
          (MirLiftCore.evalNonSelectIntrinsicCall_callerBodies k s target bodyLocalDecls bodyLayouts
            argOps argVals locals' destination targetBb)
    cases h_sp : (match kind with
      | .constEvalSelect | .copyNonOverlapping | .writeBytes => true
      | _ => false) with
    | true =>
      cases kind with
      | constEvalSelect => cases h_cl
      | copyNonOverlapping =>
        exact nodeSuccs_closedInvLookupPoly_of_ctx h_inv
          (MirLiftCore.evalCopyNonOverlappingCall_calleeCtx_preserved s bodyLocalDecls bodyLayouts
            argOps argVals locals' destination targetBb)
          (MirLiftCore.evalCopyNonOverlappingCall_callerBodies s bodyLocalDecls bodyLayouts
            argOps argVals locals' destination targetBb)
      | writeBytes =>
        exact nodeSuccs_closedInvLookupPoly_of_ctx h_inv
          (MirLiftCore.evalWriteBytesCall_calleeCtx_preserved s target bodyLocalDecls bodyLayouts
            argOps argVals locals' destination targetBb)
          (MirLiftCore.evalWriteBytesCall_callerBodies s target bodyLocalDecls bodyLayouts
            argOps argVals locals' destination targetBb)
      | _ => cases h_sp
    | false =>
      have h_eq :
          evalDirectRustIntrinsic? s currentBody target bodyLocalDecls bodyLayouts
            argOps argVals locals' destination targetBb unwind =
          some (match evalCoreMemPtrIntrinsicCall? kind s target bodyLocalDecls bodyLayouts
              argOps argVals locals' destination (.some targetBb) with
           | some sn => sn
           | none => evalNonSelectIntrinsicCall kind s target bodyLocalDecls bodyLayouts
               argOps argVals locals' destination targetBb) := by
        unfold evalDirectRustIntrinsic?; rw [h_k]
        cases kind <;> first | (cases h_sp; done) | rfl
      unfold evalDirectRustIntrinsic? at h_eq
      rw [h_k] at h_eq
      rw [h_eq]
      exact h_step kind

theorem nodeSuccs_evalTerminatorLookupPoly {cone : List DefPath} {root : CapturedMir}
    {tbl t₂ : OpaqueCalleeTable} {ti : List TraitImplEntry} {s : MachineState} {term : Terminator}
    (h_inv : ClosedInvLookupPoly cone root tbl ti s)
    (h_term : MirLiftCore.TermConeSafePoly cone t₂.toList s (s.memory.activeCallee.getD root) term) :
    MirLiftCore.NodeSuccs (ClosedInvLookupPoly cone root tbl ti)
      (evalTerminator s term (some (s.memory.activeCallee.getD root))) := by
  have h_cur : InConeLookupPoly cone root tbl (s.memory.activeCallee.getD root) := h_inv.2.2.1
  rcases term with ⟨kind, span⟩
  cases kind with
  | goto target => exact h_inv
  | switchInt discr targets =>
    unfold evalTerminator; dsimp only
    repeat' (first | trivial | exact h_inv | split)
  | unwindResume =>
    unfold evalTerminator; dsimp only
    exact nodeSuccs_unwindMatchLookupPoly _
      (closedInvLookupPoly_unwindFromCallStack s.memory.callStack s.memory h_inv.1 h_inv.2.1
        h_inv.2.2.2)
  | unwindTerminate => trivial
  | return_ =>
    rw [MirLiftCore.ccEvalReturn_eq]
    unfold MirLiftCore.ccEvalReturn
    repeat' (first | trivial | exact closedInvLookupPoly_return h_inv ‹_› ‹_› | split)
  | unreachable => trivial
  | drop place target unwind =>
    unfold evalTerminator; dsimp only
    repeat' (first | trivial | exact h_inv | split)
  | assert cond expected target unwind =>
    unfold evalTerminator; dsimp only
    repeat' (first | trivial | exact h_inv | exact nodeSuccs_applyUnwindLookupPoly h_inv _ _ | split)
  | call func argOps destination target unwind =>
    have hq : MirLiftCore.CallTargetInConePoly cone t₂.toList s (s.memory.activeCallee.getD root)
        func (length argOps) := h_term
    cases target with
    | some targetBb =>
      unfold evalTerminator; dsimp only
      cases h_res : resolveCallTarget s func (length argOps)
          (bodyLocalDeclsOf (some (s.memory.activeCallee.getD root)))
          (s.memory.activeCallee.getD root).layouts with
      | ub => trivial
      | unsupported => trivial
      | ok tgt localsAfterFunc =>
        obtain ⟨h_dp, h_no₁, _, h_cl⟩ := hq tgt localsAfterFunc h_res
        dsimp only
        cases evalOperandsWithBodyCast localsAfterFunc argOps s.memory.borrows s.memory.globals
            (s.memory.activeCallee.getD root).layouts s.memory.callerLocals
            (bodyLocalDeclsOf (some (s.memory.activeCallee.getD root))) s.memory.callStack with
        | ub => trivial
        | unsupported => trivial
        | ok argVals locals' =>
          dsimp only
          cases h_lk : lookupCallee s.memory.callees (s.memory.activeCallee.getD root).layouts
              tgt.defPath tgt.typeArgs s.memory.traitImpls with
          | some calleeBody =>
            dsimp only
            cases checkCalleeTargetCompatible tgt calleeBody (length argVals) with
            | false => trivial
            | true =>
              rw [h_inv.1, h_inv.2.1] at h_lk h_no₁
              exact closedInvLookupPoly_push h_inv h_cur (inConeLookupPoly_of_lookup h_dp h_no₁ h_lk)
          | none =>
            dsimp only
            repeat' (first
              | trivial | exact h_inv
              | exact nodeSuccs_closedInvLookupPoly_of_ctx h_inv
                  (MirLiftCore.writeIntrinsicReturn_calleeCtx_preserved _ _ _ _ _)
                  (MirLiftCore.writeIntrinsicReturn_callerBodies _ _ _ _ _)
              | exact nodeSuccs_evalDirectRustIntrinsic?_lookupPoly h_inv _ _ _ _ _ _ _ _ _ _ h_cl _
                  (by
                    repeat' (first
                      | trivial | exact h_inv
                      | exact nodeSuccs_closedInvLookupPoly_of_ctx h_inv
                          (MirLiftCore.writeIntrinsicReturn_calleeCtx_preserved _ _ _ _ _)
                          (MirLiftCore.writeIntrinsicReturn_callerBodies _ _ _ _ _)
                      | split))
              | split)
    | none =>
      unfold evalTerminator; dsimp only
      cases h_res : resolveCallTarget s func (length argOps)
          (bodyLocalDeclsOf (some (s.memory.activeCallee.getD root)))
          (s.memory.activeCallee.getD root).layouts with
      | ub => trivial
      | unsupported => trivial
      | ok tgt localsAfterFunc =>
        obtain ⟨h_dp, h_no₁, _, _⟩ := hq tgt localsAfterFunc h_res
        dsimp only
        cases evalOperandsWithBodyCast localsAfterFunc argOps s.memory.borrows s.memory.globals
            (s.memory.activeCallee.getD root).layouts s.memory.callerLocals
            (bodyLocalDeclsOf (some (s.memory.activeCallee.getD root))) s.memory.callStack with
        | ub => trivial
        | unsupported => trivial
        | ok argVals locals' =>
          dsimp only
          cases h_lk : lookupCallee s.memory.callees (s.memory.activeCallee.getD root).layouts
              tgt.defPath tgt.typeArgs s.memory.traitImpls with
          | some calleeBody =>
            dsimp only
            cases checkCalleeTargetCompatible tgt calleeBody (length argVals) with
            | false => trivial
            | true =>
              rw [h_inv.1, h_inv.2.1] at h_lk h_no₁
              exact closedInvLookupPoly_push h_inv h_cur (inConeLookupPoly_of_lookup h_dp h_no₁ h_lk)
          | none =>
            dsimp only
            rcases Anneal.PureMirExec.evalDivergingRustIntrinsic?_eq_none_or_fault s tgt
                (bodyLocalDeclsOf (some (s.memory.activeCallee.getD root)))
                (s.memory.activeCallee.getD root).layouts argOps argVals locals' destination with
              h_di | ⟨fk, h_di⟩ | h_di <;>
              (rw [h_di]; repeat' (first | trivial | exact nodeSuccs_applyUnwindLookupPoly h_inv _ _ | split))
  | tailCall func argOps =>
    have hq : MirLiftCore.CallTargetInConePoly cone t₂.toList s (s.memory.activeCallee.getD root)
        func (length argOps) := h_term
    unfold evalTerminator; dsimp only
    unfold evalTailCallTerminator; dsimp only
    cases h_res : resolveCallTarget s func (length argOps)
        (bodyLocalDeclsOf (some (s.memory.activeCallee.getD root)))
        (s.memory.activeCallee.getD root).layouts with
    | ub => trivial
    | unsupported => trivial
    | ok tgt localsAfterFunc =>
      obtain ⟨h_dp, h_no₁, _, _⟩ := hq tgt localsAfterFunc h_res
      dsimp only
      cases evalOperandsWithBodyCast localsAfterFunc argOps s.memory.borrows s.memory.globals
          (s.memory.activeCallee.getD root).layouts s.memory.callerLocals
          (bodyLocalDeclsOf (some (s.memory.activeCallee.getD root))) s.memory.callStack with
      | ub => trivial
      | unsupported => trivial
      | ok argVals locals' =>
        dsimp only
        cases hasFrameDeallocProtectorConflict s.memory.borrows s.memory.activeProtectors
            (length s.memory.callStack) (length s.frame.locals) with
        | true => trivial
        | false =>
          dsimp only
          cases h_lk : lookupCallee s.memory.callees (s.memory.activeCallee.getD root).layouts
              tgt.defPath tgt.typeArgs s.memory.traitImpls with
          | none => trivial
          | some calleeBody =>
            dsimp only
            rw [h_inv.1, h_inv.2.1] at h_lk h_no₁
            cases checkCalleeTargetCompatible tgt calleeBody (length argVals) with
            | false => trivial
            | true =>
              dsimp only [MirLiftCore.NodeSuccs]
              refine ⟨(tailCalleeEntryMemory_callees _ _ _ _).trans h_inv.1,
                (tailCalleeEntryMemory_traitImpls _ _ _ _).trans h_inv.2.1,
                inConeLookupPoly_of_lookup h_dp h_no₁ h_lk, ?_⟩
              dsimp only [enterTailCalleeFrame]
              rw [tailCalleeEntryMemory_callStack]
              intro f hf
              rcases Anneal.PureMirExec.narrowCallStackForTailCallee_mem hf with
                ⟨f₀, hf₀, _, hcb⟩
              rw [hcb.2.2]
              exact h_inv.2.2.2 f₀ hf₀
  | _ => trivial

theorem nodeSuccs_stepMirFnLookupPoly {cone : List DefPath} {root : CapturedMir}
    {tbl t₂ : OpaqueCalleeTable} {ti : List TraitImplEntry} {s : MachineState}
    (h_closed : tbl.callConeClosedPoly cone root ti = true)
    (h_no₂ : ∀ dp, dp ∈ cone → hasTraitImplForDefPath (ti ++ t₂.traitImpls) dp = false)
    (h_inv : ClosedInvLookupPoly cone root tbl ti s) :
    MirLiftCore.NodeSuccs (ClosedInvLookupPoly cone root tbl ti) (stepMirFn root s) := by
  have h_safe := stepConeSafePoly_of_closedInvLookupPoly h_closed h_no₂ h_inv
  unfold stepMirFn; dsimp only
  split
  · trivial
  · cases h_bb : get? (s.memory.activeCallee.getD root).basicBlocks s.frame.blockIdx with
    | none => trivial
    | some blk =>
      obtain ⟨h_stmt, h_term⟩ := h_safe blk h_bb
      dsimp only
      cases h_st : get? blk.statements s.frame.stmtIdx with
      | some stmt =>
        dsimp only
        exact nodeSuccs_closedInvLookupPoly_of_ctx h_inv
          (MirLiftCore.evalStmt_calleeCtx_preserved s stmt _ _ (h_stmt stmt h_st))
          (MirLiftCore.evalStmt_callerBodies s stmt _ _)
      | none =>
        dsimp only
        by_cases h_end : (s.frame.stmtIdx == length blk.statements) = true
        · simp only [h_end, ite_true]
          exact nodeSuccs_evalTerminatorLookupPoly h_inv h_term
        · simp only [h_end, Bool.false_eq_true, ite_false]
          trivial

/-- **`tbl.toList`-free polymorphic syntactic closure implies `MirLiftCore.ConeReach`** for every
fuel bound. -/
theorem coneReach_of_closedInvLookupPoly {cone : List DefPath} {root : CapturedMir}
    {tbl t₂ : OpaqueCalleeTable} {ti : List TraitImplEntry}
    (h_closed : tbl.callConeClosedPoly cone root ti = true)
    (h_no₂ : ∀ dp, dp ∈ cone → hasTraitImplForDefPath (ti ++ t₂.traitImpls) dp = false) :
    ∀ (fuel : Nat) (s : MachineState), ClosedInvLookupPoly cone root tbl ti s →
      MirLiftCore.ConeReach root (MirLiftCore.StepConeSafePoly cone t₂.toList root) fuel (.running s)
  | 0, _, _ => trivial
  | fuel + 1, s, h_inv => by
    refine ⟨stepConeSafePoly_of_closedInvLookupPoly h_closed h_no₂ h_inv, ?_⟩
    have h_succ := nodeSuccs_stepMirFnLookupPoly h_closed h_no₂ h_inv
    revert h_succ
    cases stepMirFn root s with
    | ret _ => intro _; trivial
    | tau st' =>
      cases st' with
      | running s' => intro h; exact coneReach_of_closedInvLookupPoly h_closed h_no₂ fuel s' h
      | halted _ => intro _; cases fuel <;> trivial
      | faulted _ => intro _; cases fuel <;> trivial
    | vis e k =>
      rcases e with fk | obs | ⟨req⟩
      · intro _; trivial
      · intro h
        show MirLiftCore.ConeReach root _ fuel (k PUnit.unit)
        revert h
        show (match k PUnit.unit with
          | .running s' => ClosedInvLookupPoly cone root tbl ti s'
          | _ => True) → _
        cases k PUnit.unit with
        | running s' => intro h; exact coneReach_of_closedInvLookupPoly h_closed h_no₂ fuel s' h
        | halted _ => intro _; cases fuel <;> trivial
        | faulted _ => intro _; cases fuel <;> trivial
      · intro _; trivial

theorem closedInvLookupPoly_init_of_wf (cone : List DefPath) (body : CapturedMir) (args : List Value)
    (mem : Memory) {tbl : OpaqueCalleeTable} (h₁ : MirLiftCore.CalleeInitWf body mem tbl.toList)
    (h_ac : mem.activeCallee = none) (h_cs : mem.callStack = []) :
    ClosedInvLookupPoly cone body tbl body.traitImpls
      (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem tbl.toList) := by
  refine ⟨MirLiftCore.initMachineStateWithMemoryAndCallees_callees_of_wf body args mem h₁,
    MirLiftCore.initMachineStateWithMemoryAndCallees_traitImpls_of_wf body args mem h₁, ?_, ?_⟩
  · show InConeLookupPoly cone body tbl
      ((Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem
        tbl.toList).memory.activeCallee.getD body)
    rw [initMachineStateWithMemoryAndCallees_activeCallee, h_ac]
    exact Or.inl rfl
  · intro f hf
    rw [initMachineStateWithMemoryAndCallees_callStack, h_cs] at hf
    cases hf

/-- **`tbl.toList`-free polymorphic syntactic `runCfgWithCallees` narrowing between opaque tables**
(discharged via `t₁.callConeClosedPoly`, which queries only `t₁.lookupRaw` and `t₁.traitImpls`). -/
theorem runCfgWithCallees_cone_narrow_of_callConeClosedPoly_wf (cone : List DefPath)
    (fuel : Nat) (body : CapturedMir) (args : List Value) (mem : Memory)
    {t₁ t₂ : OpaqueCalleeTable}
    (h₁ : MirLiftCore.CalleeInitWf body mem t₁.toList)
    (h₂ : MirLiftCore.CalleeInitWf body mem t₂.toList)
    (h_agree : OpaqueCalleeTable.AgreesOn cone t₁ t₂)
    (h_closed : t₁.callConeClosedPoly cone body body.traitImpls = true)
    (h_no₂ : ∀ dp, dp ∈ cone →
      hasTraitImplForDefPath (body.traitImpls ++ t₂.traitImpls) dp = false)
    (h_ac : mem.activeCallee = none) (h_cs : mem.callStack = []) :
    MirLiftCore.runCfgWithCallees fuel body args mem t₂.toList =
      (MirLiftCore.runCfgWithCallees fuel body args mem t₁.toList).map
        (MirLiftCore.MirOutcome.mapMem (MirLiftCore.Memory.withCallees t₂.toList)) := by
  unfold MirLiftCore.runCfgWithCallees
  rw [MirLiftCore.initMachineStateWithMemoryAndCallees_withCallees_of_wf body args mem h₁ h₂]
  refine MirLiftCore.runMirExecBounded_cone_narrow_poly cone body t₂.toList fuel _
    (coneReach_of_closedInvLookupPoly h_closed h_no₂ fuel _
      (closedInvLookupPoly_init_of_wf cone body args mem h₁ h_ac h_cs)) ?_
  intro s hs
  cases hs
  rw [MirLiftCore.initMachineStateWithMemoryAndCallees_callees_of_wf body args mem h₁]
  exact calleesAgreeOn_of_agreesOn h_agree

/-- **`tbl.toList`-free polymorphic syntactic `wpMirExecSym` narrowing between opaque tables.** -/
theorem wpMirExecSym_cone_narrow_of_callConeClosedPoly_wf (cone : List DefPath) (fuel : Nat)
    (body : CapturedMir) (args : List Value) (mem : Memory) {t₁ t₂ : OpaqueCalleeTable}
    (h₁ : MirLiftCore.CalleeInitWf body mem t₁.toList)
    (h₂ : MirLiftCore.CalleeInitWf body mem t₂.toList)
    (h_agree : OpaqueCalleeTable.AgreesOn cone t₁ t₂)
    (h_closed : t₁.callConeClosedPoly cone body body.traitImpls = true)
    (h_no₂ : ∀ dp, dp ∈ cone →
      hasTraitImplForDefPath (body.traitImpls ++ t₂.traitImpls) dp = false)
    (h_ac : mem.activeCallee = none) (h_cs : mem.callStack = [])
    (post : MirOutcome → Prop)
    (h_post : ∀ out,
      post (MirLiftCore.MirOutcome.mapMem (MirLiftCore.Memory.withCallees t₂.toList) out) ↔ post out) :
    Anneal.Rustc.V2026_06_01.SymbolicEval.wpMirExecSym fuel body
        (.running (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem
          t₂.toList)) post ↔
      Anneal.Rustc.V2026_06_01.SymbolicEval.wpMirExecSym fuel body
        (.running (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem
          t₁.toList)) post := by
  rw [MirLiftCore.initMachineStateWithMemoryAndCallees_withCallees_of_wf body args mem h₁ h₂]
  refine MirLiftCore.wpMirExecSym_cone_narrow_poly cone body t₂.toList post h_post fuel _
    (coneReach_of_closedInvLookupPoly h_closed h_no₂ fuel _
      (closedInvLookupPoly_init_of_wf cone body args mem h₁ h_ac h_cs)) ?_
  intro s hs
  cases hs
  rw [MirLiftCore.initMachineStateWithMemoryAndCallees_callees_of_wf body args mem h₁]
  exact calleesAgreeOn_of_agreesOn h_agree

/-- **`tbl.toList`-free polymorphic syntactic `MirWpConverges` narrowing between opaque tables.** -/
theorem mirWpConverges_cone_narrow_of_callConeClosedPoly_wf (cone : List DefPath)
    (body : CapturedMir) (args : List Value) (mem : Memory) {t₁ t₂ : OpaqueCalleeTable}
    (h₁ : MirLiftCore.CalleeInitWf body mem t₁.toList)
    (h₂ : MirLiftCore.CalleeInitWf body mem t₂.toList)
    (h_agree : OpaqueCalleeTable.AgreesOn cone t₁ t₂)
    (h_closed : t₁.callConeClosedPoly cone body body.traitImpls = true)
    (h_no₂ : ∀ dp, dp ∈ cone →
      hasTraitImplForDefPath (body.traitImpls ++ t₂.traitImpls) dp = false)
    (h_ac : mem.activeCallee = none) (h_cs : mem.callStack = [])
    (post : MirOutcome → Prop)
    (h_post : ∀ out,
      post (MirLiftCore.MirOutcome.mapMem (MirLiftCore.Memory.withCallees t₂.toList) out) ↔ post out) :
    MirFuelFree.MirWpConverges body
        (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem
          t₂.toList) post ↔
      MirFuelFree.MirWpConverges body
        (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem
          t₁.toList) post := by
  rw [MirLiftCore.initMachineStateWithMemoryAndCallees_withCallees_of_wf body args mem h₁ h₂]
  have h_at : MirLiftCore.AgreesAt cone t₂.toList
      (.running (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem
        t₁.toList)) := by
    intro s hs
    cases hs
    rw [MirLiftCore.initMachineStateWithMemoryAndCallees_callees_of_wf body args mem h₁]
    exact calleesAgreeOn_of_agreesOn h_agree
  constructor
  · rintro ⟨fuel, h⟩
    exact ⟨fuel,
      (MirLiftCore.wpMirExecSym_cone_narrow_poly cone body t₂.toList post h_post fuel _
        (coneReach_of_closedInvLookupPoly h_closed h_no₂ fuel _
          (closedInvLookupPoly_init_of_wf cone body args mem h₁ h_ac h_cs))
        h_at).1 h⟩
  · rintro ⟨fuel, h⟩
    exact ⟨fuel,
      (MirLiftCore.wpMirExecSym_cone_narrow_poly cone body t₂.toList post h_post fuel _
        (coneReach_of_closedInvLookupPoly h_closed h_no₂ fuel _
          (closedInvLookupPoly_init_of_wf cone body args mem h₁ h_ac h_cs))
        h_at).2 h⟩

end Anneal.OpaqueCalleeTable
