-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Trusted
import Anneal.Refinement
import Anneal.StepResult

/-!
# In-Place MIR Lowering and Backward Simulation

This module defines:
1. The inductive symbolic small-step execution relation `ExecNormal` over
   `Trusted.MirBody`.
2. The in-place CFG normalization pass `lowerBody : MirBody → MirBody`, which
   coalesces straight-line forwarding `goto` chains (`bb_i: { goto -> bb_j }`
   where `bb_j` is `{ stmts := [], terminator := .goto bb_k }`) while
   preserving `b.blocks.length`, `BlockId` numbering, and `storageLive` /
   `storageDead` statements.
3. The backward simulation theorem `lowerBody_simulates`, proving that
   `ExecNormal` on `lowerBody b` implies `ExecNormal` on the unlowered `b`.
-/

namespace Anneal

open Trusted

/-- Inductive normal-termination symbolic execution relation for a `MirBody`. -/
inductive ExecNormal (adts : List AdtDecl := []) (bodies : List BodyDecl := [])
    (body : MirBody) : MirState → (MirReturn → Prop) → Prop where
  | step {s s' : MirState} {P : MirReturn → Prop} :
      evalMirStep adts bodies body s = .silent s' →
      ExecNormal adts bodies body s' P →
      ExecNormal adts bodies body s P
  | normal {s : MirState} {v : MirReturn} {P : MirReturn → Prop} :
      evalMirStep adts bodies body s = .terminated (.normal v) →
      P v →
      ExecNormal adts bodies body s P

/-- Weaken the return predicate `P` of `ExecNormal`. -/
theorem ExecNormal.map {adts : List AdtDecl} {bodies : List BodyDecl}
    {body : MirBody} {s : MirState} {P Q : MirReturn → Prop}
    (himp : ∀ v, P v → Q v)
    (hexec : ExecNormal adts bodies body s P) :
    ExecNormal adts bodies body s Q := by
  induction hexec with
  | step hstep _ ih => exact .step hstep (ih himp)
  | normal hterm hp => exact .normal hterm (himp _ hp)

/-- Whether a terminator is a `.call1`. -/
def isCall1 (t : Terminator) : Bool :=
  match t with
  | .call1 _ _ _ _ _ => true
  | _ => false

theorem lookupAt_map {α β : Type} (f : α → β) :
    ∀ (xs : List α) (i : Nat),
      lookupAt (xs.map f) i = (lookupAt xs i).map f
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: xs, i + 1 => lookupAt_map f xs i

theorem list_length_map {α β : Type} (f : α → β) :
    ∀ (xs : List α), (xs.map f).length = xs.length
  | [] => rfl
  | _ :: xs => congrArg Nat.succ (list_length_map f xs)

/-- Coalesce a `.goto target` terminator across an empty forwarding block
`{ stmts := [], terminator := .goto target2 }`, provided `target.index <
blocks.length`. -/
noncomputable def lowerTerminator (blocks : List BasicBlock) :
    Terminator → Terminator
  | .goto target =>
    if decide (target.index < blocks.length) then
      match lookupAt blocks target.index with
      | some { stmts := [], terminator := .goto target2 } => .goto target2
      | _ => .goto target
    else
      .goto target
  | term => term

/-- Normalize a basic block in place. -/
noncomputable def lowerBlock (blocks : List BasicBlock)
    (bb : BasicBlock) : BasicBlock where
  stmts := bb.stmts
  terminator := lowerTerminator blocks bb.terminator

/-- Normalize a `MirBody` in place while preserving its signature, local count,
`BlockId` numbering (`(lowerBody b).blocks.length = b.blocks.length`), and
required constants. -/
noncomputable def lowerBody (b : MirBody) : MirBody where
  argTys := b.argTys
  retTy := b.retTy
  localCount := b.localCount
  blocks := b.blocks.map (lowerBlock b.blocks)
  requiredConsts := b.requiredConsts

theorem lowerBody_blocks_length (b : MirBody) :
    (lowerBody b).blocks.length = b.blocks.length :=
  list_length_map (lowerBlock b.blocks) b.blocks

theorem evalMirStmt_lowerBody (adts : List AdtDecl) (b : MirBody)
    (s : MirState) (stmt : Stmt) :
    evalMirStmt (lowerBody b) s stmt adts = evalMirStmt b s stmt adts := by
  cases stmt <;> rfl

theorem if_true_eq {α : Type} {P : Prop} [Decidable P] (hp : P) (a b : α) :
    (if P then a else b) = a := by
  cases ‹Decidable P› with
  | isFalse hnp => exact False.elim (hnp hp)
  | isTrue _ => rfl

theorem silent_of_if_failed {P : Prop} [Decidable P]
    {a : StepResult MirState Empty MirReturn} {s' : MirState}
    (h : (if P then a else .failed) = .silent s') :
    P ∧ a = .silent s' := by
  cases ‹Decidable P› with
  | isFalse _ => cases h
  | isTrue hp => exact ⟨hp, h⟩

theorem not_normal_of_if_failed {P : Prop} [Decidable P]
    {a : StepResult MirState Empty MirReturn} {v : MirReturn}
    (ha : a = .terminated (.normal v) → False) :
    (if P then a else .failed) = .terminated (.normal v) → False := by
  cases ‹Decidable P› with
  | isFalse _ => intro h; cases h
  | isTrue _ => exact ha

theorem not_normal_of_goto (adts : List AdtDecl) (bodies : List BodyDecl)
    (b : MirBody) (s : MirState) (target : BlockId) {v : MirReturn} :
    evalMirTerminator adts bodies b s (.goto target) =
      .terminated (.normal v) → False := by
  dsimp [evalMirTerminator, MirState.gotoBlock]
  exact not_normal_of_if_failed (fun h => by cases h)

theorem evalMirTerminator_eq_of_nocall (adts : List AdtDecl)
    (bodies : List BodyDecl) (b : MirBody) (s : MirState)
    (term : Terminator) (hnocall : isCall1 term = false) :
    evalMirTerminator adts bodies (lowerBody b) s term =
      evalMirTerminator adts bodies b s term := by
  cases term with
  | return_ => rfl
  | goto _ =>
    dsimp [evalMirTerminator, lowerBody]
    rw [list_length_map]
  | unreachable => rfl
  | panic => rfl
  | assert _ _ _ =>
    dsimp [evalMirTerminator, lowerBody]
    rw [list_length_map]
  | switchInt _ _ _ =>
    dsimp [evalMirTerminator, lowerBody]
    rw [list_length_map]
  | callSizeOf _ _ _ =>
    dsimp [evalMirTerminator, lowerBody]
    rw [list_length_map]
  | callTransmuteCopy _ _ _ _ _ =>
    dsimp [evalMirTerminator, lowerBody]
    rw [list_length_map]
  | call1 _ _ _ _ _ => cases hnocall
  | unsupported => rfl

theorem evalMirTerminator_lowerBody_normal (adts : List AdtDecl)
    (bodies : List BodyDecl) (b : MirBody) (s : MirState)
    (term : Terminator) {v : MirReturn}
    (hnocall : isCall1 term = false) :
    evalMirTerminator adts bodies (lowerBody b) s
        (lowerTerminator b.blocks term) = .terminated (.normal v) →
      evalMirTerminator adts bodies b s term = .terminated (.normal v) := by
  cases term with
  | goto target =>
    dsimp [lowerTerminator]
    cases decide (target.index < b.blocks.length) with
    | false =>
      dsimp
      exact fun h =>
        False.elim (not_normal_of_goto adts bodies (lowerBody b) s target h)
    | true =>
      dsimp
      cases lookupAt b.blocks target.index with
      | none =>
        dsimp
        exact fun h =>
          False.elim (not_normal_of_goto adts bodies (lowerBody b) s target h)
      | some bbT =>
        cases bbT with
        | mk stmtsT termT =>
          cases stmtsT with
          | nil =>
            cases termT <;> (
              dsimp
              exact fun h =>
                False.elim (not_normal_of_goto adts bodies (lowerBody b) s _ h))
          | cons _ _ =>
            dsimp
            exact fun h =>
              False.elim (not_normal_of_goto adts bodies (lowerBody b) s target h)
  | _ =>
    dsimp [lowerTerminator]
    rw [evalMirTerminator_eq_of_nocall adts bodies b s _ hnocall]
    exact fun h => h

theorem silent_inj {s₁ s₂ : MirState}
    (h : StepResult.silent (Obs := Empty) (Val := MirReturn) s₁ = .silent s₂) :
    s₁ = s₂ := by
  injection h with hfun
  have heq : (s₁ = s₁) = (s₁ = s₂) := congrFun hfun s₁
  exact heq ▸ rfl

theorem nextStmt_preserves_root {s s' : MirState}
    {locals' : Nat → Option MirVal} (hcur : s.curBody = none)
    (hstack : s.stack = []) (h : s.nextStmt locals' = .silent s') :
    s'.curBody = none ∧ s'.stack = [] := by
  cases silent_inj h
  exact ⟨hcur, hstack⟩

theorem nextStmtGen_preserves_root {s s' : MirState}
    {locals' : Nat → Option MirVal} {gens' : Nat → Nat}
    (hcur : s.curBody = none) (hstack : s.stack = [])
    (h : s.nextStmtGen locals' gens' = .silent s') :
    s'.curBody = none ∧ s'.stack = [] := by
  cases silent_inj h
  exact ⟨hcur, hstack⟩

theorem gotoBlock_preserves_root {s s' : MirState}
    {locals' : Nat → Option MirVal} {target : Nat}
    (hcur : s.curBody = none) (hstack : s.stack = [])
    (h : s.gotoBlock locals' target = .silent s') :
    s'.curBody = none ∧ s'.stack = [] := by
  cases silent_inj h
  exact ⟨hcur, hstack⟩

theorem evalMirStmt_preserves_root (adts : List AdtDecl) (b : MirBody)
    (s s' : MirState) (stmt : Stmt)
    (hcur : s.curBody = none) (hstack : s.stack = []) :
    evalMirStmt b s stmt adts = .silent s' →
      s'.curBody = none ∧ s'.stack = [] := by
  cases stmt with
  | assign dst rv =>
    cases rv with
    | use op =>
      dsimp [evalMirStmt]
      cases evalOperand b.localCount s op with
      | none => intro h; cases h
      | some p =>
        dsimp
        cases assignPlace b.localCount p.2 dst p.1 with
        | none => intro h; cases h
        | some _ => exact nextStmt_preserves_root hcur hstack
    | binaryOp op lhs rhs =>
      dsimp [evalMirStmt]
      cases evalOperand b.localCount s lhs with
      | none => intro h; cases h
      | some p1 =>
        dsimp
        cases evalOperand b.localCount { s with locals := p1.2 } rhs with
        | none => intro h; cases h
        | some p2 =>
          dsimp
          cases evalBinOp op p1.1 p2.1 with
          | none => intro h; cases h
          | some _ =>
            dsimp
            cases assignPlace b.localCount p2.2 dst _ with
            | none => intro h; cases h
            | some _ => exact nextStmt_preserves_root hcur hstack
    | aggregate adtId op =>
      dsimp [evalMirStmt]
      cases (findAdtDecl adts adtId).any (fun d => d.fields.length == 1) with
      | false => intro h; cases h
      | true =>
        dsimp
        cases evalOperand b.localCount s op with
        | none => intro h; cases h
        | some p =>
          dsimp
          cases assignPlace b.localCount p.2 dst (.adt adtId p.1) with
          | none => intro h; cases h
          | some _ => exact nextStmt_preserves_root hcur hstack
    | ref src =>
      dsimp [evalMirStmt]
      cases evalRefPlace b.localCount s src with
      | none => intro h; cases h
      | some refVal =>
        dsimp
        cases assignPlace b.localCount s.locals dst refVal with
        | none => intro h; cases h
        | some _ => exact nextStmt_preserves_root hcur hstack
    | unsupported => intro h; cases h
  | placeMention p =>
    dsimp [evalMirStmt]
    cases p.projection with
    | nil =>
      dsimp
      exact fun h => nextStmt_preserves_root hcur hstack (silent_of_if_failed h).2
    | cons _ _ =>
      dsimp
      cases evalPlace b.localCount s _ with
      | none => intro h; cases h
      | some _ => exact nextStmt_preserves_root hcur hstack
  | storageLive _ | storageDead _ =>
    dsimp [evalMirStmt]
    exact fun h => nextStmtGen_preserves_root hcur hstack (silent_of_if_failed h).2
  | nop =>
    dsimp [evalMirStmt]
    exact nextStmt_preserves_root hcur hstack
  | unsupported => intro h; cases h

theorem not_silent_of_if_failed {P : Prop} [Decidable P]
    {a : StepResult MirState Empty MirReturn} {s' : MirState}
    (ha : a = .silent s' → False) :
    (if P then a else .failed) = .silent s' → False := by
  cases ‹Decidable P› with
  | isFalse _ => intro h; cases h
  | isTrue _ => exact ha

theorem evalMirTerminator_preserves_root (adts : List AdtDecl)
    (bodies : List BodyDecl) (b : MirBody) (s s' : MirState)
    (term : Terminator) (hcur : s.curBody = none) (hstack : s.stack = [])
    (hnocall : isCall1 term = false) :
    evalMirTerminator adts bodies b s term = .silent s' →
      s'.curBody = none ∧ s'.stack = [] := by
  cases term with
  | return_ =>
    dsimp [evalMirTerminator]
    rw [hstack]
    refine fun h => False.elim (not_silent_of_if_failed ?_ h)
    cases s.locals 0 with
    | none => intro h1; cases h1
    | some _ =>
      dsimp
      exact not_silent_of_if_failed (fun h1 => by cases h1)
  | goto _ =>
    dsimp [evalMirTerminator]
    exact fun h => gotoBlock_preserves_root hcur hstack (silent_of_if_failed h).2
  | unreachable => intro h; cases h
  | panic => intro h; cases h
  | assert cond expected _ =>
    dsimp [evalMirTerminator]
    cases evalOperand b.localCount s cond with
    | none => intro h; cases h
    | some p =>
      cases p with
      | mk val _ =>
        cases val with
        | bool bval =>
          dsimp
          cases bval == expected with
          | false => intro h; cases h
          | true =>
            dsimp
            exact fun h =>
              gotoBlock_preserves_root hcur hstack (silent_of_if_failed h).2
        | _ => intro h; cases h
  | switchInt discr _ _ =>
    dsimp [evalMirTerminator]
    cases evalOperand b.localCount s discr with
    | none => intro h; cases h
    | some p =>
      cases p with
      | mk val _ =>
        cases val with
        | bool bval =>
          cases bval <;> (
            dsimp
            exact fun h =>
              gotoBlock_preserves_root hcur hstack (silent_of_if_failed h).2)
        | _ => intro h; cases h
  | callSizeOf dst ty _ =>
    dsimp [evalMirTerminator]
    intro h
    have h1 := (silent_of_if_failed h).2
    revert h1
    cases evalTyByteSize adts s.tySizes ty with
    | none => intro h1; cases h1
    | some sz =>
      dsimp
      cases assignPlace b.localCount s.locals dst (.usize sz) with
      | none => intro h1; cases h1
      | some _ => exact gotoBlock_preserves_root hcur hstack
  | callTransmuteCopy dst srcTy dstTy op _ =>
    dsimp [evalMirTerminator]
    intro h
    have h1 := (silent_of_if_failed h).2
    revert h1
    cases evalOperand b.localCount s op with
    | none => intro h1; cases h1
    | some p =>
      dsimp
      cases evalTransmuteCopy adts { s with locals := p.2 } srcTy dstTy p.1 with
      | none => intro h1; cases h1
      | some outVal =>
        dsimp
        cases assignPlace b.localCount p.2 dst outVal with
        | none => intro h1; cases h1
        | some _ => exact gotoBlock_preserves_root hcur hstack
  | call1 _ _ _ _ _ => cases hnocall
  | unsupported => intro h; cases h

theorem evalMirTerminator_lowerBody_silent (adts : List AdtDecl)
    (bodies : List BodyDecl) (b : MirBody) (s s' : MirState)
    (term : Terminator)
    (hcur : s.curBody = none)
    (hstack : s.stack = [])
    (hnocall : isCall1 term = false) :
    evalMirTerminator adts bodies (lowerBody b) s
        (lowerTerminator b.blocks term) = .silent s' →
      (s'.curBody = none ∧ s'.stack = []) ∧
      (evalMirTerminator adts bodies b s term = .silent s' ∨
       ∃ s₁,
         evalMirTerminator adts bodies b s term = .silent s₁ ∧
         evalMirStep adts bodies b s₁ = .silent s') := by
  cases term with
  | goto target =>
    dsimp [lowerTerminator]
    cases hdec : decide (target.index < b.blocks.length) with
    | false =>
      dsimp
      rw [evalMirTerminator_eq_of_nocall adts bodies b s (.goto target) rfl]
      exact fun h =>
        ⟨evalMirTerminator_preserves_root adts bodies b s s' (.goto target)
          hcur hstack rfl h, Or.inl h⟩
    | true =>
      dsimp
      have hlt : target.index < b.blocks.length := of_decide_eq_true hdec
      cases hlook : lookupAt b.blocks target.index with
      | none =>
        dsimp
        rw [evalMirTerminator_eq_of_nocall adts bodies b s (.goto target) rfl]
        exact fun h =>
          ⟨evalMirTerminator_preserves_root adts bodies b s s' (.goto target)
            hcur hstack rfl h, Or.inl h⟩
      | some bbTarget =>
        cases bbTarget with
        | mk stmtsT termT =>
          cases stmtsT with
          | nil =>
            cases termT with
            | goto target2 =>
              dsimp
              rw [evalMirTerminator_eq_of_nocall adts bodies b s (.goto target2) rfl]
              intro h
              have hpres := evalMirTerminator_preserves_root adts bodies b s s'
                (.goto target2) hcur hstack rfl h
              refine ⟨hpres,
                Or.inr ⟨{ s with block := target.index, stmtIdx := 0 }, ?_, ?_⟩⟩
              · dsimp [evalMirTerminator]
                exact if_true_eq hlt _ _
              · dsimp [evalMirStep]
                rw [hcur]
                dsimp [Option.getD]
                rw [hlook]
                dsimp [lookupAt, evalMirTerminator, MirState.gotoBlock]
                dsimp [evalMirTerminator, MirState.gotoBlock] at h
                rw [hcur] at h
                exact h
            | _ =>
              dsimp
              rw [evalMirTerminator_eq_of_nocall adts bodies b s (.goto target) rfl]
              exact fun h =>
                ⟨evalMirTerminator_preserves_root adts bodies b s s' (.goto target)
                  hcur hstack rfl h, Or.inl h⟩
          | cons _ _ =>
            dsimp
            rw [evalMirTerminator_eq_of_nocall adts bodies b s (.goto target) rfl]
            exact fun h =>
              ⟨evalMirTerminator_preserves_root adts bodies b s s' (.goto target)
                hcur hstack rfl h, Or.inl h⟩
  | _ =>
    dsimp [lowerTerminator]
    rw [evalMirTerminator_eq_of_nocall adts bodies b s _ hnocall]
    exact fun h =>
      ⟨evalMirTerminator_preserves_root adts bodies b s s' _ hcur hstack hnocall h,
       Or.inl h⟩

theorem noCall_of_all : ∀ {bbs : List BasicBlock},
    bbs.all (fun bb => !isCall1 bb.terminator) = true →
    ∀ {bb : BasicBlock}, bb ∈ bbs → isCall1 bb.terminator = false
  | b :: rest, h, bb, hmem => by
    have h' : ((!isCall1 b.terminator) &&
        rest.all (fun bb => !isCall1 bb.terminator)) = true := h
    cases hb : isCall1 b.terminator with
    | true => rw [hb] at h'; cases h'
    | false =>
      rw [hb] at h'
      cases hmem with
      | head => exact hb
      | tail _ hm => exact noCall_of_all h' hm

theorem lookupAt_mem {α : Type} :
    ∀ {xs : List α} {i : Nat} {x : α},
      lookupAt xs i = some x → x ∈ xs
  | x :: _, 0, _, h => by injection h with h'; subst h'; exact .head _
  | _ :: xs, i + 1, x, h => .tail _ (lookupAt_mem h)

theorem evalMirStep_lowerBody_normal (adts : List AdtDecl)
    (bodies : List BodyDecl) (b : MirBody) (s : MirState) {v : MirReturn}
    (hcalls : b.blocks.all (fun bb => !isCall1 bb.terminator) = true)
    (hcur : s.curBody = none) :
    evalMirStep adts bodies (lowerBody b) s = .terminated (.normal v) →
      evalMirStep adts bodies b s = .terminated (.normal v) := by
  dsimp [evalMirStep, lowerBody]
  rw [hcur]
  dsimp [Option.getD]
  rw [lookupAt_map]
  cases hbb : lookupAt b.blocks s.block with
  | none =>
    dsimp
    exact fun h => h
  | some bb =>
    dsimp [Option.map, lowerBlock]
    cases lookupAt bb.stmts s.stmtIdx with
    | some stmt =>
      dsimp
      exact fun h => h
    | none =>
      dsimp
      cases s.stmtIdx == bb.stmts.length with
      | false =>
        dsimp
        exact fun h => h
      | true =>
        dsimp
        exact evalMirTerminator_lowerBody_normal adts bodies b s bb.terminator
          (noCall_of_all hcalls (lookupAt_mem hbb))

/-- Backward simulation for `lowerBody`: any normal-termination execution of
`lowerBody b` on an intra-procedural body (`hcalls`) lifts to a
normal-termination execution of the unlowered body `b`. -/
theorem lowerBody_simulates {adts : List AdtDecl} {bodies : List BodyDecl}
    {b : MirBody} {s : MirState} {P : MirReturn → Prop}
    (hcalls : b.blocks.all (fun bb => !isCall1 bb.terminator) = true)
    (hcur : s.curBody = none := by rfl)
    (hstack : s.stack = [])
    (hexec : ExecNormal adts bodies (lowerBody b) s P) :
    ExecNormal adts bodies b s P := by
  induction hexec with
  | normal hterm hp =>
    exact .normal (evalMirStep_lowerBody_normal adts bodies b _ hcalls hcur hterm) hp
  | @step s s' P hstep _ ih =>
    revert hstep
    dsimp [evalMirStep, lowerBody]
    rw [hcur]
    dsimp [Option.getD]
    rw [lookupAt_map]
    cases hbb : lookupAt b.blocks s.block with
    | none =>
      intro hstep
      cases hstep
    | some bb =>
      dsimp [Option.map, lowerBlock]
      cases hstmt : lookupAt bb.stmts s.stmtIdx with
      | some stmt =>
        dsimp
        intro hstep
        have hpres := evalMirStmt_preserves_root adts b s s' stmt hcur hstack hstep
        have hstepB : evalMirStep adts bodies b s = .silent s' := by
          dsimp [evalMirStep]
          rw [hcur]
          dsimp [Option.getD]
          rw [hbb]
          dsimp
          rw [hstmt]
          exact hstep
        exact .step hstepB (ih hpres.1 hpres.2)
      | none =>
        dsimp
        cases hlen : s.stmtIdx == bb.stmts.length with
        | false =>
          intro hstep
          cases hstep
        | true =>
          dsimp
          intro hstep
          have hnocall : isCall1 bb.terminator = false :=
            noCall_of_all hcalls (lookupAt_mem hbb)
          have hsim := evalMirTerminator_lowerBody_silent adts bodies b s s'
            bb.terminator hcur hstack hnocall hstep
          have htermB :
              evalMirStep adts bodies b s =
                evalMirTerminator adts bodies b s bb.terminator := by
            dsimp [evalMirStep]
            rw [hcur]
            dsimp [Option.getD]
            rw [hbb]
            dsimp
            rw [hstmt]
            dsimp
            rw [hlen]
            rfl
          cases hsim.2 with
          | inl h1 =>
            rw [← htermB] at h1
            exact .step h1 (ih hsim.1.1 hsim.1.2)
          | inr h2 =>
            cases h2 with
            | intro s₁ hs₁ =>
              rw [← htermB] at hs₁
              exact .step hs₁.1 (.step hs₁.2 (ih hsim.1.1 hsim.1.2))

/-- Diamond CFG join helper: once two branch executions step to a shared join
state `sJoin`, a single suffix proof from `sJoin` discharges both branches. -/
theorem execNormal_join {adts : List AdtDecl} {bodies : List BodyDecl}
    {body : MirBody} {s sJoin : MirState} {P : MirReturn → Prop}
    (hstep : evalMirStep adts bodies body s = .silent sJoin)
    (hjoin : ExecNormal adts bodies body sJoin P) :
    ExecNormal adts bodies body s P :=
  .step hstep hjoin

/-- Canary: `lowerBody` coalesces a forwarding `goto` block (`bb0 -> bb1 -> bb2`)
into a direct jump (`bb0 -> bb2`), and `lowerBody_simulates` lifts the
shortened execution back to the unlowered body. -/
def gotoChainBody : MirBody where
  argTys := [.usize]
  retTy := .usize
  localCount := 2
  blocks := [
    { stmts := [.assign ⟨⟨0⟩, []⟩ (.use (.copy ⟨⟨1⟩, []⟩))]
      terminator := .goto ⟨1⟩ },
    { stmts := []
      terminator := .goto ⟨2⟩ },
    { stmts := []
      terminator := .return_ }
  ]

theorem canary_lowerBody_coalesces_goto_chain :
    (lowerBody gotoChainBody).blocks = [
      { stmts := [.assign ⟨⟨0⟩, []⟩ (.use (.copy ⟨⟨1⟩, []⟩))]
        terminator := .goto ⟨2⟩ },
      { stmts := []
        terminator := .goto ⟨2⟩ },
      { stmts := []
        terminator := .return_ }
    ] ∧
    let s0 : MirState := {
      locals := updateLocal (fun _ => none) 1 (some (.usize 42))
      block := 0
      stmtIdx := 0
    }
    ExecNormal [] [] gotoChainBody s0 (fun r => r.value = .usize 42) := by
  refine ⟨rfl, ?_⟩
  intro s0
  refine lowerBody_simulates rfl rfl rfl ?_
  exact .step rfl (.step rfl (.normal rfl rfl))

end Anneal
