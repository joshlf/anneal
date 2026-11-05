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
2. The computable in-place CFG normalization pass `lowerBody : MirBody → MirBody`,
   which first strips `Stmt.nop` statements from every basic block
   (`stripNopsBody`) and then iterates forwarding-`goto` coalescing to a fixed
   point (`coalesceGotosBody`) while preserving `b.blocks.length`, `BlockId`
   numbering, and `storageLive` / `storageDead` statements.
3. The backward simulation theorem `lowerBody_simulates`, proving that
   `ExecNormal` on `lowerBody b` implies `ExecNormal` on the unlowered `b`,
   together with entry-state equivalence (`initMirState_lowerBody_iff`).
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

/-- Whether a return predicate `P : MirReturn → Prop` is invariant under
replacing the terminal state's intra-block statement index `stmtIdx`. -/
def StmtIdxInvariant (P : MirReturn → Prop) : Prop :=
  ∀ val s idx, P ⟨val, s⟩ → P ⟨val, { s with stmtIdx := idx }⟩

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

theorem if_true_eq {α : Type} {P : Prop} [Decidable P] (hp : P) (a b : α) :
    (if P then a else b) = a := by
  cases ‹Decidable P› with
  | isFalse hnp => exact False.elim (hnp hp)
  | isTrue _ => rfl

theorem if_false_eq {α : Type} {P : Prop} [Decidable P] (hnp : ¬ P) (a b : α) :
    (if P then a else b) = b := by
  cases ‹Decidable P› with
  | isFalse _ => rfl
  | isTrue hp => exact False.elim (hnp hp)

theorem silent_of_if_failed {P : Prop} [Decidable P]
    {a : StepResult MirState Empty MirReturn} {s' : MirState}
    (h : (if P then a else .failed) = .silent s') :
    P ∧ a = .silent s' := by
  cases ‹Decidable P› with
  | isFalse _ => cases h
  | isTrue hp => exact ⟨hp, h⟩

theorem normal_of_if_failed {P : Prop} [Decidable P]
    {a : StepResult MirState Empty MirReturn} {v : MirReturn}
    (h : (if P then a else .failed) = .terminated (.normal v)) :
    P ∧ a = .terminated (.normal v) := by
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

theorem not_silent_of_if_failed {P : Prop} [Decidable P]
    {a : StepResult MirState Empty MirReturn} {s' : MirState}
    (ha : a = .silent s' → False) :
    (if P then a else .failed) = .silent s' → False := by
  cases ‹Decidable P› with
  | isFalse _ => intro h; cases h
  | isTrue _ => exact ha

theorem silent_inj {s₁ s₂ : MirState}
    (h : StepResult.silent (Obs := Empty) (Val := MirReturn) s₁ = .silent s₂) :
    s₁ = s₂ := by
  injection h with hfun
  have heq : (s₁ = s₁) = (s₁ = s₂) := congrFun hfun s₁
  exact heq ▸ rfl

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

theorem all_map_eq {α β : Type} (f : α → β) (p : β → Bool) (q : α → Bool)
    (hfg : ∀ x, p (f x) = q x) :
    ∀ (xs : List α), (xs.map f).all p = xs.all q
  | [] => rfl
  | x :: xs => by
    dsimp [List.map, List.all]
    rw [hfg x, all_map_eq f p q hfg xs]

theorem lookupAt_mem {α : Type} :
    ∀ {xs : List α} {i : Nat} {x : α},
      lookupAt xs i = some x → x ∈ xs
  | x :: _, 0, _, h => by injection h with h'; subst h'; exact .head _
  | _ :: xs, _ + 1, _, h => .tail _ (lookupAt_mem h)

/-!
## 1. Statement-Index Independence of Value Validity and Place Evaluation
-/

theorem resolveRef_with_stmtIdx (s : MirState) (idx frameId gen : Nat)
    (loc : LocalId) :
    resolveRef { s with stmtIdx := idx } frameId gen loc =
      resolveRef s frameId gen loc :=
  rfl

theorem validStep_with_stmtIdx (adts : List AdtDecl) (adtInv : AdtInv)
    (s : MirState) (idx callerBase : Nat)
    {unfold1 unfold2 : MirTy → MirVal → Prop}
    (hunf : ∀ ty v, unfold1 ty v ↔ unfold2 ty v) :
    ∀ (ty : MirTy) (v : MirVal),
      validStep adts adtInv { s with stmtIdx := idx } callerBase unfold1 ty v ↔
        validStep adts adtInv s callerBase unfold2 ty v
  | .usize, .usize _ => Iff.rfl
  | .usize, .uninit | .usize, .bool _ | .usize, .unit
  | .usize, .adt _ _ | .usize, .bytes _ _ | .usize, .ref _ _ _ => Iff.rfl
  | .bool, .bool _ => Iff.rfl
  | .bool, .uninit | .bool, .usize _ | .bool, .unit
  | .bool, .adt _ _ | .bool, .bytes _ _ | .bool, .ref _ _ _ => Iff.rfl
  | .unit, .unit => Iff.rfl
  | .unit, .uninit | .unit, .usize _ | .unit, .bool _
  | .unit, .adt _ _ | .unit, .bytes _ _ | .unit, .ref _ _ _ => Iff.rfl
  | .adt id, .adt _ inner => by
    dsimp [validStep]
    cases (findAdtDecl adts id).bind AdtDecl.payloadTy with
    | none => exact Iff.rfl
    | some payload =>
      exact ⟨fun ⟨h1, h2, h3⟩ => ⟨h1, h2, (hunf payload inner).mp h3⟩,
             fun ⟨h1, h2, h3⟩ => ⟨h1, h2, (hunf payload inner).mpr h3⟩⟩
  | .adt _, .uninit | .adt _, .usize _ | .adt _, .bool _
  | .adt _, .unit | .adt _, .bytes _ _ | .adt _, .ref _ _ _ => Iff.rfl
  | .param _, .bytes _ _ => Iff.rfl
  | .param _, .uninit | .param _, .usize _ | .param _, .bool _
  | .param _, .unit | .param _, .adt _ _ | .param _, .ref _ _ _ => Iff.rfl
  | .ref inner, .ref frameId gen loc => by
    dsimp [validStep]
    rw [resolveRef_with_stmtIdx]
    cases resolveRef s frameId gen loc with
    | none => exact Iff.rfl
    | some pointee =>
      have ih := validStep_with_stmtIdx adts adtInv s idx callerBase hunf
        inner pointee
      exact ⟨fun ⟨h1, h2, h3⟩ => ⟨h1, h2, ih.mp h3⟩,
             fun ⟨h1, h2, h3⟩ => ⟨h1, h2, ih.mpr h3⟩⟩
  | .ref _, .uninit | .ref _, .usize _ | .ref _, .bool _
  | .ref _, .unit | .ref _, .adt _ _ | .ref _, .bytes _ _ => Iff.rfl
  | .unsupported, _ => Iff.rfl

theorem validFuel_with_stmtIdx (adts : List AdtDecl) (adtInv : AdtInv)
    (s : MirState) (idx callerBase : Nat) :
    ∀ (fuel : Nat) (ty : MirTy) (v : MirVal),
      v.validFuel adts adtInv { s with stmtIdx := idx } callerBase fuel ty ↔
        v.validFuel adts adtInv s callerBase fuel ty
  | 0, _, _ => Iff.rfl
  | fuel + 1, ty, v =>
    validStep_with_stmtIdx adts adtInv s idx callerBase
      (validFuel_with_stmtIdx adts adtInv s idx callerBase fuel) ty v

theorem valid_with_stmtIdx (adts : List AdtDecl) (adtInv : AdtInv)
    (s : MirState) (idx callerBase : Nat) (ty : MirTy) (v : MirVal) :
    v.valid adts adtInv { s with stmtIdx := idx } callerBase ty ↔
      v.valid adts adtInv s callerBase ty :=
  validFuel_with_stmtIdx adts adtInv s idx callerBase (adts.length + 1) ty v

theorem stmtIdxInvariant_valid (adts : List AdtDecl) (adtInv : AdtInv)
    (callerBase : Nat) (ty : MirTy) :
    StmtIdxInvariant (fun r => r.value.valid adts adtInv r.state callerBase ty) :=
  fun val s idx h => (valid_with_stmtIdx adts adtInv s idx callerBase ty val).mpr h

theorem returnRefsStep_with_stmtIdx (s : MirState) (idx localCount : Nat)
    {follow1 follow2 : MirVal → Bool}
    (hf : ∀ v, follow1 v = follow2 v) :
    ∀ (v : MirVal),
      returnRefsStep { s with stmtIdx := idx } localCount follow1 v =
        returnRefsStep s localCount follow2 v
  | .uninit | .usize _ | .bool _ | .unit | .bytes _ _ => rfl
  | .adt _ inner => returnRefsStep_with_stmtIdx s idx localCount hf inner
  | .ref frameId gen loc => by
    dsimp [returnRefsStep]
    rw [resolveRef_with_stmtIdx]
    cases resolveRef s frameId gen loc with
    | none => rfl
    | some pointee =>
      dsimp [Option.any]
      rw [hf pointee]

theorem returnRefsFuel_with_stmtIdx (s : MirState) (idx localCount : Nat) :
    ∀ (fuel : Nat) (v : MirVal),
      returnRefsFuel { s with stmtIdx := idx } localCount fuel v =
        returnRefsFuel s localCount fuel v
  | 0, _ => rfl
  | fuel + 1, v =>
    returnRefsStep_with_stmtIdx s idx localCount
      (returnRefsFuel_with_stmtIdx s idx localCount fuel) v

theorem returnRefsOk_with_stmtIdx (s : MirState) (idx localCount : Nat)
    (v : MirVal) :
    v.returnRefsOk { s with stmtIdx := idx } localCount =
      v.returnRefsOk s localCount :=
  returnRefsFuel_with_stmtIdx s idx localCount 5 v

theorem evalProj_with_stmtIdx (s : MirState) (idx : Nat) :
    ∀ (proj : List PlaceElem) (v : MirVal),
      evalProj { s with stmtIdx := idx } proj v = evalProj s proj v
  | [], _ => rfl
  | .field 0 :: rest, .adt _ inner => evalProj_with_stmtIdx s idx rest inner
  | .field (_ + 1) :: _, _ => rfl
  | .field 0 :: _, .uninit | .field 0 :: _, .usize _ | .field 0 :: _, .bool _
  | .field 0 :: _, .unit | .field 0 :: _, .bytes _ _
  | .field 0 :: _, .ref _ _ _ => rfl
  | .deref :: rest, .ref frameId gen loc => by
    dsimp [evalProj]
    rw [resolveRef_with_stmtIdx]
    cases resolveRef s frameId gen loc with
    | none => rfl
    | some pointee => exact evalProj_with_stmtIdx s idx rest pointee
  | .deref :: _, .uninit | .deref :: _, .usize _ | .deref :: _, .bool _
  | .deref :: _, .unit | .deref :: _, .adt _ _
  | .deref :: _, .bytes _ _ => rfl
  | .unsupported :: _, _ => rfl

theorem evalPlace_with_stmtIdx (localCount : Nat) (s : MirState) (idx : Nat)
    (p : Place) :
    evalPlace localCount { s with stmtIdx := idx } p =
      evalPlace localCount s p := by
  dsimp [evalPlace]
  cases (inferInstance : Decidable (p.loc.index < localCount)) with
  | isFalse hnp => rw [if_false_eq hnp, if_false_eq hnp]
  | isTrue hp =>
    rw [if_true_eq hp, if_true_eq hp]
    cases s.locals p.loc.index with
    | none => rfl
    | some v => exact evalProj_with_stmtIdx s idx p.projection v

theorem evalRefProj_with_stmtIdx (s : MirState) (idx : Nat) :
    ∀ (frameId gen : Nat) (loc : LocalId) (proj : List PlaceElem) (v : MirVal),
      evalRefProj { s with stmtIdx := idx } frameId gen loc proj v =
        evalRefProj s frameId gen loc proj v
  | _, _, _, [], _ => rfl
  | _, _, _, .field _ :: _, _ => rfl
  | _, _, _, .unsupported :: _, _ => rfl
  | _, _, _, .deref :: rest, .ref frameId' gen' loc' => by
    dsimp [evalRefProj]
    rw [resolveRef_with_stmtIdx]
    cases resolveRef s frameId' gen' loc' with
    | none => rfl
    | some pointee =>
      exact evalRefProj_with_stmtIdx s idx frameId' gen' loc' rest pointee
  | _, _, _, .deref :: _, .uninit | _, _, _, .deref :: _, .usize _
  | _, _, _, .deref :: _, .bool _ | _, _, _, .deref :: _, .unit
  | _, _, _, .deref :: _, .adt _ _ | _, _, _, .deref :: _, .bytes _ _ => rfl

theorem evalRefPlace_with_stmtIdx (localCount : Nat) (s : MirState)
    (idx : Nat) (p : Place) :
    evalRefPlace localCount { s with stmtIdx := idx } p =
      evalRefPlace localCount s p := by
  dsimp [evalRefPlace]
  cases (inferInstance : Decidable (p.loc.index < localCount)) with
  | isFalse hnp => rw [if_false_eq hnp, if_false_eq hnp]
  | isTrue hp =>
    rw [if_true_eq hp, if_true_eq hp]
    cases s.locals p.loc.index with
    | none => rfl
    | some v =>
      exact evalRefProj_with_stmtIdx s idx s.frameId (s.localGens p.loc.index)
        p.loc p.projection v

theorem evalOperand_with_stmtIdx (localCount : Nat) (s : MirState) (idx : Nat)
    (op : Operand) :
    evalOperand localCount { s with stmtIdx := idx } op =
      evalOperand localCount s op := by
  cases op with
  | copy src =>
    dsimp [evalOperand]
    rw [evalPlace_with_stmtIdx]
  | move src =>
    dsimp [evalOperand]
    rw [evalPlace_with_stmtIdx]
  | constVal _ => rfl
  | unsupported => rfl

theorem evalTransmuteCopy_with_stmtIdx (adts : List AdtDecl) (s : MirState)
    (idx : Nat) (srcTy dstTy : MirTy) (argVal : MirVal) :
    evalTransmuteCopy adts { s with stmtIdx := idx } srcTy dstTy argVal =
      evalTransmuteCopy adts s srcTy dstTy argVal := by
  dsimp [evalTransmuteCopy]
  cases evalTyByteSize adts s.tySizes srcTy with
  | none => rfl
  | some srcSz =>
    cases evalTyByteSize adts s.tySizes dstTy with
    | none => rfl
    | some dstSz =>
      cases argVal <;> rfl

/-!
## 2. Pass 1: Stripping `Stmt.nop` (`stripNopsBody`) and Suffix Simulation
-/

/-- Whether a MIR statement is `Stmt.nop`. -/
def isNopStmt : Stmt → Bool
  | .nop => true
  | _ => false

/-- Computably remove all `Stmt.nop` statements from `stmts`. -/
def filterNops (stmts : List Stmt) : List Stmt :=
  stmts.foldr (fun x ih => if isNopStmt x then ih else x :: ih) []

/-- Strip `Stmt.nop` statements from a basic block. -/
def stripNopsBlock (bb : BasicBlock) : BasicBlock where
  stmts := filterNops bb.stmts
  terminator := bb.terminator

/-- Strip `Stmt.nop` statements from every basic block of `b`. -/
def stripNopsBody (b : MirBody) : MirBody where
  argTys := b.argTys
  retTy := b.retTy
  localCount := b.localCount
  blocks := b.blocks.map stripNopsBlock
  requiredConsts := b.requiredConsts

theorem stripNopsBody_blocks_length (b : MirBody) :
    (stripNopsBody b).blocks.length = b.blocks.length :=
  list_length_map stripNopsBlock b.blocks

theorem noCall_stripNopsBody (b : MirBody) :
    (stripNopsBody b).blocks.all (fun bb => !isCall1 bb.terminator) =
      b.blocks.all (fun bb => !isCall1 bb.terminator) :=
  all_map_eq stripNopsBlock (fun bb => !isCall1 bb.terminator)
    (fun bb => !isCall1 bb.terminator) (fun _ => rfl) b.blocks

/-- `IsSuffixAt xs idx rem` holds when dropping `idx` elements from `xs`
yields the suffix `rem`. -/
inductive IsSuffixAt {α : Type} : List α → Nat → List α → Prop where
  | zero (xs : List α) : IsSuffixAt xs 0 xs
  | succ {x : α} {xs ys : List α} {k : Nat} :
      IsSuffixAt xs k ys → IsSuffixAt (x :: xs) (k + 1) ys

theorem isSuffixAt_lookup_cons {α : Type} :
    ∀ {xs : List α} {k : Nat} {y : α} {ys : List α},
      IsSuffixAt xs k (y :: ys) →
      lookupAt xs k = some y ∧ IsSuffixAt xs (k + 1) ys
  | _ :: _, 0, _, ys, .zero _ => ⟨rfl, .succ (.zero ys)⟩
  | _ :: _, _ + 1, _, _, .succ h =>
    let ih := isSuffixAt_lookup_cons h
    ⟨ih.1, .succ ih.2⟩

theorem isSuffixAt_nil_eq_length {α : Type} :
    ∀ {xs : List α} {k : Nat},
      IsSuffixAt xs k [] →
      lookupAt xs k = none ∧ k = xs.length
  | [], 0, .zero _ => ⟨rfl, rfl⟩
  | _ :: _, _ + 1, .succ h =>
    let ih := isSuffixAt_nil_eq_length h
    ⟨ih.1, congrArg Nat.succ ih.2⟩

theorem isSuffixAt_nil_beq_length {α : Type} {xs : List α} {k : Nat}
    (h : IsSuffixAt xs k []) :
    lookupAt xs k = none ∧ (k == xs.length) = true := by
  have ⟨hlook, hlen⟩ := isSuffixAt_nil_eq_length h
  refine ⟨hlook, ?_⟩
  rw [hlen]
  exact decide_eq_true rfl

theorem isSuffixAt_zero_witness (bb : BasicBlock) :
    ∃ rem,
      IsSuffixAt bb.stmts 0 rem ∧
      IsSuffixAt (filterNops bb.stmts) 0 (filterNops rem) :=
  ⟨bb.stmts, .zero bb.stmts, .zero (filterNops bb.stmts)⟩

theorem nextStmt_with_stmtIdx {s s' : MirState} {locals' : Nat → Option MirVal}
    (idx : Nat) (h : s.nextStmt locals' = .silent s') :
    ({ s with stmtIdx := idx }).nextStmt locals' =
      .silent { s' with stmtIdx := idx + 1 } ∧
    s'.block = s.block ∧
    s'.stmtIdx = s.stmtIdx + 1 ∧
    s'.curBody = s.curBody ∧
    s'.stack = s.stack := by
  cases s
  cases silent_inj h
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem nextStmtGen_with_stmtIdx {s s' : MirState}
    {locals' : Nat → Option MirVal} {gens' : Nat → Nat}
    (idx : Nat) (h : s.nextStmtGen locals' gens' = .silent s') :
    ({ s with stmtIdx := idx }).nextStmtGen locals' gens' =
      .silent { s' with stmtIdx := idx + 1 } ∧
    s'.block = s.block ∧
    s'.stmtIdx = s.stmtIdx + 1 ∧
    s'.curBody = s.curBody ∧
    s'.stack = s.stack := by
  cases s
  cases silent_inj h
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem gotoBlock_with_stmtIdx {s s' : MirState}
    {locals' : Nat → Option MirVal} {target : Nat}
    (idx : Nat) (h : s.gotoBlock locals' target = .silent s') :
    ({ s with stmtIdx := idx }).gotoBlock locals' target = .silent s' ∧
    s'.stmtIdx = 0 ∧
    s'.curBody = s.curBody ∧
    s'.stack = s.stack := by
  cases s
  cases silent_inj h
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem evalMirStmt_not_normal (adts : List AdtDecl) (b : MirBody)
    (s : MirState) (stmt : Stmt) {v : MirReturn} :
    evalMirStmt b s stmt adts = .terminated (.normal v) → False := by
  cases stmt with
  | assign dst rv =>
    cases rv with
    | use op =>
      dsimp [evalMirStmt]
      cases evalOperand b.localCount s op with
      | none => intro h; cases h
      | some p =>
        dsimp
        cases assignPlace b.localCount p.2 dst p.1 <;>
          (cases s; intro h; cases h)
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
            cases assignPlace b.localCount p2.2 dst _ <;>
              (cases s; intro h; cases h)
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
          cases assignPlace b.localCount p.2 dst (.adt adtId p.1) <;>
            (cases s; intro h; cases h)
    | ref src =>
      dsimp [evalMirStmt]
      cases evalRefPlace b.localCount s src with
      | none => intro h; cases h
      | some refVal =>
        dsimp
        cases assignPlace b.localCount s.locals dst refVal <;>
          (cases s; intro h; cases h)
    | unsupported => intro h; cases h
  | placeMention p =>
    dsimp [evalMirStmt]
    cases p.projection with
    | nil =>
      dsimp
      exact not_normal_of_if_failed (by cases s; intro h; cases h)
    | cons _ _ =>
      dsimp
      cases evalPlace b.localCount s _ <;> (cases s; intro h; cases h)
  | storageLive _ | storageDead _ =>
    dsimp [evalMirStmt]
    exact not_normal_of_if_failed (by cases s; intro h; cases h)
  | nop => cases s; intro h; cases h
  | unsupported => intro h; cases h

theorem evalMirStmt_with_stmtIdx_silent (adts : List AdtDecl)
    (b₁ b₂ : MirBody) (s s' : MirState) (idx : Nat) (stmt : Stmt)
    (hlc : b₁.localCount = b₂.localCount) :
    evalMirStmt b₁ s stmt adts = .silent s' →
      evalMirStmt b₂ { s with stmtIdx := idx } stmt adts =
        .silent { s' with stmtIdx := idx + 1 } ∧
      s'.block = s.block ∧
      s'.stmtIdx = s.stmtIdx + 1 ∧
      s'.curBody = s.curBody ∧
      s'.stack = s.stack := by
  cases s with
  | mk locals localGens block stmtIdx tySizes curBody stack frameId nextFrameId =>
  let s : MirState :=
    ⟨locals, localGens, block, stmtIdx, tySizes, curBody, stack, frameId, nextFrameId⟩
  cases stmt with
  | assign dst rv =>
    cases rv with
    | use op =>
      dsimp [evalMirStmt]
      rw [← hlc, evalOperand_with_stmtIdx b₁.localCount s idx op]
      cases evalOperand b₁.localCount s op with
      | none => intro h; cases h
      | some p =>
        dsimp
        cases assignPlace b₁.localCount p.2 dst p.1 with
        | none => intro h; cases h
        | some _ => exact nextStmt_with_stmtIdx idx
    | binaryOp op lhs rhs =>
      dsimp [evalMirStmt]
      rw [← hlc, evalOperand_with_stmtIdx b₁.localCount s idx lhs]
      cases evalOperand b₁.localCount s lhs with
      | none => intro h; cases h
      | some p1 =>
        dsimp
        rw [evalOperand_with_stmtIdx b₁.localCount { s with locals := p1.2 } idx rhs]
        cases evalOperand b₁.localCount { s with locals := p1.2 } rhs with
        | none => intro h; cases h
        | some p2 =>
          dsimp
          cases evalBinOp op p1.1 p2.1 with
          | none => intro h; cases h
          | some _ =>
            dsimp
            cases assignPlace b₁.localCount p2.2 dst _ with
            | none => intro h; cases h
            | some _ => exact nextStmt_with_stmtIdx idx
    | aggregate adtId op =>
      dsimp [evalMirStmt]
      rw [← hlc, evalOperand_with_stmtIdx b₁.localCount s idx op]
      cases (findAdtDecl adts adtId).any (fun d => d.fields.length == 1) with
      | false => intro h; cases h
      | true =>
        dsimp
        cases evalOperand b₁.localCount s op with
        | none => intro h; cases h
        | some p =>
          dsimp
          cases assignPlace b₁.localCount p.2 dst (.adt adtId p.1) with
          | none => intro h; cases h
          | some _ => exact nextStmt_with_stmtIdx idx
    | ref src =>
      dsimp [evalMirStmt]
      rw [← hlc, evalRefPlace_with_stmtIdx b₁.localCount s idx src]
      cases evalRefPlace b₁.localCount s src with
      | none => intro h; cases h
      | some refVal =>
        dsimp
        cases assignPlace b₁.localCount s.locals dst refVal with
        | none => intro h; cases h
        | some _ => exact nextStmt_with_stmtIdx idx
    | unsupported => intro h; cases h
  | placeMention p =>
    dsimp [evalMirStmt]
    rw [← hlc]
    cases p.projection with
    | nil =>
      dsimp
      intro h
      have ⟨hlt, hs⟩ := silent_of_if_failed h
      rw [if_true_eq hlt]
      exact nextStmt_with_stmtIdx idx hs
    | cons _ _ =>
      dsimp
      rw [evalPlace_with_stmtIdx b₁.localCount s idx p]
      cases evalPlace b₁.localCount s p with
      | none => intro h; cases h
      | some _ => exact nextStmt_with_stmtIdx idx
  | storageLive _ | storageDead _ =>
    dsimp [evalMirStmt]
    rw [← hlc]
    intro h
    have ⟨hlt, hs⟩ := silent_of_if_failed h
    rw [if_true_eq hlt]
    exact nextStmtGen_with_stmtIdx idx hs
  | nop =>
    dsimp [evalMirStmt]
    exact nextStmt_with_stmtIdx idx
  | unsupported => intro h; cases h

theorem evalMirTerminator_with_stmtIdx_normal (adts : List AdtDecl)
    (bodies : List BodyDecl) (b₁ b₂ : MirBody) (s : MirState)
    (idx : Nat) (term : Terminator) {v : MirReturn}
    (hlc : b₁.localCount = b₂.localCount)
    (hstack : s.stack = [])
    (hnocall : isCall1 term = false)
    (hP : StmtIdxInvariant P)
    (hp : P v) :
    evalMirTerminator adts bodies b₁ s term = .terminated (.normal v) →
      ∃ v',
        evalMirTerminator adts bodies b₂ { s with stmtIdx := idx } term =
          .terminated (.normal v') ∧ P v' := by
  cases s with
  | mk locals localGens block stmtIdx tySizes curBody stack frameId nextFrameId =>
  dsimp at hstack
  subst hstack
  let s : MirState :=
    ⟨locals, localGens, block, stmtIdx, tySizes, curBody, [], frameId, nextFrameId⟩
  cases term with
  | return_ =>
    dsimp [evalMirTerminator]
    rw [← hlc]
    intro h
    have ⟨hlt, h1⟩ := normal_of_if_failed h
    rw [if_true_eq hlt]
    revert h1
    cases locals 0 with
    | none => intro h1; cases h1
    | some retVal =>
      dsimp
      rw [returnRefsOk_with_stmtIdx s idx b₁.localCount retVal]
      intro h1
      have ⟨hcond, h2⟩ := normal_of_if_failed h1
      rw [if_true_eq hcond]
      injection h2 with h3
      injection h3 with hv
      subst hv
      exact ⟨⟨retVal, { s with stmtIdx := idx }⟩, rfl, hP retVal s idx hp⟩
  | goto _ =>
    dsimp [evalMirTerminator]
    exact fun h =>
      False.elim (not_normal_of_if_failed (fun h1 => by cases h1) h)
  | unreachable => intro h; cases h
  | panic => intro h; cases h
  | assert cond expected _ =>
    dsimp [evalMirTerminator]
    cases evalOperand b₁.localCount s cond with
    | none => intro h; cases h
    | some p =>
      cases p with
      | mk pval plocals =>
        cases pval with
        | bool bval =>
          dsimp
          cases bval == expected with
          | false => intro h; cases h
          | true =>
            dsimp
            exact fun h =>
              False.elim (not_normal_of_if_failed (fun h1 => by cases h1) h)
        | _ => intro h; cases h
  | switchInt discr _ _ =>
    dsimp [evalMirTerminator]
    cases evalOperand b₁.localCount s discr with
    | none => intro h; cases h
    | some p =>
      cases p with
      | mk pval plocals =>
        cases pval with
        | bool bval =>
          cases bval <;> (
            dsimp
            exact fun h =>
              False.elim (not_normal_of_if_failed (fun h1 => by cases h1) h))
        | _ => intro h; cases h
  | callSizeOf dst ty _ =>
    dsimp [evalMirTerminator]
    refine fun h => False.elim (not_normal_of_if_failed ?_ h)
    cases evalTyByteSize adts tySizes ty with
    | none => intro h1; cases h1
    | some sz =>
      dsimp
      cases assignPlace b₁.localCount locals dst (.usize sz) <;>
        (intro h1; cases h1)
  | callTransmuteCopy dst srcTy dstTy op _ =>
    dsimp [evalMirTerminator]
    refine fun h => False.elim (not_normal_of_if_failed ?_ h)
    cases evalOperand b₁.localCount s op with
    | none => intro h1; cases h1
    | some p =>
      dsimp
      cases evalTransmuteCopy adts { s with locals := p.2 } srcTy dstTy p.1 with
      | none => intro h1; cases h1
      | some outVal =>
        dsimp
        cases assignPlace b₁.localCount p.2 dst outVal <;>
          (intro h1; cases h1)
  | call1 _ _ _ _ _ => cases hnocall
  | unsupported => intro h; cases h

theorem evalMirTerminator_with_stmtIdx_silent (adts : List AdtDecl)
    (bodies : List BodyDecl) (b₁ b₂ : MirBody) (s s' : MirState)
    (idx : Nat) (term : Terminator)
    (hlc : b₁.localCount = b₂.localCount)
    (hlen : b₁.blocks.length = b₂.blocks.length)
    (hcur : s.curBody = none)
    (hstack : s.stack = [])
    (hnocall : isCall1 term = false) :
    evalMirTerminator adts bodies b₁ s term = .silent s' →
      evalMirTerminator adts bodies b₂ { s with stmtIdx := idx } term =
        .silent s' ∧
      s'.stmtIdx = 0 ∧
      s'.curBody = none ∧
      s'.stack = [] := by
  cases s with
  | mk locals localGens block stmtIdx tySizes curBody stack frameId nextFrameId =>
  let s : MirState :=
    ⟨locals, localGens, block, stmtIdx, tySizes, curBody, stack, frameId, nextFrameId⟩
  dsimp at hcur hstack
  cases term with
  | return_ =>
    dsimp [evalMirTerminator]
    rw [hstack]
    refine fun h => False.elim (not_silent_of_if_failed ?_ h)
    cases locals 0 with
    | none => intro h1; cases h1
    | some _ =>
      dsimp
      exact not_silent_of_if_failed (fun h1 => by cases h1)
  | goto target =>
    dsimp [evalMirTerminator]
    rw [← hlen]
    intro h
    have ⟨hlt, hs⟩ := silent_of_if_failed h
    rw [if_true_eq hlt]
    have hg := gotoBlock_with_stmtIdx idx hs
    exact ⟨hg.1, hg.2.1, hg.2.2.1.trans hcur, hg.2.2.2.trans hstack⟩
  | unreachable => intro h; cases h
  | panic => intro h; cases h
  | assert cond expected target =>
    dsimp [evalMirTerminator]
    rw [← hlc, ← hlen, evalOperand_with_stmtIdx b₁.localCount s idx cond]
    cases evalOperand b₁.localCount s cond with
    | none => intro h; cases h
    | some p =>
      cases p with
      | mk pval plocals =>
        cases pval with
        | bool bval =>
          dsimp
          cases bval == expected with
          | false => intro h; cases h
          | true =>
            dsimp
            intro h
            have ⟨hlt, hs⟩ := silent_of_if_failed h
            rw [if_true_eq hlt]
            have hg := gotoBlock_with_stmtIdx idx hs
            exact ⟨hg.1, hg.2.1, hg.2.2.1.trans hcur, hg.2.2.2.trans hstack⟩
        | _ => intro h; cases h
  | switchInt discr fTarget tTarget =>
    dsimp [evalMirTerminator]
    rw [← hlc, ← hlen, evalOperand_with_stmtIdx b₁.localCount s idx discr]
    cases evalOperand b₁.localCount s discr with
    | none => intro h; cases h
    | some p =>
      cases p with
      | mk pval plocals =>
        cases pval with
        | bool bval =>
          cases bval <;> (
            dsimp
            intro h
            have ⟨hlt, hs⟩ := silent_of_if_failed h
            rw [if_true_eq hlt]
            have hg := gotoBlock_with_stmtIdx idx hs
            exact ⟨hg.1, hg.2.1, hg.2.2.1.trans hcur, hg.2.2.2.trans hstack⟩)
        | _ => intro h; cases h
  | callSizeOf dst ty target =>
    dsimp [evalMirTerminator]
    rw [← hlc, ← hlen]
    intro h
    have ⟨hlt, h1⟩ := silent_of_if_failed h
    rw [if_true_eq hlt]
    revert h1
    cases evalTyByteSize adts tySizes ty with
    | none => intro h1; cases h1
    | some sz =>
      dsimp
      cases assignPlace b₁.localCount locals dst (.usize sz) with
      | none => intro h1; cases h1
      | some _ =>
        intro hs
        have hg := gotoBlock_with_stmtIdx idx hs
        exact ⟨hg.1, hg.2.1, hg.2.2.1.trans hcur, hg.2.2.2.trans hstack⟩
  | callTransmuteCopy dst srcTy dstTy op target =>
    dsimp [evalMirTerminator]
    rw [← hlc, ← hlen, evalOperand_with_stmtIdx b₁.localCount s idx op]
    intro h
    have ⟨hlt, h1⟩ := silent_of_if_failed h
    rw [if_true_eq hlt]
    revert h1
    cases evalOperand b₁.localCount s op with
    | none => intro h1; cases h1
    | some p =>
      dsimp
      rw [evalTransmuteCopy_with_stmtIdx adts { s with locals := p.2 } idx srcTy dstTy p.1]
      cases evalTransmuteCopy adts { s with locals := p.2 } srcTy dstTy p.1 with
      | none => intro h1; cases h1
      | some outVal =>
        dsimp
        cases assignPlace b₁.localCount p.2 dst outVal with
        | none => intro h1; cases h1
        | some _ =>
          intro hs
          have hg := gotoBlock_with_stmtIdx idx hs
          exact ⟨hg.1, hg.2.1, hg.2.2.1.trans hcur, hg.2.2.2.trans hstack⟩
  | call1 _ _ _ _ _ => cases hnocall
  | unsupported => intro h; cases h

theorem evalMirStep_at_block {adts : List AdtDecl} {bodies : List BodyDecl}
    {b : MirBody} {bb : BasicBlock} {s : MirState}
    (hcur : s.curBody = none)
    (hbb : lookupAt b.blocks s.block = some bb) :
    evalMirStep adts bodies b s =
      match lookupAt bb.stmts s.stmtIdx with
      | some stmt => evalMirStmt b s stmt adts
      | none =>
        if s.stmtIdx == bb.stmts.length then
          evalMirTerminator adts bodies b s bb.terminator
        else
          .failed := by
  dsimp [evalMirStep]
  cases hs : s.curBody with
  | none =>
    dsimp [Option.getD]
    rw [hbb]
    rfl
  | some _ =>
    rw [hcur] at hs
    cases hs

theorem evalMirStep_at_block_idx {adts : List AdtDecl} {bodies : List BodyDecl}
    {b : MirBody} {bb : BasicBlock} {s : MirState} (idx : Nat)
    (hcur : s.curBody = none)
    (hbb : lookupAt b.blocks s.block = some bb) :
    evalMirStep adts bodies b { s with stmtIdx := idx } =
      match lookupAt bb.stmts idx with
      | some stmt => evalMirStmt b { s with stmtIdx := idx } stmt adts
      | none =>
        if idx == bb.stmts.length then
          evalMirTerminator adts bodies b { s with stmtIdx := idx }
            bb.terminator
        else
          .failed :=
  evalMirStep_at_block (s := { s with stmtIdx := idx }) hcur hbb

theorem step_nop_at {adts : List AdtDecl} {bodies : List BodyDecl}
    {b : MirBody} {bb : BasicBlock} {s : MirState} {k : Nat}
    (hcur : s.curBody = none)
    (hbb : lookupAt b.blocks s.block = some bb)
    (hlook : lookupAt bb.stmts k = some .nop) :
    evalMirStep adts bodies b { s with stmtIdx := k } =
      .silent { s with stmtIdx := k + 1 } := by
  rw [evalMirStep_at_block_idx k hcur hbb, hlook]
  cases s
  rfl

theorem stripNops_normal_suffix {adts : List AdtDecl} {bodies : List BodyDecl}
    {b : MirBody} {bb : BasicBlock} {s : MirState} {v : MirReturn}
    {P : MirReturn → Prop}
    (hcalls : b.blocks.all (fun bb => !isCall1 bb.terminator) = true)
    (hP : StmtIdxInvariant P)
    (hp : P v)
    (hcur : s.curBody = none)
    (hstack : s.stack = [])
    (hbb : lookupAt b.blocks s.block = some bb)
    (hterm : evalMirStep adts bodies (stripNopsBody b) s = .terminated (.normal v)) :
    ∀ (rem : List Stmt) (k_orig : Nat),
      IsSuffixAt bb.stmts k_orig rem →
      IsSuffixAt (filterNops bb.stmts) s.stmtIdx (filterNops rem) →
      ExecNormal adts bodies b { s with stmtIdx := k_orig } P
  | [], k_orig, hOrig, hLow => by
    have ⟨hlookLow, _⟩ := isSuffixAt_nil_beq_length hLow
    have ⟨hlookOrig, hlenOrig⟩ := isSuffixAt_nil_beq_length hOrig
    have hbbLow :
        lookupAt (stripNopsBody b).blocks s.block =
          some (stripNopsBlock bb) := by
      dsimp [stripNopsBody]
      rw [lookupAt_map, hbb]
      rfl
    have hterm' :
        evalMirTerminator adts bodies (stripNopsBody b) s bb.terminator =
          .terminated (.normal v) := by
      rw [evalMirStep_at_block hcur hbbLow] at hterm
      dsimp [stripNopsBlock] at hterm
      rw [hlookLow] at hterm
      dsimp at hterm
      exact (normal_of_if_failed hterm).2
    have hnocall : isCall1 bb.terminator = false :=
      noCall_of_all hcalls (lookupAt_mem hbb)
    cases evalMirTerminator_with_stmtIdx_normal adts bodies (stripNopsBody b) b
        s k_orig bb.terminator rfl hstack hnocall hP hp hterm' with
    | intro v' hv' =>
      refine .normal ?_ hv'.2
      rw [evalMirStep_at_block_idx k_orig hcur hbb, hlookOrig]
      dsimp
      rw [if_true_eq hlenOrig]
      exact hv'.1
  | x :: rem, k_orig, hOrig, hLow => by
    have ⟨hlookOrig, hOrig'⟩ := isSuffixAt_lookup_cons hOrig
    cases hx : isNopStmt x with
    | true =>
      have hxNop : x = .nop := by cases x <;> first | rfl | cases hx
      subst hxNop
      have hLow' : IsSuffixAt (filterNops bb.stmts) s.stmtIdx (filterNops rem) :=
        hLow
      exact .step (step_nop_at hcur hbb hlookOrig)
        (stripNops_normal_suffix hcalls hP hp hcur hstack hbb hterm
          rem (k_orig + 1) hOrig' hLow')
    | false =>
      have hLowCons :
          IsSuffixAt (filterNops bb.stmts) s.stmtIdx (x :: filterNops rem) := by
        change IsSuffixAt (filterNops bb.stmts) s.stmtIdx
          (if isNopStmt x then filterNops rem else x :: filterNops rem) at hLow
        rw [hx] at hLow
        exact hLow
      have ⟨hlookLow, _⟩ := isSuffixAt_lookup_cons hLowCons
      have hbbLow :
          lookupAt (stripNopsBody b).blocks s.block =
            some (stripNopsBlock bb) := by
        dsimp [stripNopsBody]
        rw [lookupAt_map, hbb]
        rfl
      have hstmtTerm :
          evalMirStmt (stripNopsBody b) s x adts = .terminated (.normal v) := by
        rw [evalMirStep_at_block hcur hbbLow] at hterm
        dsimp [stripNopsBlock] at hterm
        rw [hlookLow] at hterm
        exact hterm
      exact False.elim
        (evalMirStmt_not_normal adts (stripNopsBody b) s x hstmtTerm)

theorem stripNops_step_suffix {adts : List AdtDecl} {bodies : List BodyDecl}
    {b : MirBody} {bb : BasicBlock} {s s' : MirState}
    {P : MirReturn → Prop}
    (hcalls : b.blocks.all (fun bb => !isCall1 bb.terminator) = true)
    (hcur : s.curBody = none)
    (hstack : s.stack = [])
    (hbb : lookupAt b.blocks s.block = some bb)
    (hstep : evalMirStep adts bodies (stripNopsBody b) s = .silent s')
    (ih : ∀ (k' : Nat),
      s'.curBody = none →
      s'.stack = [] →
      (∀ bb', lookupAt b.blocks s'.block = some bb' →
        ∃ rem',
          IsSuffixAt bb'.stmts k' rem' ∧
          IsSuffixAt (filterNops bb'.stmts) s'.stmtIdx (filterNops rem')) →
      ExecNormal adts bodies b { s' with stmtIdx := k' } P) :
    ∀ (rem : List Stmt) (k_orig : Nat),
      IsSuffixAt bb.stmts k_orig rem →
      IsSuffixAt (filterNops bb.stmts) s.stmtIdx (filterNops rem) →
      ExecNormal adts bodies b { s with stmtIdx := k_orig } P
  | [], k_orig, hOrig, hLow => by
    have ⟨hlookLow, _⟩ := isSuffixAt_nil_beq_length hLow
    have ⟨hlookOrig, hlenOrig⟩ := isSuffixAt_nil_beq_length hOrig
    have hbbLow :
        lookupAt (stripNopsBody b).blocks s.block =
          some (stripNopsBlock bb) := by
      dsimp [stripNopsBody]
      rw [lookupAt_map, hbb]
      rfl
    have htermStep :
        evalMirTerminator adts bodies (stripNopsBody b) s bb.terminator =
          .silent s' := by
      rw [evalMirStep_at_block hcur hbbLow] at hstep
      dsimp [stripNopsBlock] at hstep
      rw [hlookLow] at hstep
      dsimp at hstep
      exact (silent_of_if_failed hstep).2
    have hnocall : isCall1 bb.terminator = false :=
      noCall_of_all hcalls (lookupAt_mem hbb)
    have ⟨htermOrig, hs'Idx, hs'Cur, hs'Stack⟩ :=
      evalMirTerminator_with_stmtIdx_silent adts bodies (stripNopsBody b) b
        s s' k_orig bb.terminator rfl (stripNopsBody_blocks_length b)
        hcur hstack hnocall htermStep
    have hs'Eq : { s' with stmtIdx := 0 } = s' := by
      cases s'
      dsimp at hs'Idx
      subst hs'Idx
      rfl
    have hstepOrig :
        evalMirStep adts bodies b { s with stmtIdx := k_orig } = .silent s' := by
      rw [evalMirStep_at_block_idx k_orig hcur hbb, hlookOrig]
      dsimp
      rw [if_true_eq hlenOrig]
      exact htermOrig
    have hNext : ExecNormal adts bodies b { s' with stmtIdx := 0 } P :=
      ih 0 hs'Cur hs'Stack (fun bb' _ => by
        rw [hs'Idx]
        exact isSuffixAt_zero_witness bb')
    rw [hs'Eq] at hNext
    exact .step hstepOrig hNext
  | x :: rem, k_orig, hOrig, hLow => by
    have ⟨hlookOrig, hOrig'⟩ := isSuffixAt_lookup_cons hOrig
    cases hx : isNopStmt x with
    | true =>
      have hxNop : x = .nop := by cases x <;> first | rfl | cases hx
      subst hxNop
      have hLow' : IsSuffixAt (filterNops bb.stmts) s.stmtIdx (filterNops rem) :=
        hLow
      exact .step (step_nop_at hcur hbb hlookOrig)
        (stripNops_step_suffix hcalls hcur hstack hbb hstep ih
          rem (k_orig + 1) hOrig' hLow')
    | false =>
      have hLowCons :
          IsSuffixAt (filterNops bb.stmts) s.stmtIdx (x :: filterNops rem) := by
        change IsSuffixAt (filterNops bb.stmts) s.stmtIdx
          (if isNopStmt x then filterNops rem else x :: filterNops rem) at hLow
        rw [hx] at hLow
        exact hLow
      have ⟨hlookLow, hLow'⟩ := isSuffixAt_lookup_cons hLowCons
      have hbbLow :
          lookupAt (stripNopsBody b).blocks s.block =
            some (stripNopsBlock bb) := by
        dsimp [stripNopsBody]
        rw [lookupAt_map, hbb]
        rfl
      have hstmtStep :
          evalMirStmt (stripNopsBody b) s x adts = .silent s' := by
        rw [evalMirStep_at_block hcur hbbLow] at hstep
        dsimp [stripNopsBlock] at hstep
        rw [hlookLow] at hstep
        exact hstep
      have ⟨hstmtOrig, hs'Blk, hs'Idx, hs'Cur, hs'Stack⟩ :=
        evalMirStmt_with_stmtIdx_silent adts (stripNopsBody b) b s s'
          k_orig x rfl hstmtStep
      have hstepOrig :
          evalMirStep adts bodies b { s with stmtIdx := k_orig } =
            .silent { s' with stmtIdx := k_orig + 1 } := by
        rw [evalMirStep_at_block_idx k_orig hcur hbb, hlookOrig]
        exact hstmtOrig
      refine .step hstepOrig
        (ih (k_orig + 1) (hs'Cur.trans hcur) (hs'Stack.trans hstack) ?_)
      intro bb' hbb'
      rw [hs'Blk, hbb] at hbb'
      injection hbb' with hbbEq
      subst hbbEq
      rw [hs'Idx]
      exact ⟨rem, hOrig', hLow'⟩

theorem stripNopsBody_simulates_aux {adts : List AdtDecl}
    {bodies : List BodyDecl} {b : MirBody} {s : MirState}
    {P : MirReturn → Prop}
    (hcalls : b.blocks.all (fun bb => !isCall1 bb.terminator) = true)
    (hP : StmtIdxInvariant P)
    (hexec : ExecNormal adts bodies (stripNopsBody b) s P) :
    ∀ (k_orig : Nat),
      s.curBody = none →
      s.stack = [] →
      (∀ bb, lookupAt b.blocks s.block = some bb →
        ∃ rem,
          IsSuffixAt bb.stmts k_orig rem ∧
          IsSuffixAt (filterNops bb.stmts) s.stmtIdx (filterNops rem)) →
      ExecNormal adts bodies b { s with stmtIdx := k_orig } P := by
  induction hexec with
  | @normal s v P hterm hp =>
    intro k_orig hcur hstack hsuf
    cases hbb : lookupAt b.blocks s.block with
    | none =>
      dsimp [evalMirStep, stripNopsBody] at hterm
      rw [hcur] at hterm
      dsimp [Option.getD] at hterm
      rw [lookupAt_map, hbb] at hterm
      cases hterm
    | some bb =>
      cases hsuf bb hbb with
      | intro rem hrem =>
        exact stripNops_normal_suffix hcalls hP hp hcur hstack hbb hterm
          rem k_orig hrem.1 hrem.2
  | @step s s' P hstep _ ih =>
    intro k_orig hcur hstack hsuf
    cases hbb : lookupAt b.blocks s.block with
    | none =>
      dsimp [evalMirStep, stripNopsBody] at hstep
      rw [hcur] at hstep
      dsimp [Option.getD] at hstep
      rw [lookupAt_map, hbb] at hstep
      cases hstep
    | some bb =>
      cases hsuf bb hbb with
      | intro rem hrem =>
        exact stripNops_step_suffix hcalls hcur hstack hbb hstep (ih hP)
          rem k_orig hrem.1 hrem.2

/-- Backward simulation for `stripNopsBody`: any normal-termination execution
of `stripNopsBody b` from a statement-0 state (`hstmt : s.stmtIdx = 0`) lifts
to a normal-termination execution of `b`. -/
theorem stripNopsBody_simulates {adts : List AdtDecl} {bodies : List BodyDecl}
    {b : MirBody} {s : MirState} {P : MirReturn → Prop}
    (hcalls : b.blocks.all (fun bb => !isCall1 bb.terminator) = true)
    (hP : StmtIdxInvariant P := by intro _ _ _ h; exact h)
    (hstmt : s.stmtIdx = 0 := by rfl)
    (hcur : s.curBody = none := by rfl)
    (hstack : s.stack = [])
    (hexec : ExecNormal adts bodies (stripNopsBody b) s P) :
    ExecNormal adts bodies b s P := by
  have hsim := stripNopsBody_simulates_aux hcalls hP hexec 0 hcur hstack
    (fun bb _ => by
      rw [hstmt]
      exact isSuffixAt_zero_witness bb)
  have hsEq : { s with stmtIdx := 0 } = s := by
    cases s
    dsimp at hstmt
    subst hstmt
    rfl
  rw [hsEq] at hsim
  exact hsim

/-!
## 3. Pass 2: Fixed-Point Forwarding-`goto` Coalescing (`coalesceGotosBody`)
-/

/-- Coalesce a `.goto target` terminator across an empty forwarding block
`{ stmts := [], terminator := .goto target2 }`, provided `target.index <
blocks.length`. -/
def lowerTerminator (blocks : List BasicBlock) :
    Terminator → Terminator
  | .goto target =>
    if decide (target.index < blocks.length) then
      match lookupAt blocks target.index with
      | some { stmts := [], terminator := .goto target2 } => .goto target2
      | _ => .goto target
    else
      .goto target
  | term => term

/-- Normalize a basic block by one forwarding-`goto` coalescing step. -/
def lowerBlock (blocks : List BasicBlock)
    (bb : BasicBlock) : BasicBlock where
  stmts := bb.stmts
  terminator := lowerTerminator blocks bb.terminator

/-- One forwarding-`goto` coalescing step across all blocks of `b`. -/
def lowerBodyStep (b : MirBody) : MirBody where
  argTys := b.argTys
  retTy := b.retTy
  localCount := b.localCount
  blocks := b.blocks.map (lowerBlock b.blocks)
  requiredConsts := b.requiredConsts

theorem isCall1_lowerTerminator (blocks : List BasicBlock)
    (term : Terminator) :
    isCall1 (lowerTerminator blocks term) = isCall1 term := by
  cases term with
  | goto target =>
    dsimp [lowerTerminator]
    cases decide (target.index < blocks.length) with
    | false => rfl
    | true =>
      dsimp
      cases lookupAt blocks target.index with
      | none => rfl
      | some bb =>
        cases bb with
        | mk stmts termT =>
          cases stmts with
          | nil => cases termT <;> rfl
          | cons _ _ => rfl
  | _ => rfl

theorem noCall_lowerBodyStep (b : MirBody) :
    (lowerBodyStep b).blocks.all (fun bb => !isCall1 bb.terminator) =
      b.blocks.all (fun bb => !isCall1 bb.terminator) :=
  all_map_eq (lowerBlock b.blocks) (fun bb => !isCall1 bb.terminator)
    (fun bb => !isCall1 bb.terminator)
    (fun bb => congrArg not (isCall1_lowerTerminator b.blocks bb.terminator))
    b.blocks

theorem not_normal_of_goto (adts : List AdtDecl) (bodies : List BodyDecl)
    (b : MirBody) (s : MirState) (target : BlockId) {v : MirReturn} :
    evalMirTerminator adts bodies b s (.goto target) =
      .terminated (.normal v) → False := by
  dsimp [evalMirTerminator, MirState.gotoBlock]
  exact not_normal_of_if_failed (fun h => by cases h)

theorem evalMirTerminator_eq_of_nocall (adts : List AdtDecl)
    (bodies : List BodyDecl) (b : MirBody) (s : MirState)
    (term : Terminator) (hnocall : isCall1 term = false) :
    evalMirTerminator adts bodies (lowerBodyStep b) s term =
      evalMirTerminator adts bodies b s term := by
  cases term with
  | return_ => rfl
  | goto _ =>
    dsimp [evalMirTerminator, lowerBodyStep]
    rw [list_length_map]
  | unreachable => rfl
  | panic => rfl
  | assert _ _ _ =>
    dsimp [evalMirTerminator, lowerBodyStep]
    rw [list_length_map]
  | switchInt _ _ _ =>
    dsimp [evalMirTerminator, lowerBodyStep]
    rw [list_length_map]
  | callSizeOf _ _ _ =>
    dsimp [evalMirTerminator, lowerBodyStep]
    rw [list_length_map]
  | callTransmuteCopy _ _ _ _ _ =>
    dsimp [evalMirTerminator, lowerBodyStep]
    rw [list_length_map]
  | call1 _ _ _ _ _ => cases hnocall
  | unsupported => rfl

theorem evalMirTerminator_lowerBodyStep_normal (adts : List AdtDecl)
    (bodies : List BodyDecl) (b : MirBody) (s : MirState)
    (term : Terminator) {v : MirReturn}
    (hnocall : isCall1 term = false) :
    evalMirTerminator adts bodies (lowerBodyStep b) s
        (lowerTerminator b.blocks term) = .terminated (.normal v) →
      evalMirTerminator adts bodies b s term = .terminated (.normal v) := by
  cases term with
  | goto target =>
    dsimp [lowerTerminator]
    cases decide (target.index < b.blocks.length) with
    | false =>
      dsimp
      exact fun h =>
        False.elim (not_normal_of_goto adts bodies (lowerBodyStep b) s target h)
    | true =>
      dsimp
      cases lookupAt b.blocks target.index with
      | none =>
        dsimp
        exact fun h =>
          False.elim
            (not_normal_of_goto adts bodies (lowerBodyStep b) s target h)
      | some bbT =>
        cases bbT with
        | mk stmtsT termT =>
          cases stmtsT with
          | nil =>
            cases termT <;> (
              dsimp
              exact fun h =>
                False.elim
                  (not_normal_of_goto adts bodies (lowerBodyStep b) s _ h))
          | cons _ _ =>
            dsimp
            exact fun h =>
              False.elim
                (not_normal_of_goto adts bodies (lowerBodyStep b) s target h)
  | _ =>
    dsimp [lowerTerminator]
    rw [evalMirTerminator_eq_of_nocall adts bodies b s _ hnocall]
    exact fun h => h

theorem evalMirStmt_preserves_root (adts : List AdtDecl) (b : MirBody)
    (s s' : MirState) (stmt : Stmt)
    (hcur : s.curBody = none) (hstack : s.stack = []) :
    evalMirStmt b s stmt adts = .silent s' →
      s'.curBody = none ∧ s'.stack = [] := by
  intro h
  have ⟨_, _, _, hc, hst⟩ :=
    evalMirStmt_with_stmtIdx_silent adts b b s s' 0 stmt rfl h
  exact ⟨hc.trans hcur, hst.trans hstack⟩

theorem evalMirTerminator_preserves_root (adts : List AdtDecl)
    (bodies : List BodyDecl) (b : MirBody) (s s' : MirState)
    (term : Terminator) (hcur : s.curBody = none) (hstack : s.stack = [])
    (hnocall : isCall1 term = false) :
    evalMirTerminator adts bodies b s term = .silent s' →
      s'.curBody = none ∧ s'.stack = [] := by
  intro h
  have ⟨_, _, hc, hst⟩ :=
    evalMirTerminator_with_stmtIdx_silent adts bodies b b s s' 0 term rfl rfl
      hcur hstack hnocall h
  exact ⟨hc, hst⟩

theorem evalMirTerminator_lowerBodyStep_silent (adts : List AdtDecl)
    (bodies : List BodyDecl) (b : MirBody) (s s' : MirState)
    (term : Terminator)
    (hcur : s.curBody = none)
    (hstack : s.stack = [])
    (hnocall : isCall1 term = false) :
    evalMirTerminator adts bodies (lowerBodyStep b) s
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
              rw [evalMirTerminator_eq_of_nocall adts bodies b s
                (.goto target2) rfl]
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
              rw [evalMirTerminator_eq_of_nocall adts bodies b s
                (.goto target) rfl]
              exact fun h =>
                ⟨evalMirTerminator_preserves_root adts bodies b s s'
                  (.goto target) hcur hstack rfl h, Or.inl h⟩
          | cons _ _ =>
            dsimp
            rw [evalMirTerminator_eq_of_nocall adts bodies b s
              (.goto target) rfl]
            exact fun h =>
              ⟨evalMirTerminator_preserves_root adts bodies b s s'
                (.goto target) hcur hstack rfl h, Or.inl h⟩
  | _ =>
    dsimp [lowerTerminator]
    rw [evalMirTerminator_eq_of_nocall adts bodies b s _ hnocall]
    exact fun h =>
      ⟨evalMirTerminator_preserves_root adts bodies b s s' _ hcur hstack
        hnocall h, Or.inl h⟩

theorem evalMirStep_lowerBodyStep_normal (adts : List AdtDecl)
    (bodies : List BodyDecl) (b : MirBody) (s : MirState) {v : MirReturn}
    (hcalls : b.blocks.all (fun bb => !isCall1 bb.terminator) = true)
    (hcur : s.curBody = none) :
    evalMirStep adts bodies (lowerBodyStep b) s = .terminated (.normal v) →
      evalMirStep adts bodies b s = .terminated (.normal v) := by
  dsimp [evalMirStep, lowerBodyStep]
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
    | some _ =>
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
        exact evalMirTerminator_lowerBodyStep_normal adts bodies b s
          bb.terminator (noCall_of_all hcalls (lookupAt_mem hbb))

/-- Backward simulation for a single forwarding-`goto` coalescing pass. -/
theorem lowerBodyStep_simulates {adts : List AdtDecl} {bodies : List BodyDecl}
    {b : MirBody} {s : MirState} {P : MirReturn → Prop}
    (hcalls : b.blocks.all (fun bb => !isCall1 bb.terminator) = true)
    (hcur : s.curBody = none := by rfl)
    (hstack : s.stack = [])
    (hexec : ExecNormal adts bodies (lowerBodyStep b) s P) :
    ExecNormal adts bodies b s P := by
  induction hexec with
  | normal hterm hp =>
    exact .normal
      (evalMirStep_lowerBodyStep_normal adts bodies b _ hcalls hcur hterm) hp
  | @step s s' P hstep _ ih =>
    revert hstep
    dsimp [evalMirStep, lowerBodyStep]
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
          have hsim := evalMirTerminator_lowerBodyStep_silent adts bodies b s s'
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

/-- Iterate `lowerBodyStep` once per element of `xs`. -/
def lowerBodyIterList (xs : List BasicBlock) (b : MirBody) : MirBody :=
  xs.foldr (fun _ acc => lowerBodyStep acc) b

/-- Coalesce forwarding `goto` chains across up to `b.blocks.length` hops. -/
def coalesceGotosBody (b : MirBody) : MirBody :=
  lowerBodyIterList b.blocks b

theorem noCall_lowerBodyIterList :
    ∀ (xs : List BasicBlock) (b : MirBody),
      (lowerBodyIterList xs b).blocks.all (fun bb => !isCall1 bb.terminator) =
        b.blocks.all (fun bb => !isCall1 bb.terminator)
  | [], _ => rfl
  | _ :: xs, b =>
    (noCall_lowerBodyStep (lowerBodyIterList xs b)).trans
      (noCall_lowerBodyIterList xs b)

theorem lowerBodyIterList_simulates {adts : List AdtDecl}
    {bodies : List BodyDecl} {b : MirBody} {s : MirState}
    {P : MirReturn → Prop}
    (hcalls : b.blocks.all (fun bb => !isCall1 bb.terminator) = true)
    (hcur : s.curBody = none := by rfl)
    (hstack : s.stack = []) :
    ∀ (xs : List BasicBlock),
      ExecNormal adts bodies (lowerBodyIterList xs b) s P →
      ExecNormal adts bodies b s P
  | [], hexec => hexec
  | _ :: xs, hexec =>
    have hcallsXs :
        (lowerBodyIterList xs b).blocks.all (fun bb => !isCall1 bb.terminator) =
          true := by
      rw [noCall_lowerBodyIterList]
      exact hcalls
    lowerBodyIterList_simulates hcalls hcur hstack xs
      (lowerBodyStep_simulates hcallsXs hcur hstack hexec)

theorem coalesceGotosBody_simulates {adts : List AdtDecl}
    {bodies : List BodyDecl} {b : MirBody} {s : MirState}
    {P : MirReturn → Prop}
    (hcalls : b.blocks.all (fun bb => !isCall1 bb.terminator) = true)
    (hcur : s.curBody = none := by rfl)
    (hstack : s.stack = [])
    (hexec : ExecNormal adts bodies (coalesceGotosBody b) s P) :
    ExecNormal adts bodies b s P :=
  lowerBodyIterList_simulates hcalls hcur hstack b.blocks hexec

/-!
## 4. Composed In-Place Lowering (`lowerBody`) and Entry-State Equivalence
-/

/-- Normalize a `MirBody` in place by stripping all `Stmt.nop` statements and
coalescing forwarding `goto` chains to a fixed point while preserving the
body's signature, local count, `BlockId` numbering, and required constants. -/
def lowerBody (b : MirBody) : MirBody :=
  coalesceGotosBody (stripNopsBody b)

theorem lowerBodyIterList_argTys :
    ∀ (xs : List BasicBlock) (b : MirBody),
      (lowerBodyIterList xs b).argTys = b.argTys
  | [], _ => rfl
  | _ :: xs, b => lowerBodyIterList_argTys xs b

theorem lowerBodyIterList_retTy :
    ∀ (xs : List BasicBlock) (b : MirBody),
      (lowerBodyIterList xs b).retTy = b.retTy
  | [], _ => rfl
  | _ :: xs, b => lowerBodyIterList_retTy xs b

theorem lowerBodyIterList_localCount :
    ∀ (xs : List BasicBlock) (b : MirBody),
      (lowerBodyIterList xs b).localCount = b.localCount
  | [], _ => rfl
  | _ :: xs, b => lowerBodyIterList_localCount xs b

theorem lowerBodyIterList_requiredConsts :
    ∀ (xs : List BasicBlock) (b : MirBody),
      (lowerBodyIterList xs b).requiredConsts = b.requiredConsts
  | [], _ => rfl
  | _ :: xs, b => lowerBodyIterList_requiredConsts xs b

theorem lowerBodyIterList_blocks_length :
    ∀ (xs : List BasicBlock) (b : MirBody),
      (lowerBodyIterList xs b).blocks.length = b.blocks.length
  | [], _ => rfl
  | _ :: xs, b =>
    (list_length_map (lowerBlock (lowerBodyIterList xs b).blocks)
      (lowerBodyIterList xs b).blocks).trans
      (lowerBodyIterList_blocks_length xs b)

theorem lowerBody_argTys (b : MirBody) : (lowerBody b).argTys = b.argTys :=
  lowerBodyIterList_argTys (stripNopsBody b).blocks (stripNopsBody b)

theorem lowerBody_retTy (b : MirBody) : (lowerBody b).retTy = b.retTy :=
  lowerBodyIterList_retTy (stripNopsBody b).blocks (stripNopsBody b)

theorem lowerBody_localCount (b : MirBody) :
    (lowerBody b).localCount = b.localCount :=
  lowerBodyIterList_localCount (stripNopsBody b).blocks (stripNopsBody b)

theorem lowerBody_requiredConsts (b : MirBody) :
    (lowerBody b).requiredConsts = b.requiredConsts :=
  lowerBodyIterList_requiredConsts (stripNopsBody b).blocks (stripNopsBody b)

theorem lowerBody_blocks_length (b : MirBody) :
    (lowerBody b).blocks.length = b.blocks.length :=
  (lowerBodyIterList_blocks_length (stripNopsBody b).blocks
    (stripNopsBody b)).trans (stripNopsBody_blocks_length b)

theorem noCall_lowerBody (b : MirBody) :
    (lowerBody b).blocks.all (fun bb => !isCall1 bb.terminator) =
      b.blocks.all (fun bb => !isCall1 bb.terminator) :=
  (noCall_lowerBodyIterList (stripNopsBody b).blocks (stripNopsBody b)).trans
    (noCall_stripNopsBody b)

theorem initEntryState_lowerBody (adts : List AdtDecl) (b : MirBody)
    (s : MirState) :
    initEntryState adts (lowerBody b) s = initEntryState adts b s := by
  dsimp [initEntryState]
  rw [lowerBody_argTys, lowerBody_retTy, lowerBody_localCount]

theorem requiresConst_lowerBody_iff {bodies : List BodyDecl} {b : MirBody}
    {c : Option MirBody}
    (hcalls : b.blocks.all (fun bb => !isCall1 bb.terminator) = true) :
    RequiresConst bodies (some (lowerBody b)) c ↔
      RequiresConst bodies (some b) c := by
  have hcallsLow :
      (lowerBody b).blocks.all (fun bb => !isCall1 bb.terminator) = true := by
    rw [noCall_lowerBody]
    exact hcalls
  constructor
  · intro h
    cases h with
    | direct hmem =>
      rw [lowerBody_requiredConsts] at hmem
      exact .direct hmem
    | viaConst hmem hrest =>
      rw [lowerBody_requiredConsts] at hmem
      exact .viaConst hmem hrest
    | viaCall hbb hterm _ =>
      have hnc := noCall_of_all hcallsLow hbb
      rw [hterm] at hnc
      cases hnc
  · intro h
    cases h with
    | direct hmem =>
      rw [← lowerBody_requiredConsts b] at hmem
      exact .direct hmem
    | viaConst hmem hrest =>
      rw [← lowerBody_requiredConsts b] at hmem
      exact .viaConst hmem hrest
    | viaCall hbb hterm _ =>
      have hnc := noCall_of_all hcalls hbb
      rw [hterm] at hnc
      cases hnc

theorem constsTotal_lowerBody_iff {adts : List AdtDecl} {bodies : List BodyDecl}
    {b : MirBody}
    (hcalls : b.blocks.all (fun bb => !isCall1 bb.terminator) = true) :
    ConstsTotal adts bodies (lowerBody b) ↔ ConstsTotal adts bodies b :=
  ⟨fun h tySizes c hvalid hreq =>
    h tySizes c hvalid ((requiresConst_lowerBody_iff hcalls).mpr hreq),
   fun h tySizes c hvalid hreq =>
    h tySizes c hvalid ((requiresConst_lowerBody_iff hcalls).mp hreq)⟩

theorem monoAdmitted_lowerBody_iff {adts : List AdtDecl}
    {bodies : List BodyDecl} {tySizes : Nat → Nat} {b : MirBody}
    (hcalls : b.blocks.all (fun bb => !isCall1 bb.terminator) = true) :
    MonoAdmitted adts bodies tySizes (lowerBody b) ↔
      MonoAdmitted adts bodies tySizes b :=
  ⟨fun h c hreq => h c ((requiresConst_lowerBody_iff hcalls).mpr hreq),
   fun h c hreq => h c ((requiresConst_lowerBody_iff hcalls).mp hreq)⟩

theorem initMirState_lowerBody_iff {adts : List AdtDecl}
    {bodies : List BodyDecl} {b : MirBody} {s : MirState}
    (hcalls : b.blocks.all (fun bb => !isCall1 bb.terminator) = true) :
    initMirState adts bodies (lowerBody b) s ↔
      initMirState adts bodies b s := by
  dsimp [initMirState]
  rw [initEntryState_lowerBody]
  exact ⟨fun ⟨h1, h2, h3⟩ =>
          ⟨h1, (constsTotal_lowerBody_iff hcalls).mp h2,
           (monoAdmitted_lowerBody_iff hcalls).mp h3⟩,
         fun ⟨h1, h2, h3⟩ =>
          ⟨h1, (constsTotal_lowerBody_iff hcalls).mpr h2,
           (monoAdmitted_lowerBody_iff hcalls).mpr h3⟩⟩

/-- Backward simulation for `lowerBody`: any normal-termination execution of
`lowerBody b` on an intra-procedural body (`hcalls`) from a statement-0 state
lifts to a normal-termination execution of the unlowered body `b`. -/
theorem lowerBody_simulates {adts : List AdtDecl} {bodies : List BodyDecl}
    {b : MirBody} {s : MirState} {P : MirReturn → Prop}
    (hcalls : b.blocks.all (fun bb => !isCall1 bb.terminator) = true)
    (hP : StmtIdxInvariant P := by intro _ _ _ h; exact h)
    (hstmt : s.stmtIdx = 0 := by rfl)
    (hcur : s.curBody = none := by rfl)
    (hstack : s.stack = [])
    (hexec : ExecNormal adts bodies (lowerBody b) s P) :
    ExecNormal adts bodies b s P := by
  have hcallsStrip :
      (stripNopsBody b).blocks.all (fun bb => !isCall1 bb.terminator) = true := by
    rw [noCall_stripNopsBody]
    exact hcalls
  exact stripNopsBody_simulates hcalls hP hstmt hcur hstack
    (coalesceGotosBody_simulates hcallsStrip hcur hstack hexec)

/-- Diamond CFG join helper: once two branch executions step to a shared join
state `sJoin`, a single suffix proof from `sJoin` discharges both branches. -/
theorem execNormal_join {adts : List AdtDecl} {bodies : List BodyDecl}
    {body : MirBody} {s sJoin : MirState} {P : MirReturn → Prop}
    (hstep : evalMirStep adts bodies body s = .silent sJoin)
    (hjoin : ExecNormal adts bodies body sJoin P) :
    ExecNormal adts bodies body s P :=
  .step hstep hjoin

/-- Canary: `lowerBody` strips `Stmt.nop` statements and coalesces a multi-hop
forwarding `goto` chain (`bb0 -> bb1 -> bb2 -> bb3`, where `bb1` also contains a
`Stmt.nop`) into a direct jump (`bb0 -> bb3`), and `lowerBody_simulates` lifts
the shortened execution back to the unlowered body. -/
def gotoChainBody : MirBody where
  argTys := [.usize]
  retTy := .usize
  localCount := 2
  blocks := [
    { stmts := [.nop, .assign ⟨⟨0⟩, []⟩ (.use (.copy ⟨⟨1⟩, []⟩)), .nop]
      terminator := .goto ⟨1⟩ },
    { stmts := [.nop]
      terminator := .goto ⟨2⟩ },
    { stmts := []
      terminator := .goto ⟨3⟩ },
    { stmts := [.nop]
      terminator := .return_ }
  ]

theorem canary_lowerBody_coalesces_goto_chain :
    (lowerBody gotoChainBody).blocks = [
      { stmts := [.assign ⟨⟨0⟩, []⟩ (.use (.copy ⟨⟨1⟩, []⟩))]
        terminator := .goto ⟨3⟩ },
      { stmts := []
        terminator := .goto ⟨3⟩ },
      { stmts := []
        terminator := .goto ⟨3⟩ },
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
  refine lowerBody_simulates rfl (fun _ _ _ h => h) rfl rfl rfl ?_
  exact .step rfl (.step rfl (.normal rfl rfl))

end Anneal
