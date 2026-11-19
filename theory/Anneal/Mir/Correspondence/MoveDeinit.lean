/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/
import Trusted.Correspondence
import Anneal.Mir.Correspondence.Codec
import Anneal.Mir.Correspondence.LayoutQuery

/-!
# Move-deinitialization correspondence proofs for `Trusted.Correspondence`

Untrusted proofs about the shared byte-level machine of
`Trusted.Correspondence`:

* **Latch transparency** (`twoPhaseStrategy_true_eq_eager`): with
  `deinitMoves = true`, LeanMiri's two-phase `evalOperand` →
  `readImmediate` / `copyRuntimePlaceNoValidate` protocol is extensionally
  `M_anneal`'s eager move deinitialization; with `deinitMoves = false`, `move`
  is `copy` (`deinitMovedPlace_false_id`).
* **Codec-driven resolution correspondence** (`refFetch_encodeProg`) and the
  headline simulation theorems (`anneal_corresponds_to_miri`,
  `refObs_encodeProg`, `reachesResult_fault_iff_refReachesOutcome`,
  `behavior_transfer`, `simulationInv_bijective`).
* **Falsification witnesses** (Part 8): `deinitMoves = false`, eager indirect
  deinitialization inside `evalOperand`, batched call arguments, and the
  unpatched upstream `Call.lean` argument path all break the correspondence.
* **Tree Borrows** (Part 9): moving out of `*ptr` is a read, not a write.
* **Wiring and latch invariants** (Parts 10, 10c, 10d) and the **live
  `Trusted.Rustc.V2026_06_01.MirSemantics.evalOperand` bridge** (Part 10b).
* Proofs of `CorrespondenceClaim`, `FaultEquivalenceClaim`,
  `MiriMoveDeinitWiringClaim`, and `TrustedProjectedMoveDeinitClaim`.
-/

namespace Anneal.Mir.Correspondence

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.Correspondence

set_option linter.constructorNameAsVariable false

/-! ## Part 5 — The two-phase latch protocol is transparent when `deinitMoves = true` -/

theorem clearLatch_idem (st : PState) : clearLatch (clearLatch st) = clearLatch st := rfl

theorem clearLatch_set_true (st : PState) :
    clearLatch { clearLatch st with pendingMoveDeinit := true } = clearLatch st := rfl

theorem twoPhaseReadOperand_true_eq (pb : Nat) (st : PState) (op : SemOperand) :
    twoPhaseReadOperand true pb st op = annealReadOperand pb st op := by
  cases op with
  | const b ty =>
    simp only [twoPhaseReadOperand, refEvalOperand, refReadImmediate, takePendingMoveDeinit,
      readOpBytes, annealReadOperand, ite_true, clearLatch_idem]
    cases checkValid ty b <;> rfl
  | copy p =>
    simp only [twoPhaseReadOperand, refEvalOperand, annealReadOperand, ite_true]
    cases h : evalPlaceToOp pb (clearLatch st) p with
    | error e => rfl
    | ok r =>
      obtain ⟨o, ty⟩ := r
      simp only [refReadImmediate, takePendingMoveDeinit, clearLatch_idem]
      cases readOpBytes (clearLatch st) o with
      | error e => rfl
      | ok r' =>
        obtain ⟨b, st₁⟩ := r'
        simp only
        cases checkValid ty b <;> rfl
  | move p =>
    simp only [twoPhaseReadOperand, refEvalOperand, annealReadOperand]
    cases h : evalPlaceToOp pb (clearLatch st) p with
    | error e => rfl
    | ok r =>
      obtain ⟨o, ty⟩ := r
      cases o with
      | immediate b =>
        simp only
        cases hp : p.projs with
        | nil =>
          simp only
          cases setLocalE (clearLatch st) p.local_ (.imm (uninitBytes b.length)) with
          | error e => rfl
          | ok st₁ =>
            simp only [refReadImmediate, takePendingMoveDeinit, readOpBytes, clearLatch_idem]
            cases checkValid ty b <;> rfl
        | cons _ _ => rfl
      | indirect mp =>
        simp only [refReadImmediate, takePendingMoveDeinit, readOpBytes, clearLatch_set_true]
        cases loadMPlace (clearLatch st) mp with
        | error e => rfl
        | ok r' =>
          obtain ⟨b, st₁⟩ := r'
          simp only
          cases checkValid ty b with
          | error e => rfl
          | ok u => rfl

theorem twoPhaseAssignUse_true_eq (pb : Nat) (st : PState) (op : SemOperand) (d : DestPlace) :
    twoPhaseAssignUse true pb st op d = annealAssignUse pb st op d := by
  cases op with
  | const b ty =>
    simp only [twoPhaseAssignUse, refEvalOperand, refCopyRuntimePlaceNoValidate,
      takePendingMoveDeinit, readOpBytes, annealAssignUse, ite_true, clearLatch_idem]
    cases checkValid ty b <;> rfl
  | copy p =>
    simp only [twoPhaseAssignUse, refEvalOperand, annealAssignUse, ite_true]
    cases h : evalPlaceToOp pb (clearLatch st) p with
    | error e => rfl
    | ok r =>
      obtain ⟨o, ty⟩ := r
      simp only [refCopyRuntimePlaceNoValidate, takePendingMoveDeinit, clearLatch_idem]
      cases o with
      | immediate b =>
        simp only [readOpBytes]
        cases checkValid ty b <;> rfl
      | indirect src =>
        cases hm : usesMemoryPath ty (.indirect src) with
        | true =>
          simp only
          cases copyMemPath (clearLatch st) src d <;> rfl
        | false =>
          simp only [readOpBytes]
          cases loadMPlace (clearLatch st) src with
          | error e => rfl
          | ok r' =>
            obtain ⟨b, st₁⟩ := r'
            simp only
            cases checkValid ty b <;> rfl
  | move p =>
    simp only [twoPhaseAssignUse, refEvalOperand, annealAssignUse]
    cases h : evalPlaceToOp pb (clearLatch st) p with
    | error e => rfl
    | ok r =>
      obtain ⟨o, ty⟩ := r
      cases o with
      | immediate b =>
        simp only
        cases hp : p.projs with
        | nil =>
          simp only
          cases setLocalE (clearLatch st) p.local_ (.imm (uninitBytes b.length)) with
          | error e => rfl
          | ok st₁ =>
            simp only [refCopyRuntimePlaceNoValidate, takePendingMoveDeinit, readOpBytes,
              clearLatch_idem]
            cases checkValid ty b <;> rfl
        | cons _ _ => rfl
      | indirect src =>
        simp only [refCopyRuntimePlaceNoValidate, takePendingMoveDeinit, clearLatch_set_true]
        cases hm : usesMemoryPath ty (.indirect src) with
        | true =>
          simp only
          cases copyMemPath (clearLatch st) src d <;> rfl
        | false =>
          simp only [readOpBytes]
          cases loadMPlace (clearLatch st) src with
          | error e => rfl
          | ok r' =>
            obtain ⟨b, st₁⟩ := r'
            simp only
            cases checkValid ty b with
            | error e => rfl
            | ok u => rfl

/-- **Latch transparency**: with `deinitMoves = true` the LeanMiri two-phase
`evalOperand` → `readImmediate` / `copyRuntimePlaceNoValidate` protocol is
extensionally equal to `M_anneal`'s eager move deinitialization. -/
theorem twoPhaseStrategy_true_eq_eager : twoPhaseStrategy true = eagerStrategy := by
  have hR : twoPhaseReadOperand true = annealReadOperand := by
    funext pb st op; exact twoPhaseReadOperand_true_eq pb st op
  have hA : twoPhaseAssignUse true = annealAssignUse := by
    funext pb st op d; exact twoPhaseAssignUse_true_eq pb st op d
  simp only [twoPhaseStrategy, eagerStrategy, hR, hA]

/-- `deinitMovedPlace_false_id`: with `deinitMoves = false`, `Operand.move`
is *identical* to `Operand.copy` at `evalOperand` and at both consumers
(upstream `lean-miri` behavior: `copy_move_same`). -/
theorem deinitMovedPlace_false_id (pb : Nat) (st : PState) (p : SemPlace) (d : DestPlace) :
    refEvalOperand false pb st (.move p) = refEvalOperand false pb st (.copy p) ∧
    twoPhaseReadOperand false pb st (.move p) = twoPhaseReadOperand false pb st (.copy p) ∧
    twoPhaseAssignUse false pb st (.move p) d = twoPhaseAssignUse false pb st (.copy p) d := by
  have h : refEvalOperand false pb st (.move p) = refEvalOperand false pb st (.copy p) := by
    simp only [refEvalOperand, Bool.false_eq_true, ite_false]
  refine ⟨h, ?_, ?_⟩
  · simp only [twoPhaseReadOperand, h]
  · simp only [twoPhaseAssignUse, h]

/-- With `deinitMoves = false` the latch is never consulted by consumers. -/
theorem takePendingMoveDeinit_false (st : PState) :
    (takePendingMoveDeinit false st).1 = false := rfl

/-! ### Falsification variant: eager deinit inside `evalOperand` -/

/-- The rejected design: deinitialize an `.indirect mplace` *inside*
`evalOperand`, before any consumer has read it. -/
def eagerInEvalOperandReadOperand (ptrBits : Nat) (st : PState) (op : SemOperand) :
    Except Fault (Bytes × PState) :=
  match op with
  | .move p =>
    match evalPlaceToOp ptrBits (clearLatch st) p with
    | .error e => .error e
    | .ok (.indirect mp, ty) =>
      match deinitMPlaceRaw (clearLatch st) mp with
      | .error e => .error e
      | .ok st₁ => refReadImmediate true st₁ (.indirect mp) ty
    | .ok (.immediate _, _) => twoPhaseReadOperand true ptrBits st op
  | _ => twoPhaseReadOperand true ptrBits st op

/-- Assignment counterpart of `eagerInEvalOperandReadOperand`. -/
def eagerInEvalOperandAssignUse (ptrBits : Nat) (st : PState) (op : SemOperand)
    (d : DestPlace) : Except Fault PState :=
  match op with
  | .move p =>
    match evalPlaceToOp ptrBits (clearLatch st) p with
    | .error e => .error e
    | .ok (.indirect mp, ty) =>
      match deinitMPlaceRaw (clearLatch st) mp with
      | .error e => .error e
      | .ok st₁ => refCopyRuntimePlaceNoValidate true st₁ (.indirect mp) ty d
    | .ok (.immediate _, _) => twoPhaseAssignUse true ptrBits st op d
  | _ => twoPhaseAssignUse true ptrBits st op d

/-- The eager-in-`evalOperand` operand strategy. -/
def eagerInEvalOperandStrategy : OperandStrategy :=
  { readOperand := eagerInEvalOperandReadOperand, assignUse := eagerInEvalOperandAssignUse }

/-! ### Falsification variant: batched call-argument evaluation (`kani#5172`)

All argument `OpTy`s are evaluated first and consumed afterwards; the single
Boolean latch of an earlier `move` argument is overwritten by later
arguments' `evalOperand`. -/

/-- Evaluate every operand (phase 1 only). -/
def evalOperandsBatched (dm : Bool) (pb : Nat) :
    PState → List SemOperand → Except Fault (List (OpTy × SemTy) × PState)
  | st, [] => .ok ([], st)
  | st, op :: ops =>
    match refEvalOperand dm pb st op with
    | .error e => .error e
    | .ok (o, ty, st₁) =>
      match evalOperandsBatched dm pb st₁ ops with
      | .error e => .error e
      | .ok (rs, st₂) => .ok ((o, ty) :: rs, st₂)

/-- Consume every evaluated operand (phase 2 only). -/
def consumeBatched (dm : Bool) : PState → List (OpTy × SemTy) → Except Fault (List Bytes × PState)
  | st, [] => .ok ([], st)
  | st, (o, ty) :: rs =>
    match refReadImmediate dm st o ty with
    | .error e => .error e
    | .ok (b, st₁) =>
      match consumeBatched dm st₁ rs with
      | .error e => .error e
      | .ok (bs, st₂) => .ok (b :: bs, st₂)

/-- Batched evaluation followed by batched consumption. -/
def readOperandsBatched (dm : Bool) (pb : Nat) (st : PState) (ops : List SemOperand) :
    Except Fault (List Bytes × PState) :=
  match evalOperandsBatched dm pb st ops with
  | .error e => .error e
  | .ok (rs, st₁) => consumeBatched dm st₁ rs

/-! ## Part 6b — Codec-driven resolution correspondence

`M_ref`'s demand-time resolution of `encodeProg p` coincides with
`M_anneal`'s deep resolution of `p`, for every program and every state. -/

theorem decodeList_map_congr {α β γ : Type} (f : β → Option α) (g : γ → β) (h : γ → Option α) :
    ∀ (xs : List γ), (∀ x ∈ xs, f (g x) = h x) → decodeList f (xs.map g) = decodeList h xs
  | [], _ => rfl
  | x :: xs, hx => by
    simp only [List.map, decodeList]
    rw [hx x (List.Mem.head _),
      decodeList_map_congr f g h xs (fun y hy => hx y (List.Mem.tail _ hy))]

theorem refResolveProj_encode {tt : TypeTable} (L : LayoutTable) (e : ProjectionElem)
    (h : Covers tt (projElemTys e)) :
    refResolveProj tt L (encodeProjElem tt e) = annealResolveProj L e := by
  cases e <;> simp only [encodeProjElem, refResolveProj, annealResolveProj, projElemTys] at h ⊢
  case field i ty => rw [refResolveTy_encode L h.single]

theorem refResolvePlace_encode {tt : TypeTable} (b : CapturedMir) (p : Place)
    (hd : DeclsCovered tt b) (h : Covers tt (placeTys p)) :
    refResolvePlace tt (encodeBody tt b) (encodePlace tt p) = annealResolvePlace b p := by
  simp only [refResolvePlace, annealResolvePlace, encodePlace, nth?_encodeDecls, encodeBody_layouts]
  cases hn : nth? b.localDecls p.local_ with
  | none => rfl
  | some d =>
    simp only [Option.map_some, encodeLocalDecl]
    rw [refResolveTy_encode _ (hd d (mem_of_nth? hn)),
      decodeList_map_congr _ _ _ _ (fun e he => refResolveProj_encode _ e (h.flatMap e he))]

theorem refResolveOperand_encode {tt : TypeTable} (b : CapturedMir) (op : Operand)
    (hd : DeclsCovered tt b) (h : Covers tt (operandTys op)) :
    refResolveOperand tt (encodeBody tt b) (encodeOperand tt op) = annealResolveOperand b op := by
  cases op <;> simp only [encodeOperand, refResolveOperand, annealResolveOperand, operandTys] at h ⊢
  · rw [refResolvePlace_encode b _ hd h]
  · rw [refResolvePlace_encode b _ hd h]
  · rw [encodeBody_layouts, refResolveTy_encode _ h.single]

theorem refResolveOperands_encode {tt : TypeTable} (b : CapturedMir) (ops : List Operand)
    (hd : DeclsCovered tt b) (h : Covers tt (ops.flatMap operandTys)) :
    decodeList (refResolveOperand tt (encodeBody tt b)) (ops.map (encodeOperand tt)) =
      decodeList (annealResolveOperand b) ops :=
  decodeList_map_congr _ _ _ _ (fun o ho => refResolveOperand_encode b o hd (h.flatMap o ho))

theorem refResolveRvalue_encode {tt : TypeTable} (b : CapturedMir) (rv : Rvalue)
    (hd : DeclsCovered tt b) (h : Covers tt (rvalueTys rv)) :
    refResolveRvalue tt (encodeBody tt b) (encodeRvalue tt rv) = annealResolveRvalue b rv := by
  cases rv <;> simp only [encodeRvalue, refResolveRvalue, annealResolveRvalue, rvalueTys] at h ⊢
  case use op => rw [refResolveOperand_encode b op hd h]
  case ref bk p => rw [refResolvePlace_encode b p hd h]
  case rawPtr m p => rw [refResolvePlace_encode b p hd h]
  case binaryOp o l r =>
    rw [refResolveOperand_encode b l hd h.append.1, refResolveOperand_encode b r hd h.append.2]
  case aggregate k ops => rw [refResolveOperands_encode b ops hd h.append.2]

theorem refResolveStmt_encode {tt : TypeTable} (b : CapturedMir) (s : Statement)
    (hd : DeclsCovered tt b) (h : Covers tt (stmtTys s)) :
    refResolveStmt tt (encodeBody tt b) (encodeStmt tt s) = annealResolveStmt b s := by
  obtain ⟨k, sp⟩ := s
  simp only [stmtTys] at h
  cases k <;> simp only [encodeStmt, encodeStmtKind, refResolveStmt, annealResolveStmt,
    stmtKindTys] at h ⊢
  case assign p rv =>
    rw [refResolvePlace_encode b p hd h.append.1, refResolveRvalue_encode b rv hd h.append.2]
  case deinit p => rw [refResolvePlace_encode b p hd h]
  case storageLive l =>
    simp only [nth?_encodeDecls, encodeBody_layouts]
    cases hn : nth? b.localDecls l with
    | none => rfl
    | some d =>
      simp only [Option.map_some, Option.bind_some, encodeLocalDecl]
      rw [refResolveTy_encode _ (hd d (mem_of_nth? hn))]

theorem refResolveLocals_encode {tt : TypeTable} (b : CapturedMir) (hd : DeclsCovered tt b) :
    refResolveLocals tt (encodeBody tt b) = annealResolveLocals b := by
  simp only [refResolveLocals, annealResolveLocals, encodeBody]
  exact decodeList_map_congr _ _ _ _ (fun d hdm => by
    simp only [encodeLocalDecl]; exact refResolveTy_encode _ (hd d hdm))

theorem defPaths_encode (tt : TypeTable) (bs : List CapturedMir) :
    (bs.map (encodeBody tt)).map RefBody.defPath = bs.map CapturedMir.defPath := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp only [List.map, ih]; rfl

theorem refSite_encode (p : V2026Prog) (frames : List PFrame) :
    refSite (encodeProg p) frames = annealSite p frames := by
  match frames with
  | [] => rfl
  | [_] => rfl
  | _ :: caller :: _ =>
    simp only [refSite, annealSite, encodeProg_bodies, nth?_map]
    cases hb : nth? p.bodies caller.body with
    | none => rfl
    | some cb =>
      have hcov := encodeProg_body_covered p cb (mem_of_nth? hb)
      simp only [Option.map_some, encodeBody, nth?_map]
      cases hbb : nth? cb.basicBlocks caller.block with
      | none => rfl
      | some bb =>
        have hbc := bodyCovered_block hcov (mem_of_nth? hbb)
        simp only [Option.map_some, encodeBlock, encodeTerminator]
        cases hk : bb.terminator.kind <;> simp only [encodeTermKind]
        case call f args dest target unwind =>
          have hdest : Covers (collectProgTypes p) (placeTys dest) := by
            have := hbc.append.2; rw [hk] at this; exact this.append.2
          rw [encodeProg_types]
          have := refResolvePlace_encode (tt := collectProgTypes p) cb dest
            (bodyCovered_decls hcov) hdest
          simp only [encodeBody] at this
          rw [this]

theorem refCallee_encode (p : V2026Prog) (f : Operand)
    (h : Covers (collectProgTypes p) (operandTys f)) :
    refCallee (encodeProg p) (encodeOperand (collectProgTypes p) f) = annealCallee p f := by
  cases f <;> simp only [encodeOperand, refCallee, annealCallee]
  case constant c =>
    simp only [operandTys] at h
    have hd : nth? (collectProgTypes p).types (encodeType (collectProgTypes p) c.ty) = some c.ty :=
      decodeType_encodeType_of_mem h.single
    rw [encodeProg_types, hd, encodeProg_bodies, defPaths_encode]
    rfl

theorem refResolveTerm_encode (p : V2026Prog) (frames : List PFrame) (b : CapturedMir)
    (hb : b ∈ p.bodies) (t : Terminator) (h : Covers (collectProgTypes p) (termKindTys t.kind)) :
    refResolveTerm (encodeProg p) frames (encodeBody (collectProgTypes p) b)
      (encodeTerminator (collectProgTypes p) t) = annealResolveTerm p frames b t := by
  have hcov := encodeProg_body_covered p b hb
  have hd := bodyCovered_decls hcov
  obtain ⟨k, sp⟩ := t
  simp only [termKindTys] at h
  cases k <;> simp only [encodeTerminator, encodeTermKind, refResolveTerm, annealResolveTerm,
    encodeProg_types] at h ⊢
  case return_ =>
    rw [refSite_encode]
    simp only [nth?_encodeDecls, encodeBody_layouts]
    cases hn : nth? b.localDecls 0 with
    | none => rfl
    | some d =>
      simp only [Option.map_some, Option.bind_some, encodeLocalDecl]
      rw [refResolveTy_encode _ (hd d (mem_of_nth? hn))]
  case switchInt d ts => rw [refResolveOperand_encode b d hd h]
  case assert c e tgt u => rw [refResolveOperand_encode b c hd h]
  case unwindResume => rw [refSite_encode]
  case call f args dest target unwind =>
    rw [refResolvePlace_encode b dest hd h.append.2,
        refResolveOperands_encode b args hd h.append.1.append.2]
    cases annealResolvePlace b dest with
    | none => rfl
    | some dest' =>
      cases decodeList (annealResolveOperand b) args with
      | none => rfl
      | some args' =>
        simp only
        rw [refCallee_encode p f h.append.1.append.1]
        cases hc : annealCallee p f with
        | none => rfl
        | some bi =>
          simp only [encodeProg_bodies, nth?_map]
          cases hcb : nth? p.bodies bi with
          | none => rfl
          | some cb =>
            simp only [Option.map_some, Option.bind_some]
            rw [refResolveLocals_encode cb
              (bodyCovered_decls (encodeProg_body_covered p cb (mem_of_nth? hcb)))]
            rfl

/-- **Fetch/resolve correspondence**: for every program and every state,
`M_ref`'s fetch of `encodeProg p` equals `M_anneal`'s fetch of `p`. -/
theorem refFetch_encodeProg (p : V2026Prog) (st : PState) :
    refFetch (encodeProg p) st = annealFetch p st := by
  rcases st with ⟨frames, heap, borrows, nextTag, pend⟩
  simp only [refFetch, annealFetch]
  cases frames with
  | nil => rfl
  | cons fr rest =>
    simp only [encodeProg_bodies, nth?_map]
    cases hb : nth? p.bodies fr.body with
    | none => rfl
    | some b =>
      have hmem := mem_of_nth? hb
      have hcov := encodeProg_body_covered p b hmem
      simp only [Option.map_some]
      simp only [encodeBody, nth?_map]
      cases hbb : nth? b.basicBlocks fr.block with
      | none => rfl
      | some bb =>
        have hbc := bodyCovered_block hcov (mem_of_nth? hbb)
        simp only [Option.map_some, encodeBlock, nth?_map, List.length_map]
        cases hs : nth? bb.statements fr.stmt with
        | some s =>
          simp only [Option.map_some]
          have := refResolveStmt_encode (tt := collectProgTypes p) b s (bodyCovered_decls hcov)
            (hbc.append.1.flatMap s (mem_of_nth? hs))
          simp only [encodeBody] at this
          rw [encodeProg_types, this]
        | none =>
          simp only [Option.map_none]
          cases Nat.beq fr.stmt bb.statements.length with
          | false => rfl
          | true =>
            have := refResolveTerm_encode p (fr :: rest) b hmem bb.terminator hbc.append.2
            simp only [encodeBody] at this
            rw [this]

/-- **Forward simulation (one step, every state)**: with `deinitMoves = true`,
`M_ref` on `encodeProg p` takes exactly `M_anneal`'s step on `p`. -/
theorem anneal_corresponds_to_miri (p : V2026Prog) (st : PState) :
    refStepCore true (encodeProg p) st = annealStep p st := by
  simp only [refStepCore, refStepCoreWith, annealStep, refFetch_encodeProg,
    twoPhaseStrategy_true_eq_eager]

theorem refInit_encodeProg (p : V2026Prog) (args : List Bytes) :
    refInit (encodeProg p) args = annealInit p args := by
  simp only [refInit, annealInit, encodeProg_bodies, encodeProg_entry, encodeProg_types, nth?_map]
  cases hb : nth? p.bodies p.entry with
  | none => rfl
  | some b =>
    simp only [Option.map_some]
    rw [refResolveLocals_encode b
      (bodyCovered_decls (encodeProg_body_covered p b (mem_of_nth? hb)))]
    rfl

theorem refRunFuel_encode (p : V2026Prog) :
    ∀ (n k : Nat) (st : PState),
      refOutcomeObs (refRunFuel true (encodeProg p) (n + 1) ⟨st, k, k + n⟩) =
        stepOutObs (annealRun p n st)
  | 0, k, st => by
    have h0 : Nat.blt k (k + 0) = false := by
      cases h : Nat.blt k (k + 0) with
      | false => rfl
      | true => exact absurd (Nat.blt_eq.mp h) (by omega)
    simp only [refRunFuel, refStep, h0, refOutcomeObs, annealRun, stepOutObs]
  | n + 1, k, st => by
    have hlt : Nat.blt k (k + (n + 1)) = true := by
      simp only [Nat.blt_eq]; omega
    rw [refRunFuel.eq_2, annealRun.eq_2]
    have hstep : refStep true (encodeProg p) ⟨st, k, k + (n + 1)⟩ =
        (match annealStep p st with
         | .running st' => .running ⟨st', k + 1, k + (n + 1)⟩
         | .returned b => .returned b
         | .panicked => .panicked
         | .fault f => faultToRefOutcome f) := by
      simp only [refStep, hlt, anneal_corresponds_to_miri] <;> rfl
    rw [hstep]
    cases annealStep p st with
    | running st' =>
      have hk : k + (n + 1) = (k + 1) + n := by omega
      simp only
      rw [hk]; exact refRunFuel_encode p n (k + 1) st'
    | returned b => rfl
    | panicked => rfl
    | fault f => cases f <;> rfl

/-- **Whole-program behavioral equivalence** (`deinitMoves = true`): for every
program, argument vector and step budget, `M_ref` on `encodeProg p` and
`M_anneal` on `p` produce the same observation. -/
theorem refObs_encodeProg (p : V2026Prog) (args : List Bytes) (n : Nat) :
    refObs true (encodeProg p) args n = annealObs p args n := by
  simp only [refObs, annealObs, refInit_encodeProg]
  cases annealInit p args with
  | error f => cases f <;> rfl
  | ok st =>
    simp only
    have := refRunFuel_encode p n 0 st
    simp only [Nat.zero_add] at this
    exact this

/-- **Bidirectional fault equivalence**: `M_anneal` reaches fault `f` iff
`M_ref` (`deinitMoves = true`) reaches the corresponding `.ub` / `.blocked`
outcome under some step budget. -/
theorem reachesResult_fault_iff_refReachesOutcome (p : V2026Prog) (args : List Bytes)
    (f : Fault) :
    (∃ n, annealObs p args n = faultObs f) ↔
      (∃ maxSteps, refObs true (encodeProg p) args maxSteps = faultObs f) := by
  simp only [refObs_encodeProg]

/-- Forward simulation of terminal behavior. -/
theorem behavior_transfer (p : V2026Prog) (args : List Bytes) (n : Nat) (v : Option Nat)
    (len : Nat) (h : annealObs p args n = .returned v len) :
    refObs true (encodeProg p) args n = .returned v len := by
  rw [refObs_encodeProg]; exact h

/-- `SimulationInv` is a bijection (for fixed step counters) that is preserved
in both directions by every step (`deinitMoves = true`). -/
theorem simulationInv_bijective (p : V2026Prog) : SimulationInvBijective p := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro s s' rs h₁ h₂; exact h₁.symm.trans h₂
  · intro s rs rs' h₁ h₂ h₃ h₄
    cases rs; cases rs'; simp only [SimulationInv] at h₁ h₂ h₃ h₄; subst h₁ h₂ h₃ h₄; rfl
  · intro s k m; exact ⟨⟨s, k, m⟩, rfl, rfl, rfl⟩
  · intro s rs s' h hlt hs
    have hb : Nat.blt rs.stepsExecuted rs.maxSteps = true := Nat.blt_eq.mpr hlt
    refine ⟨⟨s', rs.stepsExecuted + 1, rs.maxSteps⟩, ?_, rfl⟩
    simp only [refStep, hb, anneal_corresponds_to_miri, SimulationInv] at h ⊢
    rw [h, hs]
  · intro s rs rs' h hr
    simp only [refStep, SimulationInv] at h hr
    cases hb : Nat.blt rs.stepsExecuted rs.maxSteps with
    | false => rw [hb] at hr; cases hr
    | true =>
      rw [hb] at hr; simp only [anneal_corresponds_to_miri, h] at hr
      cases hs : annealStep p s <;> rw [hs] at hr <;> simp only at hr
      · cases hr; rfl
      · cases hr
      · cases hr
      · rename_i f; cases f <;> cases hr

/-- Run a strategy variant of `M_ref` (no budget) for at most `fuel` steps. -/
def refRunWith (S : OperandStrategy) (rp : RefProg) : Nat → PState → StepOut
  | 0, st => .running st
  | n + 1, st =>
    match refStepCoreWith S rp st with
    | .running st' => refRunWith S rp n st'
    | o => o

/-- Observation of a strategy variant of `M_ref`. -/
def refObsWith (S : OperandStrategy) (rp : RefProg) (args : List Bytes) (fuel : Nat) : Obs :=
  match refInit rp args with
  | .error (.ub why) => .ub why
  | .error .unsupported => .unsupported
  | .ok st => stepOutObs (refRunWith S rp fuel st)

/-! ## Canary programs (real `V2026_06_01` bodies)

Every canary is a real `CapturedMir` (`runtimePostCleanup`, real
`LocalDecl`/`Ty`/`LayoutTable`, layouts synthesized by Trusted's
`RigidTy.computeLayout`), executed by `M_anneal` and by `M_ref` on
`encodeProg p`. The programs used by the falsification witnesses below live
here; the `D1`–`D9` canary theorems live in
`Anneal.Mir.Correspondence.Canaries`. -/

/-- Fallback layout (never used by the canaries: every layout synthesizes). -/
def fallbackLayout : TypeLayout :=
  { size := ⟨0⟩, align := ⟨1⟩, backendRepr := .memory, fields := .primitive,
    variants := .single 0, isUninhabited := false }

/-- Synthesized `x86_64` layout of a kind. -/
def lay (k : RigidTy) : TypeLayout := (pointeeLayoutOf 64 k).getD fallbackLayout

def kU8 : RigidTy := .uint .u8
def kPair : RigidTy := .tuple [kU8, kU8]
def kArr4 : RigidTy := .array kU8 4
def kArr2 : RigidTy := .array kU8 2
def kMaybeUninit : RigidTy := .adt "core::mem::MaybeUninit" [kU8]

/-- The canaries' compiler layout table (`x86_64`). -/
def canaryLayouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true
    entries := [lay (.tuple []), lay kU8, lay .bool, lay kPair, lay kArr4,
      lay (.rawPtr .mut kU8), lay (.ref .not kU8), lay (.uint .usize), lay kArr2,
      lay (.fnDef "callee" []), lay (.fnDef "unresolved" []), lay kMaybeUninit,
      lay (.fnDef "panicky" [])] }

def tUnit : Ty := ⟨.tuple [], 0⟩
def tU8 : Ty := ⟨kU8, 1⟩
def tBool : Ty := ⟨.bool, 2⟩
def tPair : Ty := ⟨kPair, 3⟩
def tArr4 : Ty := ⟨kArr4, 4⟩
def tRaw : Ty := ⟨.rawPtr .mut kU8, 5⟩
def tRef : Ty := ⟨.ref .not kU8, 6⟩
def tArr2 : Ty := ⟨kArr2, 8⟩
def tFnCallee : Ty := ⟨.fnDef "callee" [], 9⟩
def tFnUnresolved : Ty := ⟨.fnDef "unresolved" [], 10⟩
def tMU : Ty := ⟨kMaybeUninit, 11⟩
def tFnPanicky : Ty := ⟨.fnDef "panicky" [], 12⟩

/-- A canary body. -/
def mkBody (path : DefPath) (argCount : Nat) (locals : List Ty) (blocks : List BasicBlockData) :
    CapturedMir :=
  { defPath := path, phase := .runtimePostCleanup, role := .subject, argCount := argCount
    localDecls := locals.map (fun ty => ⟨.mut, ty, none⟩), basicBlocks := blocks
    fnAbi := ⟨[], ⟨lay (.tuple []), .ignore⟩, .rust, true⟩, layouts := canaryLayouts
    allocations := [] }

def stmt (k : StatementKind) : Statement := ⟨k, ""⟩
def asg (dst : Place) (rv : Rvalue) : Statement := stmt (.assign dst rv)
def blk (ss : List Statement) (t : TerminatorKind) (cleanup : Bool := false) : BasicBlockData :=
  ⟨ss, ⟨t, ""⟩, cleanup⟩
def loc (l : Nat) : Place := ⟨l, []⟩
def fld (l i : Nat) (ty : Ty) : Place := ⟨l, [.field i ty]⟩
def drf (l : Nat) : Place := ⟨l, [.deref]⟩
def cU8 (n : Nat) : Operand := .constant ⟨tU8, .scalar (.int ⟨n, 1⟩)⟩
def cBool (b : Bool) : Operand := .constant ⟨tBool, .scalar (.int ⟨if b then 1 else 0, 1⟩)⟩
def cUnit : Operand := .constant ⟨tUnit, .zeroSized⟩
def prog1 (b : CapturedMir) : V2026Prog := ⟨[b], 0⟩

/-- Both machines on one program: `M_anneal` and `M_ref` (`deinitMoves = true`). -/
def bothObs (p : V2026Prog) : Obs × Obs :=
  (annealObs p [] 40, refObs true (encodeProg p) [] 40)

/-- `D1`: `_1 = 7; _2 = move _1; _0 = copy _1`. -/
def d1MoveThenRead : V2026Prog := prog1 <| mkBody "d1" 0 [tU8, tU8, tU8]
  [blk [asg (loc 1) (.use (cU8 7)), asg (loc 2) (.use (.move (loc 1))),
        asg (loc 0) (.use (.copy (loc 1)))] .return_]

/-- `D3`: move then re-initialize. -/
def d3Prog : V2026Prog := prog1 <| mkBody "d3" 0 [tU8, tU8, tU8]
  [blk [asg (loc 1) (.use (cU8 5)), asg (loc 2) (.use (.move (loc 1))),
        asg (loc 1) (.use (cU8 99)), asg (loc 0) (.use (.copy (loc 1)))] .return_]

/-- `D5`: `_1 = 5; _3 = &_1; _2 = &raw mut _1; <s>; _0 = <rv>`. -/
def d5Prog (s : Statement) (rv : Rvalue) : V2026Prog := prog1 <| mkBody "d5" 0
  [tU8, tU8, tRaw, tRef, tU8]
  [blk [asg (loc 1) (.use (cU8 5)), asg (loc 3) (.ref .shared (loc 1)),
        asg (loc 2) (.rawPtr .mut (loc 1)), s, asg (loc 0) rv] .return_]

/-- `D7` callee: reads through the raw pointer `_2`. -/
def d7Callee : CapturedMir := mkBody "callee" 2 [tU8, tU8, tRaw]
  [blk [asg (loc 0) (.use (.copy (drf 2)))] .return_]

/-- `D7`: `_1 = 5; _2 = &raw mut _1; _0 = callee(arg, copy _2)`. -/
def d7Prog (arg : Operand) : V2026Prog := ⟨[mkBody "caller" 0 [tU8, tU8, tRaw]
  [blk [asg (loc 1) (.use (cU8 5)), asg (loc 2) (.rawPtr .mut (loc 1))]
     (.call (.constant ⟨tFnCallee, .zeroSized⟩) [arg, .copy (loc 2)] (loc 0) (some 1) .continue_),
   blk [] .return_], d7Callee], 0⟩

/-- `D7` with an unresolved callee. -/
def d7Unresolved (arg : Operand) : V2026Prog := prog1 <| mkBody "caller" 0 [tU8, tU8]
  [blk [] (.call (.constant ⟨tFnUnresolved, .zeroSized⟩) [arg] (loc 0) (some 1) .continue_),
   blk [] .return_]

/-! ## Part 8 — Falsification witnesses (non-vacuity / mutant separation) -/

/-- `MaybeUninit<u8>` byte copy after a move: no UB in either machine at the
copy, but the copied bytes differ, so a later typed read separates them. -/
def maybeUninitProg : V2026Prog := prog1 <| mkBody "mu" 0 [tU8, tMU, tMU, tMU]
  [blk [asg (loc 1) (.aggregate (.adt "core::mem::MaybeUninit" 0 none) [cU8 42]),
        asg (loc 2) (.use (.move (loc 1))),
        asg (loc 3) (.use (.copy (loc 1))),
        asg (loc 0) (.use (.copy (fld 3 0 tU8)))] .return_]

/-- **`deinitMoves = false` breaks the correspondence**: on use-after-move
(`D1`) and on a `MaybeUninit` byte copy, upstream `lean-miri` (moves are copies)
returns a value where `M_anneal` faults. -/
theorem correspondence_fails_when_deinitMoves_false :
    annealObs d1MoveThenRead [] 40 = .ub .invalidUninitBytes ∧
    refObs false (encodeProg d1MoveThenRead) [] 40 = .returned (some 7) 1 ∧
    annealObs maybeUninitProg [] 40 = .ub .invalidUninitBytes ∧
    refObs false (encodeProg maybeUninitProg) [] 40 = .returned (some 42) 1 ∧
    refObs true (encodeProg maybeUninitProg) [] 40 = .ub .invalidUninitBytes := by
  decide

/-- Hence no `deinitMoves = false` analogue of `refObs_encodeProg` exists. -/
theorem no_correspondence_when_deinitMoves_false :
    ¬ ∀ (p : V2026Prog) (args : List Bytes) (n : Nat),
      refObs false (encodeProg p) args n = annealObs p args n := by
  intro h
  have := h d1MoveThenRead [] 40
  rw [correspondence_fails_when_deinitMoves_false.1,
    correspondence_fails_when_deinitMoves_false.2.1] at this
  cases this

/-- The program `_1 = 5; _3 = &_1; _2 = &raw mut _1; _4 = move (*_2); _0 = _4`. -/
def d5MoveDeliver : V2026Prog :=
  d5Prog (asg (loc 4) (.use (.move (drf 2)))) (.use (.copy (loc 4)))

/-- **Eager indirect deinit is falsified**: deinitializing the `.indirect
mplace` inside `evalOperand` (before `readImmediate` /
`copyRuntimePlaceNoValidate`) turns a valid indirect move into a spurious
`invalidUninitBytes` fault. -/
theorem eager_indirect_deinit_falsified :
    annealObs d5MoveDeliver [] 40 = .returned (some 5) 1 ∧
    refObs true (encodeProg d5MoveDeliver) [] 40 = .returned (some 5) 1 ∧
    refObsWith eagerInEvalOperandStrategy (encodeProg d5MoveDeliver) [] 40 =
      .ub .invalidUninitBytes := by
  decide

theorem eagerInEvalOperandStrategy_ne_eager : eagerInEvalOperandStrategy ≠ eagerStrategy := by
  intro h
  have h1 := eager_indirect_deinit_falsified.2.2
  have h2 := eager_indirect_deinit_falsified.2.1
  rw [h] at h1
  have e : refObsWith eagerStrategy (encodeProg d5MoveDeliver) [] 40 =
      refObs true (encodeProg d5MoveDeliver) [] 40 := by decide
  rw [e, h2] at h1
  cases h1

/-- The `D7` caller state just before the call (`_1` in memory, `_2 = &raw mut _1`). -/
def d7PreCallState : Option PState :=
  match annealInit (d7Prog (.move (loc 1))) [] with
  | .ok st =>
    match annealRun (d7Prog (.move (loc 1))) 2 st with
    | .running st' => some st'
    | _ => none
  | .error _ => none

def d7ArgOps : List SemOperand :=
  [.move ⟨1, (kU8, lay kU8), []⟩, .copy ⟨2, (.rawPtr .mut kU8, lay (.rawPtr .mut kU8)), []⟩]

/-- Is `_1`'s memory (allocation `a`, 1 byte) still initialized? -/
def byteInit (st : PState) (a : Nat) : Bool :=
  match heapGet st a with
  | some [AbstractByte.init _ _] => true
  | _ => false

def argsKeepSource (r : Except Fault (List Bytes × PState)) : Bool :=
  match r with
  | .ok (_, st) => byteInit st 0
  | .error _ => false

/-- **`kani#5172` call-argument ordering**: consuming each argument right after
its `evalOperand` (as `M_ref` does) deinitializes the moved argument, whereas
batching all `evalOperand`s before consumption lets the second argument's
`evalOperand` clobber the single-Boolean `pendingMoveDeinit` latch, so the
moved argument stays initialized (a missed use-after-move). -/
theorem batched_call_args_lose_move_deinit :
    (d7PreCallState.map fun st =>
      argsKeepSource (readOperands (twoPhaseStrategy true) 64 st d7ArgOps)) = some false ∧
    (d7PreCallState.map fun st =>
      argsKeepSource (readOperandsBatched true 64 st d7ArgOps)) = some true := by
  decide

/-! ### Upstream LeanMiri call-argument path (`Miri/Interpreter/Call.lean`)

A faithful model of `Call.evalCalleeAndArgs` + `Call.passArgument` under the
6-file `d9b41b58b` patch (which does not touch `Call.lean`):

* `evalFnCallArgumentAt` (`Call.lean:164-175`) sends `.Copy` / `.Constant`
  through the patched `evalOperandAt`, which yields a *lazy* `OpTy`
  (`FnArg.Copy`). It sends `.Move place` through `evalPlace` + `placeToOp`
  without calling `evalOperand`. If the move places and the destination are
  `moveDefinitelyDisjoint`, an indirect place becomes `FnArg.InPlace` and an
  immediate becomes `FnArg.Copy`, with **no deinit**. Otherwise the place is
  force-allocated and passed `InPlace`.
* `evalCallTerminator` evaluates the destination place first, then *all*
  arguments, then (`initFnCall`) runs `passArgument` per argument. The copy is
  `copyAllowTransmute` (the lazy read). It is followed, for `InPlace`
  arguments, by `protectArgument` =
  `TypedRetag.protectInPlaceFunctionArgument`, which ends in
  `writeUninit place` (Miri `machine.rs`
  `protect_in_place_function_argument`). The protector retag is not modeled;
  the uninit write is modeled as a Tree Borrows write (`storeMPlace`). -/

/-- `Miri.Interpreter.Call.FnArg`. -/
inductive FnArgM : Type where
  | copyOp (o : OpTy) (ty : SemTy)
  | inPlace (mp : MPlace) (ty : SemTy)

def localsDistinct : List Local → Bool
  | [] => true
  | l :: ls => !(ls.contains l) && localsDistinct ls

/-- `Call.moveDefinitelyDisjoint`: move-argument places and the destination
have pairwise distinct locals and no leading `Deref`. -/
def moveDefinitelyDisjoint (args : List SemOperand) (dest : SemPlace) : Bool :=
  let places := args.filterMap (fun a => match a with | .move p => some p | _ => none) ++ [dest]
  places.all (fun p => match p.projs with | .deref :: _ => false | _ => true) &&
    localsDistinct (places.map SemPlace.local_)

/-- `Call.evalFnCallArgumentAt` (patched `evalOperandAt` for non-moves). -/
def leanMiriEvalFnCallArg (pb : Nat) (disjoint : Bool) (st : PState) :
    SemOperand → Except Fault (FnArgM × PState)
  | .move p =>
    match disjoint with
    | true =>
      match evalPlaceToOp pb st p with
      | .error e => .error e
      | .ok (.indirect mp, ty) => .ok (.inPlace mp ty, st)
      | .ok (.immediate b, ty) => .ok (.copyOp (.immediate b) ty, st)
    | false =>
      match placeToMPlace pb st p with
      | .error e => .error e
      | .ok (mp, st₁) =>
        match evalPlaceToOp pb st₁ p with
        | .error e => .error e
        | .ok (_, ty) => .ok (.inPlace mp ty, st₁)
  | op =>
    match refEvalOperand true pb st op with
    | .error e => .error e
    | .ok (o, ty, st₁) => .ok (.copyOp o ty, st₁)

def leanMiriEvalFnCallArgs (pb : Nat) (disjoint : Bool) :
    PState → List SemOperand → Except Fault (List FnArgM × PState)
  | st, [] => .ok ([], st)
  | st, op :: ops =>
    match leanMiriEvalFnCallArg pb disjoint st op with
    | .error e => .error e
    | .ok (fa, st₁) =>
      match leanMiriEvalFnCallArgs pb disjoint st₁ ops with
      | .error e => .error e
      | .ok (fas, st₂) => .ok (fa :: fas, st₂)

/-- `Call.passArgument` for every argument, in order: the (lazy) copy, then the
in-place protection's `writeUninit` (`TypedRetag.lean:201` →
`TypedMachineBindings.lean:17` `PlaceMachine.writeMemory access (fun _ => false)
.uninit`, which runs `accessHooks.beforeMemoryWrite`, i.e. a Tree Borrows
`.Write` via `storeMPlace`). -/
def leanMiriPassArgs : PState → List FnArgM → Except Fault (List Bytes × PState)
  | st, [] => .ok ([], st)
  | st, .copyOp o ty :: rest =>
    match refReadImmediate true st o ty with
    | .error e => .error e
    | .ok (b, st₁) =>
      match leanMiriPassArgs st₁ rest with
      | .error e => .error e
      | .ok (bs, st₂) => .ok (b :: bs, st₂)
  | st, .inPlace mp ty :: rest =>
    match loadMPlace st mp with
    | .error e => .error e
    | .ok (b, st₁) =>
      match checkValid ty b with
      | .error e => .error e
      | .ok () =>
        match storeMPlace st₁ mp (uninitBytes mp.size) with
        | .error e => .error e
        | .ok st₂ =>
          match leanMiriPassArgs st₂ rest with
          | .error e => .error e
          | .ok (bs, st₃) => .ok (b :: bs, st₃)

/-- In upstream `Call.lean`, `evalCalleeAndArgs` (`Call.lean:181-206`) runs
`evalFnCallArgumentAt` on all arguments (producing `FnArg` handles without
reading/validating bytes) and then resolves the callee via `h.resolve`
(`Call.lean:199`) *before* `initStackFrame` runs `passArgument` (`Call.lean:221`).
Thus an unresolved callee (`callee = none`) fails with `.unsupported` before
`leanMiriPassArgs` ever reads or validates the argument bytes. -/
def leanMiriCallArgsUpstream (pb : Nat) (st : PState) (callee : Option Nat)
    (args : List SemOperand) (dest : SemPlace) : Except Fault (List Bytes × PState) :=
  match leanMiriEvalFnCallArgs pb (moveDefinitelyDisjoint args dest) st args with
  | .error e => .error e
  | .ok (fas, st₁) =>
    match callee with
    | none => .error .unsupported
    | some _ => leanMiriPassArgs st₁ fas

/-- `M_ref` with the *unpatched* `Call.lean` argument path (everything else as
patched by `d9b41b58b`). -/
def leanMiriUpstreamCallStrategy : OperandStrategy :=
  { readOperand := twoPhaseReadOperand true, assignUse := twoPhaseAssignUse true,
    callArgs := leanMiriCallArgsUpstream }

def tFnCalleeImm : Ty := ⟨.fnDef "calleeImm" [], 9⟩

/-- `_1 = 5; _2 = calleeImm(move _1); _0 = copy _1` with `_1` an immediate
(never borrowed) local. -/
def d7ImmProg : V2026Prog := ⟨[mkBody "caller" 0 [tU8, tU8, tU8]
  [blk [asg (loc 1) (.use (cU8 5))]
     (.call (.constant ⟨tFnCalleeImm, .zeroSized⟩) [.move (loc 1)] (loc 2) (some 1) .continue_),
   blk [asg (loc 0) (.use (.copy (loc 1)))] .return_],
  mkBody "calleeImm" 1 [tU8, tU8] [blk [asg (loc 0) (.use (.copy (loc 1)))] .return_]], 0⟩

/-- Same-call `move _1` followed by `copy _1`: `_1 = 5; _0 = calleeAdd(move _1, copy _1)`.
Because `moveDefinitelyDisjoint` (`Call.lean:156-157`) only collects `.Move`
places and ignores `.Copy` places, `disjoint = true`, so unpatched `Call.lean`
fails to deinitialize `_1` on arg 0 and lets arg 1 (`copy _1`) read `5` in the
same call. -/
def d7MoveThenCopySameCallProg : V2026Prog := ⟨[mkBody "caller" 0 [tU8, tU8]
  [blk [asg (loc 1) (.use (cU8 5))]
     (.call (.constant ⟨tFnCalleeImm, .zeroSized⟩) [.move (loc 1), .copy (loc 1)] (loc 0) (some 1)
       .continue_),
   blk [] .return_],
  mkBody "calleeImm" 2 [tU8, tU8, tU8]
    [blk [asg (loc 0) (.binaryOp .add (.copy (loc 1)) (.copy (loc 2)))] .return_]], 0⟩

/-- `_1 = 5; _3 = &_1; _2 = &raw mut _1; _4 = calleeImm(move (*_2)); _0 = copy (*_3)`.
Because `.move (drf 2)` has a leading `.deref`, `moveDefinitelyDisjoint` is
`false` (`Call.lean:160`), so `move (*_2)` is passed `.InPlace`. In `M_anneal`
and `M_ref`, moving `*_2` into the call preserves the sibling `.frozen` borrow
`_3` (reading `*_3` passes Tree Borrows and faults on `.invalidUninitBytes`),
whereas `protectInPlaceFunctionArgument`'s `writeUninit` (`TypedRetag.lean:201`
→ `PlaceMachine.writeMemory`) performs a foreign Tree Borrows `.Write` through
`_2`'s tag that disables `_3` (`.ub .treeBorrows`). -/
def d7MoveDerefSiblingFrozenProg : V2026Prog := ⟨[mkBody "caller" 0
  [tU8, tU8, tRaw, tRef, tU8]
  [blk [asg (loc 1) (.use (cU8 5)), asg (loc 3) (.ref .shared (loc 1)),
        asg (loc 2) (.rawPtr .mut (loc 1))]
     (.call (.constant ⟨tFnCalleeImm, .zeroSized⟩) [.move (drf 2)] (loc 4) (some 1) .continue_),
   blk [asg (loc 0) (.use (.copy (drf 3)))] .return_],
  mkBody "calleeImm" 1 [tU8, tU8] [blk [asg (loc 0) (.use (.copy (loc 1)))] .return_]], 0⟩

theorem call_inPlace_writeUninit_disables_sibling_frozen :
    annealObs d7MoveDerefSiblingFrozenProg [] 40 = .ub .invalidUninitBytes ∧
    refObs true (encodeProg d7MoveDerefSiblingFrozenProg) [] 40 = .ub .invalidUninitBytes ∧
    refObsWith leanMiriUpstreamCallStrategy (encodeProg d7MoveDerefSiblingFrozenProg) [] 40 =
      .ub .treeBorrows := by
  decide

/-- **The 7th-file requirement, stated precisely.**
(1) On `D7` (the moved argument `_1` is memory-backed because `_2 = &raw mut
_1`), the unpatched `Call.lean` path *agrees* with `M_anneal`: the `InPlace`
argument is deinitialized by `protectInPlaceFunctionArgument` before the callee
runs, so the callee's raw-pointer read is UB.
(2) The genuine divergences of unpatched `Call.lean` are:
    (a) in `d7ImmProg`, a moved immediate argument is still readable in the
        caller after the call returns (`5` vs UB);
    (b) in `d7MoveThenCopySameCallProg`, `call f(move _1, copy _1)` has
        `moveDefinitelyDisjoint = true` (because `moveDefinitelyDisjoint`
        ignores `.Copy` arguments), so `copy _1` in the same call reads `5` and
        returns `10` instead of faulting with `.ub .invalidUninitBytes`;
    (c) in `d7Unresolved (.move (loc 1))` (`kani#5172` invariant), `evalCalleeAndArgs`
        (`Call.lean:186-199`) resolves the callee *after* `evalFnCallArgumentAt`
        (which only forms `FnArg` handles without reading/validating bytes) and
        *before* `passArgument`, reporting `.unsupported` instead of
        `.ub .invalidUninitBytes`. -/
theorem call_move_arg_upstream_call_path :
    annealObs (d7Prog (.move (loc 1))) [] 40 = .ub .invalidUninitBytes ∧
    refObsWith leanMiriUpstreamCallStrategy (encodeProg (d7Prog (.move (loc 1)))) [] 40 =
      .ub .invalidUninitBytes ∧
    annealObs d7ImmProg [] 40 = .ub .invalidUninitBytes ∧
    refObs true (encodeProg d7ImmProg) [] 40 = .ub .invalidUninitBytes ∧
    refObsWith leanMiriUpstreamCallStrategy (encodeProg d7ImmProg) [] 40 = .returned (some 5) 1 ∧
    refObsWith leanMiriUpstreamCallStrategy (encodeProg d7MoveThenCopySameCallProg) [] 40 =
      .returned (some 10) 1 ∧
    refObsWith leanMiriUpstreamCallStrategy (encodeProg (d7Unresolved (.move (loc 1)))) [] 40 =
      .unsupported := by
  decide

/-- Hence the unpatched call path is not the reference strategy. -/
theorem leanMiriUpstreamCallStrategy_ne_eager : leanMiriUpstreamCallStrategy ≠ eagerStrategy := by
  intro h
  have h1 := call_move_arg_upstream_call_path.2.2.2.2.1
  rw [h] at h1
  have e : refObsWith eagerStrategy (encodeProg d7ImmProg) [] 40 =
      refObs true (encodeProg d7ImmProg) [] 40 := by decide
  rw [e, call_move_arg_upstream_call_path.2.2.2.1] at h1
  cases h1

/-! ## Part 9 — Tree Borrows: moving out of `*ptr` is not a write -/

theorem setLocalE_borrows {st st' : PState} {l : Local} {v : PSlot}
    (h : setLocalE st l v = .ok st') : st'.borrows = st.borrows := by
  unfold setLocalE at h
  cases hf : st.frames with
  | nil => rw [hf] at h; cases h
  | cons fr rest =>
    rw [hf] at h; simp only at h
    cases hs : setNth? fr.locals l v with
    | none => rw [hs] at h; cases h
    | some ls => rw [hs] at h; cases h; rfl

theorem putHeap_borrows {st st' : PState} {a : Nat} {b : Bytes}
    (h : putHeap st a b = .ok st') : st'.borrows = st.borrows := by
  unfold putHeap at h
  cases hs : setNth? st.heap a (some b) with
  | none => rw [hs] at h; cases h
  | some hp => rw [hs] at h; cases h; rfl

theorem deinitMPlaceRaw_borrows {st st' : PState} {mp : MPlace}
    (h : deinitMPlaceRaw st mp = .ok st') : st'.borrows = st.borrows := by
  unfold deinitMPlaceRaw at h
  cases hg : heapGet st mp.alloc with
  | none => rw [hg] at h; cases h
  | some b =>
    rw [hg] at h; simp only at h
    cases hb : Nat.ble (mp.offset + mp.size) b.length with
    | false => rw [hb] at h; cases h
    | true => rw [hb] at h; exact putHeap_borrows h

/-- A Tree Borrows **read** never changes a `.frozen` node (child or foreign). -/
theorem treeBorrowNodeAccess_read_frozen (rel : TreeBorrowRelatedness) :
    treeBorrowNodeAccess .read rel .frozen false = .transition .frozen := by
  cases rel <;> rfl

theorem tbAccessAux_read_preserves_frozen (all : List BorrowEntry) (a : Nat) (tag : Option Nat)
    (off len : Nat) :
    ∀ (es es' : List BorrowEntry), tbAccessAux .read all a tag off len es = some es' →
      ∀ i e, nth? es i = some e → e.perm = .frozen →
        ∃ e', nth? es' i = some e' ∧ e'.tag = e.tag ∧ e'.perm = .frozen
  | [], _, _, i, e, hi, _ => by simp [nth?] at hi
  | x :: xs, es', h, i, e, hi, hf => by
    simp only [tbAccessAux] at h
    cases hr : tbAccessAux .read all a tag off len xs with
    | none => rw [hr] at h; cases h
    | some xs' =>
      rw [hr] at h; simp only at h
      cases i with
      | succ j =>
        simp only [nth?] at hi
        obtain ⟨e', h1, h2, h3⟩ :=
          tbAccessAux_read_preserves_frozen all a tag off len xs xs' hr j e hi hf
        cases hc : (Nat.beq x.targetLocal a && byteRangesOverlapBool x.rangeOffset x.rangeLen off len) <;>
          rw [hc] at h <;> simp only at h
        · cases h; exact ⟨e', h1, h2, h3⟩
        · cases hub : treeBorrowTransitionIsUB
              (treeBorrowNodeAccess .read (tbRelatedness all tag x) x.perm false) <;>
            rw [hub] at h <;> simp only at h
          · cases h; exact ⟨e', h1, h2, h3⟩
          · cases h
      | zero =>
        simp only [nth?, Option.some.injEq] at hi; subst hi
        cases hc : (Nat.beq x.targetLocal a && byteRangesOverlapBool x.rangeOffset x.rangeLen off len) <;>
          rw [hc] at h <;> simp only at h
        · cases h; exact ⟨x, rfl, rfl, hf⟩
        · rw [hf, treeBorrowNodeAccess_read_frozen] at h
          simp only [treeBorrowTransitionIsUB] at h
          cases h
          exact ⟨_, rfl, rfl, rfl⟩

theorem loadMPlace_preserves_frozen {st st' : PState} {mp : MPlace} {b : Bytes}
    (h : loadMPlace st mp = .ok (b, st')) :
    ∀ i e, nth? st.borrows i = some e → e.perm = .frozen →
      ∃ e', nth? st'.borrows i = some e' ∧ e'.tag = e.tag ∧ e'.perm = .frozen := by
  unfold loadMPlace at h
  cases hg : heapGet st mp.alloc with
  | none => rw [hg] at h; cases h
  | some bs =>
    rw [hg] at h; simp only at h
    cases hb : Nat.ble (mp.offset + mp.size) bs.length with
    | false => rw [hb] at h; cases h
    | true =>
      rw [hb] at h; simp only at h
      cases ht : tbAccess .read st.borrows mp.alloc mp.tag mp.offset mp.size with
      | none => rw [ht] at h; cases h
      | some bs' =>
        rw [ht] at h; simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨_, rfl⟩ := h
        exact tbAccessAux_read_preserves_frozen _ _ _ _ _ _ _ ht

/-- **`deinitMovedPlace_preserves_tb_tags`**: evaluating `Operand.move p`
(in particular `move (*ptr)`) through the two-phase protocol leaves the Tree
Borrows table *exactly* as the corresponding `Operand.copy p` (a pure read)
does, so every `.frozen` tag — e.g. a sibling shared borrow — stays
`.frozen`; only the moved bytes become `.uninit`. -/
theorem deinitMovedPlace_preserves_tb_tags (pb : Nat) (st : PState) (p : SemPlace) (b : Bytes)
    (st₁ : PState) (h : twoPhaseReadOperand true pb st (.move p) = .ok (b, st₁)) :
    (∃ st₂, twoPhaseReadOperand true pb st (.copy p) = .ok (b, st₂) ∧ st₂.borrows = st₁.borrows) ∧
    (∀ i e, nth? st.borrows i = some e → e.perm = .frozen →
      ∃ e', nth? st₁.borrows i = some e' ∧ e'.tag = e.tag ∧ e'.perm = .frozen) := by
  rw [twoPhaseReadOperand_true_eq] at h ⊢
  simp only [annealReadOperand] at h ⊢
  cases he : evalPlaceToOp pb (clearLatch st) p with
  | error e => rw [he] at h; cases h
  | ok r =>
    obtain ⟨o, ty⟩ := r
    rw [he] at h
    cases o with
    | immediate bb =>
      simp only at h
      cases hp : p.projs with
      | cons _ _ => rw [hp] at h; cases h
      | nil =>
        rw [hp] at h; simp only at h
        cases hs : setLocalE (clearLatch st) p.local_ (.imm (uninitBytes bb.length)) with
        | error e => rw [hs] at h; cases h
        | ok st₃ =>
          rw [hs] at h; simp only at h
          cases hv : checkValid ty bb with
          | error e => rw [hv] at h; cases h
          | ok u =>
            rw [hv] at h; simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            have hb3 := setLocalE_borrows hs
            refine ⟨⟨clearLatch st, by simp [readOpBytes, hv], ?_⟩, ?_⟩
            · simp only [clearLatch]; exact hb3.symm
            · intro i e hi hf
              refine ⟨e, ?_, rfl, hf⟩
              show nth? st₃.borrows i = some e
              rw [hb3]; exact hi
    | indirect mp =>
      simp only at h
      cases hl : loadMPlace (clearLatch st) mp with
      | error e => rw [hl] at h; cases h
      | ok r' =>
        obtain ⟨bb, st₃⟩ := r'
        rw [hl] at h; simp only at h
        cases hv : checkValid ty bb with
        | error e => rw [hv] at h; cases h
        | ok u =>
          rw [hv] at h; simp only at h
          cases hd : deinitMPlaceRaw st₃ mp with
          | error e => rw [hd] at h; cases h
          | ok st₄ =>
            rw [hd] at h; simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            have hb4 := deinitMPlaceRaw_borrows hd
            refine ⟨⟨st₃, by simp [readOpBytes, hl, hv], hb4.symm⟩, ?_⟩
            intro i e hi hf
            obtain ⟨e', h1, h2, h3⟩ := loadMPlace_preserves_frozen hl i e hi hf
            exact ⟨e', by rw [hb4]; exact h1, h2, h3⟩

/-- A `.frozen` entry is left *literally unchanged* by any Tree Borrows read. -/
theorem tbAccessAux_read_frozen_unchanged (all : List BorrowEntry) (a : Nat) (tag : Option Nat)
    (off len : Nat) :
    ∀ (es es' : List BorrowEntry), tbAccessAux .read all a tag off len es = some es' →
      ∀ i e, nth? es i = some e → e.perm = .frozen → nth? es' i = some e
  | [], _, _, i, e, hi, _ => by simp [nth?] at hi
  | x :: xs, es', h, i, e, hi, hf => by
    simp only [tbAccessAux] at h
    cases hr : tbAccessAux .read all a tag off len xs with
    | none => rw [hr] at h; cases h
    | some xs' =>
      rw [hr] at h; simp only at h
      cases i with
      | succ j =>
        simp only [nth?] at hi
        have ih := tbAccessAux_read_frozen_unchanged all a tag off len xs xs' hr j e hi hf
        cases hc : (Nat.beq x.targetLocal a && byteRangesOverlapBool x.rangeOffset x.rangeLen off len) <;>
          rw [hc] at h <;> simp only at h
        · cases h; exact ih
        · cases hub : treeBorrowTransitionIsUB
              (treeBorrowNodeAccess .read (tbRelatedness all tag x) x.perm false) <;>
            rw [hub] at h <;> simp only at h
          · cases h; exact ih
          · cases h
      | zero =>
        simp only [nth?, Option.some.injEq] at hi; subst hi
        cases hc : (Nat.beq x.targetLocal a && byteRangesOverlapBool x.rangeOffset x.rangeLen off len) <;>
          rw [hc] at h <;> simp only at h
        · cases h; rfl
        · rw [hf, treeBorrowNodeAccess_read_frozen] at h
          simp only [treeBorrowTransitionIsUB] at h
          cases h
          cases x; simp only at hf; subst hf; rfl

/-- Entries not overlapping an access window are left *literally unchanged*
by any Tree Borrows access (read or write). -/
theorem tbAccessAux_nonoverlap_unchanged (kind : TreeBorrowAccessKind) (all : List BorrowEntry)
    (a : Nat) (tag : Option Nat) (off len : Nat) :
    ∀ (es es' : List BorrowEntry), tbAccessAux kind all a tag off len es = some es' →
      ∀ i e, nth? es i = some e →
        (Nat.beq e.targetLocal a && byteRangesOverlapBool e.rangeOffset e.rangeLen off len) = false →
        nth? es' i = some e
  | [], _, _, i, e, hi, _ => by simp [nth?] at hi
  | x :: xs, es', h, i, e, hi, hno => by
    simp only [tbAccessAux] at h
    cases hr : tbAccessAux kind all a tag off len xs with
    | none => rw [hr] at h; cases h
    | some xs' =>
      rw [hr] at h; simp only at h
      cases i with
      | succ j =>
        simp only [nth?] at hi
        have ih := tbAccessAux_nonoverlap_unchanged kind all a tag off len xs xs' hr j e hi hno
        cases hc : (Nat.beq x.targetLocal a && byteRangesOverlapBool x.rangeOffset x.rangeLen off len) <;>
          rw [hc] at h <;> simp only at h
        · cases h; exact ih
        · cases hub : treeBorrowTransitionIsUB
              (treeBorrowNodeAccess kind (tbRelatedness all tag x) x.perm false) <;>
            rw [hub] at h <;> simp only at h
          · cases h; exact ih
          · cases h
      | zero =>
        simp only [nth?, Option.some.injEq] at hi; subst hi
        rw [hno] at h; simp only at h
        cases h; rfl

theorem loadMPlace_frozen_unchanged {st st' : PState} {mp : MPlace} {b : Bytes}
    (h : loadMPlace st mp = .ok (b, st')) (i : Nat) (e : BorrowEntry)
    (hi : nth? st.borrows i = some e) (hf : e.perm = .frozen) : nth? st'.borrows i = some e := by
  unfold loadMPlace at h
  cases hg : heapGet st mp.alloc with
  | none => rw [hg] at h; cases h
  | some bs =>
    rw [hg] at h; simp only at h
    cases hb : Nat.ble (mp.offset + mp.size) bs.length with
    | false => rw [hb] at h; cases h
    | true =>
      rw [hb] at h; simp only at h
      cases ht : tbAccess .read st.borrows mp.alloc mp.tag mp.offset mp.size with
      | none => rw [ht] at h; cases h
      | some bs' =>
        rw [ht] at h; simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨_, rfl⟩ := h
        exact tbAccessAux_read_frozen_unchanged _ _ _ _ _ _ _ ht i e hi hf

theorem storeMPlace_nonoverlap_unchanged {st st' : PState} {mp : MPlace} {w : Bytes}
    (h : storeMPlace st mp w = .ok st') (i : Nat) (e : BorrowEntry)
    (hi : nth? st.borrows i = some e)
    (hno : (Nat.beq e.targetLocal mp.alloc &&
      byteRangesOverlapBool e.rangeOffset e.rangeLen mp.offset mp.size) = false) :
    nth? st'.borrows i = some e := by
  unfold storeMPlace at h
  cases hg : heapGet st mp.alloc with
  | none => rw [hg] at h; cases h
  | some bs =>
    rw [hg] at h; simp only at h
    cases hb : (Nat.ble (mp.offset + mp.size) bs.length && Nat.beq w.length mp.size) with
    | false => rw [hb] at h; cases h
    | true =>
      rw [hb] at h; simp only at h
      cases ht : tbAccess .write st.borrows mp.alloc mp.tag mp.offset mp.size with
      | none => rw [ht] at h; cases h
      | some bs' =>
        rw [ht] at h; simp only at h
        rw [putHeap_borrows h]
        exact tbAccessAux_nonoverlap_unchanged _ _ _ _ _ _ _ _ ht i e hi hno

theorem writeDest_nonoverlap_unchanged {st st' : PState} {d : DestPlace} {b : Bytes}
    (h : writeDest st d b = .ok st') (i : Nat) (e : BorrowEntry)
    (hi : nth? st.borrows i = some e) (hno : entryOverlapsDest e d = false) :
    nth? st'.borrows i = some e := by
  cases d with
  | imm l => simp only [writeDest] at h; rw [setLocalE_borrows h]; exact hi
  | mem mp => exact storeMPlace_nonoverlap_unchanged h i e hi hno

/-- **`deinitMovedPlace_assignUse_preserves_tb_tags`** (`StatementKind.assign
dest (move p)` through `copyRuntimePlaceNoValidate`): for *every* state, source
place and pre-resolved destination, a successful move leaves every `.frozen`
Tree Borrows entry that does not overlap the destination window *literally
unchanged* — the move's read is a read and its deinit is not a Tree Borrows
access; only the destination store can touch overlapping entries (as it must,
and exactly as the corresponding `copy` would). -/
theorem deinitMovedPlace_assignUse_preserves_tb_tags (pb : Nat) (st : PState) (p : SemPlace)
    (d : DestPlace) (st₁ : PState) (h : twoPhaseAssignUse true pb st (.move p) d = .ok st₁) :
    ∀ i e, nth? st.borrows i = some e → e.perm = .frozen → entryOverlapsDest e d = false →
      nth? st₁.borrows i = some e := by
  intro i e hi hf hno
  rw [twoPhaseAssignUse_true_eq] at h
  simp only [annealAssignUse] at h
  cases he : evalPlaceToOp pb (clearLatch st) p with
  | error err => rw [he] at h; cases h
  | ok r =>
    obtain ⟨o, ty⟩ := r
    rw [he] at h
    cases o with
    | immediate bb =>
      simp only at h
      cases hp : p.projs with
      | cons _ _ => rw [hp] at h; cases h
      | nil =>
        rw [hp] at h; simp only at h
        cases hs : setLocalE (clearLatch st) p.local_ (.imm (uninitBytes bb.length)) with
        | error err => rw [hs] at h; cases h
        | ok st₂ =>
          rw [hs] at h; simp only at h
          cases hv : checkValid ty bb with
          | error err => rw [hv] at h; cases h
          | ok u =>
            rw [hv] at h; simp only at h
            have hb₂ := setLocalE_borrows hs
            exact writeDest_nonoverlap_unchanged h i e (by
              show nth? st₂.borrows i = some e; rw [hb₂]; exact hi) hno
    | indirect src =>
      simp only at h
      cases hm : usesMemoryPath ty (.indirect src) with
      | true =>
        rw [hm] at h; simp only at h
        cases hc : copyMemPath (clearLatch st) src d with
        | error err => rw [hc] at h; cases h
        | ok st₂ =>
          rw [hc] at h; simp only at h
          rw [deinitMPlaceRaw_borrows h]
          cases d with
          | imm l => simp only [copyMemPath] at hc; cases hc
          | mem dmp =>
            simp only [copyMemPath] at hc
            cases hl : loadMPlace (clearLatch st) src with
            | error err => rw [hl] at hc; cases hc
            | ok r' =>
              obtain ⟨bb, st₃⟩ := r'
              rw [hl] at hc; simp only at hc
              have h3 := loadMPlace_frozen_unchanged hl i e hi hf
              cases hov : placesOverlap src dmp with
              | true => rw [hov] at hc; cases hc
              | false =>
                rw [hov] at hc; simp only at hc
                exact storeMPlace_nonoverlap_unchanged hc i e h3 hno
      | false =>
        rw [hm] at h; simp only at h
        cases hl : loadMPlace (clearLatch st) src with
        | error err => rw [hl] at h; cases h
        | ok r' =>
          obtain ⟨bb, st₃⟩ := r'
          rw [hl] at h; simp only at h
          have h3 := loadMPlace_frozen_unchanged hl i e hi hf
          cases hv : checkValid ty bb with
          | error err => rw [hv] at h; cases h
          | ok u =>
            rw [hv] at h; simp only at h
            cases hd : deinitMPlaceRaw st₃ src with
            | error err => rw [hd] at h; cases h
            | ok st₄ =>
              rw [hd] at h; simp only at h
              exact writeDest_nonoverlap_unchanged h i e
                (by rw [deinitMPlaceRaw_borrows hd]; exact h3) hno

/-- A Tree Borrows **write** through a tag that is foreign to an overlapping,
unprotected `.frozen` entry disables it. -/
theorem treeBorrowNodeAccess_foreign_write_frozen :
    treeBorrowNodeAccess .write .foreignAccess .frozen false = .transition .disabled := rfl

theorem tbAccessAux_write_disables_foreign_frozen (all : List BorrowEntry) (a : Nat)
    (tag : Option Nat) (off len : Nat) (e : BorrowEntry) (es es' : List BorrowEntry)
    (h : tbAccessAux .write all a tag off len (e :: es) = some es')
    (hf : e.perm = .frozen) (hl : e.targetLocal = a)
    (ho : byteRangesOverlapBool e.rangeOffset e.rangeLen off len = true)
    (hrel : tbRelatedness all tag e = .foreignAccess) :
    ∃ e' rest, es' = e' :: rest ∧ e'.tag = e.tag ∧ e'.perm = .disabled := by
  simp only [tbAccessAux] at h
  cases hr : tbAccessAux .write all a tag off len es with
  | none => rw [hr] at h; cases h
  | some xs' =>
    rw [hr] at h
    have hc : (Nat.beq e.targetLocal a && byteRangesOverlapBool e.rangeOffset e.rangeLen off len) =
        true := by simp [hl, ho]
    simp only [hc, hrel, hf, treeBorrowNodeAccess_foreign_write_frozen,
      treeBorrowTransitionIsUB] at h
    cases h
    exact ⟨_, _, rfl, rfl, rfl⟩

/-- Is a Tree Borrows permission `.frozen`? -/
def permIsFrozen : TreeBorrowPerm → Bool
  | .frozen => true
  | _ => false

/-- Is a Tree Borrows permission `.disabled`? -/
def permIsDisabled : TreeBorrowPerm → Bool
  | .disabled => true
  | _ => false

/-- Permissions of the borrow table after a run (for state-level canaries),
as `(frozen?, disabled?)` flags. -/
def borrowPermFlags : StepOut → List (Bool × Bool)
  | .running st => st.borrows.map (fun e => (permIsFrozen e.perm, permIsDisabled e.perm))
  | _ => []

/-- Run the `D5` prefix (`_1 = 5; _3 = &_1; _2 = &raw mut _1`) then one more
statement. -/
def d5PermsAfter (s : Statement) (steps : Nat) : List (Bool × Bool) :=
  let p := d5Prog s (.use (.copy (loc 4)))
  match annealInit p [] with
  | .ok st => borrowPermFlags (annealRun p steps st)
  | .error _ => []

/-- **`assign_or_deinit_stmt_kills_sibling_frozen`**: in the `D5` state the
sibling shared borrow is `.frozen`; `StatementKind.assign (*_2)` and
`StatementKind.deinit (*_2)` disable it, while `_4 = move (*_2)` keeps it
`.frozen` (state-level). -/
theorem assign_or_deinit_stmt_kills_sibling_frozen :
    d5PermsAfter (asg (loc 4) (.use (.move (drf 2)))) 3 = [(true, false)] ∧
    d5PermsAfter (asg (loc 4) (.use (.move (drf 2)))) 4 = [(true, false)] ∧
    d5PermsAfter (asg (drf 2) (.use (cU8 9))) 4 = [(false, true)] ∧
    d5PermsAfter (stmt (.deinit (drf 2))) 4 = [(false, true)] := by
  decide

/-! ## Part 10 — `MiriMoveDeinitWiring` -/

/-- **`miriMoveDeinitWiring`** (`withValidation` / `operandHooks` /
`takePendingMoveDeinit` invariants) holds for every flag, pointer width and
state. -/
theorem miriMoveDeinitWiring_holds (dm : Bool) (pb : Nat) (st : PState) :
    MiriMoveDeinitWiring dm pb st := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ⟨rfl, rfl⟩, rfl⟩
  · intro b ty o ty' st' h
    simp only [refEvalOperand, ite_true, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨_, _, rfl⟩ := h; rfl
  · intro p o ty st' h
    simp only [refEvalOperand, ite_true] at h
    cases he : evalPlaceToOp pb (clearLatch st) p with
    | error e => rw [he] at h; cases h
    | ok r =>
      rw [he] at h; simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨_, _, rfl⟩ := h; rfl
  · intro p mp ty st' h
    simp only [refEvalOperand] at h
    cases he : evalPlaceToOp pb (clearLatch st) p with
    | error e => rw [he] at h; cases h
    | ok r =>
      obtain ⟨o, ty₀⟩ := r
      rw [he] at h
      cases o with
      | immediate b =>
        simp only at h
        cases hp : p.projs with
        | cons _ _ => rw [hp] at h; cases h
        | nil =>
          rw [hp] at h; simp only at h
          cases hs : setLocalE (clearLatch st) p.local_ (.imm (uninitBytes b.length)) with
          | error e => rw [hs] at h; cases h
          | ok st₁ => rw [hs] at h; simp only [Except.ok.injEq, Prod.mk.injEq] at h; cases h.1
      | indirect mp₀ =>
        simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨_, _, rfl⟩ := h; rfl
  · intro p b ty st' h
    simp only [refEvalOperand] at h
    cases he : evalPlaceToOp pb (clearLatch st) p with
    | error e => rw [he] at h; cases h
    | ok r =>
      obtain ⟨o, ty₀⟩ := r
      rw [he] at h
      cases o with
      | immediate b₀ =>
        simp only at h
        cases hp : p.projs with
        | cons _ _ => rw [hp] at h; cases h
        | nil =>
          rw [hp] at h; simp only at h
          cases hs : setLocalE (clearLatch st) p.local_ (.imm (uninitBytes b₀.length)) with
          | error e => rw [hs] at h; cases h
          | ok st₁ =>
            rw [hs] at h; simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨_, _, rfl⟩ := h; exact ⟨rfl, rfl⟩
      | indirect mp₀ => simp only [Except.ok.injEq, Prod.mk.injEq] at h; cases h.1

/-- A state with one memory-backed `u8` local (allocation `0`) and a set latch
cleared: the latch-set non-vacuity witness. -/
def latchWitnessState : PState :=
  { frames := [⟨0, 0, 0, [.mem 0], none⟩], heap := [some [AbstractByte.init 7 none]],
    borrows := [], nextTag := 1, pendingMoveDeinit := false }

/-- The latch is genuinely set mid-step: moving out of a memory-backed local in
phase 1 (`refEvalOperand true`) sets `pendingMoveDeinit`. -/
theorem refEvalOperand_sets_latch_nonvacuous :
    ∃ (pb : Nat) (st : PState) (p : SemPlace) (mp : MPlace) (ty : SemTy) (st' : PState),
      st.pendingMoveDeinit = false ∧
      refEvalOperand true pb st (.move p) = .ok (.indirect mp, ty, st') ∧
      st'.pendingMoveDeinit = true :=
  ⟨64, latchWitnessState, ⟨0, (kU8, lay kU8), []⟩, ⟨0, 0, (lay kU8).size.bytes, none⟩,
    (kU8, lay kU8), { clearLatch latchWitnessState with pendingMoveDeinit := true },
    rfl, rfl, rfl⟩

/-! ## Part 10b — Live `Trusted.Rustc.V2026_06_01.MirSemantics.evalOperand` bridge

1. For unprojected root locals (`place.projection = []`), the default-mode
   live `evalOperand` deinitializes the moved slot to `.uninit`
   (`set? locals l .uninit`) while `.copy` preserves `locals`.
2. For any projected place (`place.projection = e :: es`, including `.deref`
   and `.field`), the default-mode (`deinitProjectedMoves := false`) live
   `evalOperand` treats `.move` **identically** to `.copy`.
3. With `deinitProjectedMoves := true` (Episode 1), field and element moves
   deinitialize the moved sub-place for every state (in a context without local
   declarations), and the subslice and `Deref` canaries below exhibit window
   and pointee deinitialization with sibling preservation. -/

theorem seq_get?_eq {α : Type} (xs : List α) (i : Nat) : Trusted.Sequence.get? xs i = xs[i]? := rfl

theorem seq_lt_of_get? {α : Type} {xs : List α} {i : Nat} {x : α}
    (h : Trusted.Sequence.get? xs i = some x) : i < xs.length :=
  (List.getElem?_eq_some_iff.mp h).1

theorem seq_set?_of_lt {α : Type} {xs : List α} {i : Nat} (h : i < xs.length) (y : α) :
    Trusted.Sequence.set? xs i y = some (xs.set i y) := by
  simp [Trusted.Sequence.set?, h]

theorem seq_get?_set_self {α : Type} {xs : List α} {i : Nat} (h : i < xs.length) (y : α) :
    Trusted.Sequence.get? (xs.set i y) i = some y := by
  simp [Trusted.Sequence.get?, List.getElem?_set_self h]

theorem seq_get?_set_ne {α : Type} (xs : List α) {i j : Nat} (y : α) (h : j ≠ i) :
    Trusted.Sequence.get? (xs.set i y) j = Trusted.Sequence.get? xs j := by
  simp only [Trusted.Sequence.get?]
  exact List.getElem?_set_ne (Ne.symm h)

theorem moveValueIsZeroSized_nil_of_ne_unit (layouts : LayoutTable) (tyOpt : Option Ty) (v : Value)
    (h : v ≠ .unit) : moveValueIsZeroSized [] layouts tyOpt v = false := by
  cases v with
  | unit => exact absurd rfl h
  | scalar _ => rfl
  | ptr _ _ => rfl
  | aggregate _ _ => rfl

theorem trusted_evalOperand_root_move_deinits
    (locals locals' : List LocalSlot) (l : Local) (v : Value)
    (borrows : List BorrowEntry) (globals : List CapturedAllocation) (layouts : LayoutTable)
    (callerLocals : List LocalSlot) (localDecls : List LocalDecl)
    (callStack : List SavedCallerFrame)
    (hget : Trusted.Sequence.get? locals l = some (.init v))
    (hset : Trusted.Sequence.set? locals l .uninit = some locals') :
    evalOperand locals (.move ⟨l, []⟩) borrows globals layouts callerLocals localDecls callStack =
      .ok v locals' ∧
    evalOperand locals (.copy ⟨l, []⟩) borrows globals layouts callerLocals localDecls callStack =
      .ok v locals ∧
    (v ≠ .unit → valueContainsMovedUninit v = false →
      evalOperand locals (.move ⟨l, []⟩) borrows globals layouts callerLocals [] callStack true =
        .ok v locals' ∧
      evalOperand locals (.copy ⟨l, []⟩) borrows globals layouts callerLocals [] callStack true =
        .ok v locals ∧
      evalOperand locals' (.copy ⟨l, []⟩) borrows globals layouts callerLocals [] callStack true =
        .ub) := by
  have hll := seq_lt_of_get? hget
  have hsl := seq_set?_of_lt hll LocalSlot.uninit
  have heq : locals' = locals.set l .uninit := by
    rw [hsl] at hset; exact (Option.some.inj hset).symm
  have hget' : Trusted.Sequence.get? locals' l = some .uninit := by
    rw [heq]; exact seq_get?_set_self hll _
  refine ⟨by simp [evalOperand, hget, hset], by simp [evalOperand, hget, readProjectedValue], ?_⟩
  intro hunit hmv
  have hzst := moveValueIsZeroSized_nil_of_ne_unit layouts (placeTyResolved [] layouts ⟨l, []⟩) v hunit
  refine ⟨?_, ?_, ?_⟩
  · simp [evalOperand, evalMoveOperandDeinit, evalCopyPlaceRead, hget, readProjectedValue, hmv,
      hzst, deinitMovedSubPlace, hset]
  · simp [evalOperand, guardMovedUninitRead, evalCopyPlaceRead, hget, readProjectedValue, hmv]
  · simp [evalOperand, guardMovedUninitRead, evalCopyPlaceRead, hget']

theorem trusted_evalOperand_projected_move_eq_copy
    (locals : List LocalSlot) (l : Local) (e : ProjectionElem) (es : List ProjectionElem)
    (borrows : List BorrowEntry) (globals : List CapturedAllocation) (layouts : LayoutTable)
    (callerLocals : List LocalSlot) (localDecls : List LocalDecl)
    (callStack : List SavedCallerFrame) :
    evalOperand locals (.move ⟨l, e :: es⟩) borrows globals layouts callerLocals localDecls
        callStack false =
      evalOperand locals (.copy ⟨l, e :: es⟩) borrows globals layouts callerLocals localDecls
        callStack false := by
  cases e <;> rfl

/-- The fallback branch of `movedMarkerValue` always contains a moved-out leaf. -/
theorem movedMarker_fallback_contains (w : Value) :
    valueContainsMovedUninit
      (match valueContainsMovedUninit (markMovedValue w) with
       | true => markMovedValue w
       | false => movedUninitValue) = true := by
  cases hm : valueContainsMovedUninit (markMovedValue w) with
  | true => exact hm
  | false => rfl

/-- The moved-out marker contains a moved-out leaf whenever the last
structural projection is not a subslice. -/
theorem movedMarkerValue_contains_of_not_subslice (proj : List ProjectionElem) (v : Value)
    (h : ∀ a b c, lastStructuralProjection? proj ≠ some (.subslice a b c)) :
    valueContainsMovedUninit (movedMarkerValue proj v) = true := by
  unfold movedMarkerValue
  split
  · rename_i a b c elems hl
    exact absurd hl (h a b c)
  · exact movedMarker_fallback_contains _

/-- **Field moves deinitialize the field (all states, no local declarations).** -/
theorem trusted_evalOperand_field_move_deinit
    (locals : List LocalSlot) (l : Local) (variant : VariantIdx) (fields : List Value)
    (idx : FieldIdx) (fty : Ty) (v : Value) (borrows : List BorrowEntry)
    (globals : List CapturedAllocation) (layouts : LayoutTable)
    (callerLocals : List LocalSlot) (callStack : List SavedCallerFrame)
    (hl : Trusted.Sequence.get? locals l = some (.init (.aggregate variant fields)))
    (hv : Trusted.Sequence.get? fields idx = some v)
    (hunit : v ≠ .unit) (hmv : valueContainsMovedUninit v = false) :
    ∃ locals',
      evalOperand locals (.move ⟨l, [.field idx fty]⟩) borrows globals layouts callerLocals []
        callStack true = .ok v locals' ∧
      evalOperand locals' (.copy ⟨l, [.field idx fty]⟩) borrows globals layouts callerLocals []
        callStack true = .ub ∧
      ∀ (j : FieldIdx) (jty : Ty) (w : Value), j ≠ idx →
        Trusted.Sequence.get? fields j = some w → valueContainsMovedUninit w = false →
        evalOperand locals' (.copy ⟨l, [.field j jty]⟩) borrows globals layouts callerLocals []
          callStack true = .ok w locals' := by
  have hidx := seq_lt_of_get? hv
  have hll := seq_lt_of_get? hl
  have hmark : valueContainsMovedUninit (movedMarkerValue [.field idx fty] v) = true :=
    movedMarkerValue_contains_of_not_subslice _ v (by intro a b c h; cases h)
  have hl' : Trusted.Sequence.get?
      (locals.set l (.init (.aggregate variant (fields.set idx (movedMarkerValue [.field idx fty] v)))))
      l = some (.init (.aggregate variant (fields.set idx (movedMarkerValue [.field idx fty] v)))) :=
    seq_get?_set_self hll _
  have hm' : Trusted.Sequence.get? (fields.set idx (movedMarkerValue [.field idx fty] v)) idx =
      some (movedMarkerValue [.field idx fty] v) :=
    seq_get?_set_self hidx _
  refine ⟨locals.set l
    (.init (.aggregate variant (fields.set idx (movedMarkerValue [.field idx fty] v)))), ?_, ?_, ?_⟩
  · have hzst := moveValueIsZeroSized_nil_of_ne_unit layouts
      (placeTyResolved [] layouts ⟨l, [.field idx fty]⟩) v hunit
    have hsf := seq_set?_of_lt hidx (movedMarkerValue [.field idx fty] v)
    have hsl := seq_set?_of_lt hll
      (LocalSlot.init (.aggregate variant (fields.set idx (movedMarkerValue [.field idx fty] v))))
    simp only [evalOperand, evalMoveOperandDeinit, evalCopyPlaceRead, hl, readProjectedValue, hv,
      hmv, hzst, deinitMovedSubPlace, projHasDeref, writeProjectedValue, hsf, hsl]
  · simp only [evalOperand, guardMovedUninitRead, evalCopyPlaceRead, hl', readProjectedValue, hm',
      hmark]
  · intro j jty w hj hw hmw
    have hw' : Trusted.Sequence.get? (fields.set idx (movedMarkerValue [.field idx fty] v)) j =
        some w := by
      rw [seq_get?_set_ne _ _ hj]; exact hw
    simp only [evalOperand, guardMovedUninitRead, evalCopyPlaceRead, hl', readProjectedValue, hw',
      hmw]

/-- **Element moves deinitialize the element (all states, no local
declarations).** -/
theorem trusted_evalOperand_elem_move_deinit
    (locals : List LocalSlot) (l : Local) (elems : List Value) (idx minLen : Nat) (v : Value)
    (borrows : List BorrowEntry) (globals : List CapturedAllocation) (layouts : LayoutTable)
    (callerLocals : List LocalSlot) (callStack : List SavedCallerFrame)
    (hl : Trusted.Sequence.get? locals l = some (.init (.aggregate 0 elems)))
    (hmin : minLen ≤ elems.length)
    (hv : Trusted.Sequence.get? elems idx = some v)
    (hunit : v ≠ .unit) (hmv : valueContainsMovedUninit v = false) :
    ∃ locals',
      evalOperand locals (.move ⟨l, [.constantIndex idx minLen false]⟩) borrows globals layouts
        callerLocals [] callStack true = .ok v locals' ∧
      evalOperand locals' (.copy ⟨l, [.constantIndex idx minLen false]⟩) borrows globals layouts
        callerLocals [] callStack true = .ub ∧
      ∀ (j : Nat) (w : Value), j ≠ idx →
        Trusted.Sequence.get? elems j = some w → valueContainsMovedUninit w = false →
        evalOperand locals' (.copy ⟨l, [.constantIndex j minLen false]⟩) borrows globals layouts
          callerLocals [] callStack true = .ok w locals' := by
  have hidx := seq_lt_of_get? hv
  have hll := seq_lt_of_get? hl
  have hmark : valueContainsMovedUninit (movedMarkerValue [.constantIndex idx minLen false] v) =
      true :=
    movedMarkerValue_contains_of_not_subslice _ v (by intro a b c h; cases h)
  have hl' : Trusted.Sequence.get?
      (locals.set l (.init (.aggregate 0
        (elems.set idx (movedMarkerValue [.constantIndex idx minLen false] v))))) l =
      some (.init (.aggregate 0
        (elems.set idx (movedMarkerValue [.constantIndex idx minLen false] v)))) :=
    seq_get?_set_self hll _
  have hm' : Trusted.Sequence.get?
      (elems.set idx (movedMarkerValue [.constantIndex idx minLen false] v)) idx =
      some (movedMarkerValue [.constantIndex idx minLen false] v) :=
    seq_get?_set_self hidx _
  have hble : Nat.ble minLen (Trusted.Sequence.length elems) = true := Nat.ble_eq.mpr hmin
  have hble' : Nat.ble minLen (Trusted.Sequence.length
      (elems.set idx (movedMarkerValue [.constantIndex idx minLen false] v))) = true := by
    simp only [Trusted.Sequence.length, List.length_set]; exact Nat.ble_eq.mpr hmin
  refine ⟨locals.set l (.init (.aggregate 0
    (elems.set idx (movedMarkerValue [.constantIndex idx minLen false] v)))), ?_, ?_, ?_⟩
  · have hzst := moveValueIsZeroSized_nil_of_ne_unit layouts
      (placeTyResolved [] layouts ⟨l, [.constantIndex idx minLen false]⟩) v hunit
    have hse := seq_set?_of_lt hidx (movedMarkerValue [.constantIndex idx minLen false] v)
    have hsl := seq_set?_of_lt hll (LocalSlot.init (.aggregate 0
      (elems.set idx (movedMarkerValue [.constantIndex idx minLen false] v))))
    simp only [evalOperand, evalMoveOperandDeinit, evalCopyPlaceRead, hl, readProjectedValue, hble,
      hv, hmv, hzst, deinitMovedSubPlace, projHasDeref, writeProjectedValue, hse, hsl]
  · simp only [evalOperand, guardMovedUninitRead, evalCopyPlaceRead, hl', readProjectedValue,
      hble', hm', hmark]
  · intro j w hj hw hmw
    have hw' : Trusted.Sequence.get?
        (elems.set idx (movedMarkerValue [.constantIndex idx minLen false] v)) j = some w := by
      rw [seq_get?_set_ne _ _ hj]; exact hw
    simp only [evalOperand, guardMovedUninitRead, evalCopyPlaceRead, hl', readProjectedValue,
      hble', hw', hmw]

/-- **Dynamic `.index` element moves deinitialize the element (all states, no
local declarations).** -/
theorem trusted_evalOperand_index_move_deinit
    (locals : List LocalSlot) (l idxLocal : Local) (elems : List Value) (idx : Nat) (v : Value)
    (borrows : List BorrowEntry) (globals : List CapturedAllocation) (layouts : LayoutTable)
    (callerLocals : List LocalSlot) (callStack : List SavedCallerFrame)
    (hne : l ≠ idxLocal)
    (hl : Trusted.Sequence.get? locals l = some (.init (.aggregate 0 elems)))
    (hidxLocal : Trusted.Sequence.get? locals idxLocal =
      some (.init (.scalar { bits := idx, sizeBytes := 8 })))
    (hv : Trusted.Sequence.get? elems idx = some v)
    (hunit : v ≠ .unit) (hmv : valueContainsMovedUninit v = false) :
    ∃ locals',
      evalOperand locals (.move ⟨l, [.index idxLocal]⟩) borrows globals layouts
        callerLocals [] callStack true = .ok v locals' ∧
      evalOperand locals' (.copy ⟨l, [.index idxLocal]⟩) borrows globals layouts
        callerLocals [] callStack true = .ub ∧
      ∀ (j : Nat) (w : Value), j ≠ idx →
        Trusted.Sequence.get? elems j = some w → valueContainsMovedUninit w = false →
        evalOperand locals' (.copy ⟨l, [.constantIndex j 0 false]⟩) borrows globals layouts
          callerLocals [] callStack true = .ok w locals' := by
  have hidx := seq_lt_of_get? hv
  have hll := seq_lt_of_get? hl
  have hmark : valueContainsMovedUninit (movedMarkerValue [.index idxLocal] v) = true :=
    movedMarkerValue_contains_of_not_subslice _ v (by intro a b c h; cases h)
  have hl' : Trusted.Sequence.get?
      (locals.set l (.init (.aggregate 0
        (elems.set idx (movedMarkerValue [.index idxLocal] v))))) l =
      some (.init (.aggregate 0
        (elems.set idx (movedMarkerValue [.index idxLocal] v)))) :=
    seq_get?_set_self hll _
  have hidxLocal' : Trusted.Sequence.get?
      (locals.set l (.init (.aggregate 0
        (elems.set idx (movedMarkerValue [.index idxLocal] v))))) idxLocal =
      some (.init (.scalar { bits := idx, sizeBytes := 8 })) := by
    rw [seq_get?_set_ne _ _ (Ne.symm hne)]; exact hidxLocal
  have hm' : Trusted.Sequence.get?
      (elems.set idx (movedMarkerValue [.index idxLocal] v)) idx =
      some (movedMarkerValue [.index idxLocal] v) :=
    seq_get?_set_self hidx _
  have hble0 : Nat.ble 0 (Trusted.Sequence.length
      (elems.set idx (movedMarkerValue [.index idxLocal] v))) = true := by
    simp only [Nat.ble_eq]; omega
  refine ⟨locals.set l (.init (.aggregate 0
    (elems.set idx (movedMarkerValue [.index idxLocal] v)))), ?_, ?_, ?_⟩
  · have hzst := moveValueIsZeroSized_nil_of_ne_unit layouts
      (placeTyResolved [] layouts ⟨l, [.index idxLocal]⟩) v hunit
    have hse := seq_set?_of_lt hidx (movedMarkerValue [.index idxLocal] v)
    have hsl := seq_set?_of_lt hll (LocalSlot.init (.aggregate 0
      (elems.set idx (movedMarkerValue [.index idxLocal] v))))
    simp only [evalOperand, evalMoveOperandDeinit, evalCopyPlaceRead, hl, readProjectedValue,
      hidxLocal, hv, hmv, hzst, deinitMovedSubPlace, projHasDeref, writeProjectedValue, hse, hsl]
  · simp only [evalOperand, guardMovedUninitRead, evalCopyPlaceRead, hl', readProjectedValue,
      hidxLocal', hm', hmark]
  · intro j w hj hw hmw
    have hw' : Trusted.Sequence.get?
        (elems.set idx (movedMarkerValue [.index idxLocal] v)) j = some w := by
      rw [seq_get?_set_ne _ _ hj]; exact hw
    simp only [evalOperand, guardMovedUninitRead, evalCopyPlaceRead, hl', readProjectedValue,
      hble0, hw', hmw]

/-- `_1 = [10, 11, 12, 13]` after `move _1[1..3]`. -/
def d9TrustedAfterSubslice : List LocalSlot :=
  [.uninit, .init (.aggregate 0 [u8Value 10, movedUninitValue, movedUninitValue, u8Value 13])]

/-- **Subslice move canary** on the live `evalOperand` (`fromEnd := false` and
`fromEnd := true`). -/
theorem trusted_evalOperand_subslice_move_deinit :
    ∃ locals' : List LocalSlot,
      evalOperand [.uninit, .init (.aggregate 0 [u8Value 10, u8Value 11, u8Value 12, u8Value 13])]
          (.move ⟨1, [.subslice 1 3 false]⟩) [] [] emptyLayoutTable [] [] [] true =
        .ok (.aggregate 0 [u8Value 11, u8Value 12]) locals' ∧
      evalOperand [.uninit, .init (.aggregate 0 [u8Value 10, u8Value 11, u8Value 12, u8Value 13])]
          (.move ⟨1, [.subslice 1 1 true]⟩) [] [] emptyLayoutTable [] [] [] true =
        .ok (.aggregate 0 [u8Value 11, u8Value 12]) locals' ∧
      evalOperand locals' (.copy ⟨1, [.constantIndex 1 4 false]⟩) [] [] emptyLayoutTable [] [] []
        true = .ub ∧
      evalOperand locals' (.copy ⟨1, [.constantIndex 2 4 false]⟩) [] [] emptyLayoutTable [] [] []
        true = .ub ∧
      evalOperand locals' (.copy ⟨1, [.constantIndex 0 4 false]⟩) [] [] emptyLayoutTable [] [] []
        true = .ok (u8Value 10) locals' ∧
      evalOperand locals' (.copy ⟨1, [.constantIndex 3 4 false]⟩) [] [] emptyLayoutTable [] [] []
        true = .ok (u8Value 13) locals' ∧
      evalOperand locals' (.copy ⟨1, []⟩) [] [] emptyLayoutTable [] [] [] true = .ub :=
  ⟨d9TrustedAfterSubslice, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `_1 = U { b: 0x0302 }` after `move _1.a`. -/
def d3TrustedUnionAfterMove : List LocalSlot :=
  [.uninit, .init (.aggregate 0 [.unit, .unit, .aggregate 0 [.scalar ⟨0, 0⟩, .scalar ⟨3, 1⟩]])]

/-- `_1 = U { b: 0x0302 }` after `move _1.a` and `_1.a = 9`. -/
def d3TrustedUnionAfterReinit : List LocalSlot :=
  [.uninit, .init (.aggregate 0 [u8Value 9, .unit, .aggregate 0 [u8Value 9, u8Value 3]])]

/-- **Union field move and re-initialization** (`deinitUnionSubPlace`) on the
live `evalOperand`. -/
theorem trusted_evalOperand_union_move_deinit :
    ∃ locals' locals'' : List LocalSlot,
      evalOperand [.uninit, .init (.aggregate 0 [.unit, .scalar ⟨770, 2⟩])]
          (.move ⟨1, [.field 0 claimU8Ty]⟩) [] [] claimUnionLayouts [] claimUnionDecls [] true =
        .ok (u8Value 2) locals' ∧
      evalOperand locals' (.copy ⟨1, [.field 0 claimU8Ty]⟩) [] [] claimUnionLayouts []
        claimUnionDecls [] true = .ub ∧
      evalOperand locals' (.copy ⟨1, [.field 1 claimU16Ty]⟩) [] [] claimUnionLayouts []
        claimUnionDecls [] true = .ub ∧
      evalOperand locals' (.copy ⟨1, []⟩) [] [] claimUnionLayouts [] claimUnionDecls [] true =
        .ok (.aggregate 0 [.unit, .unit, .aggregate 0 [.scalar ⟨0, 0⟩, .scalar ⟨3, 1⟩]]) locals' ∧
      writePlaceValue locals' [] ⟨1, [.field 0 claimU8Ty]⟩ (u8Value 9) claimUnionDecls
        claimUnionLayouts = .ok locals'' ∧
      evalOperand locals'' (.copy ⟨1, [.field 1 claimU16Ty]⟩) [] [] claimUnionLayouts []
        claimUnionDecls [] true = .ok (.scalar ⟨777, 2⟩) locals'' ∧
      evalOperand [.uninit, .init (.aggregate 0 [.unit, .scalar ⟨770, 2⟩])]
          (.move ⟨1, [.field 0 claimU8Ty]⟩) [] [] claimUnionLayouts [] claimUnionDecls [] false =
        .ok (u8Value 2) [.uninit, .init (.aggregate 0 [.unit, .scalar ⟨770, 2⟩])] :=
  ⟨d3TrustedUnionAfterMove, d3TrustedUnionAfterReinit, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `_1 : u8 = 5; _2 = &raw mut _1` (tag `2`, active); `_3 = &_1` (tag `3`, frozen). -/
def d5TrustedLocals : List LocalSlot :=
  [.uninit, .init (u8Value 5), .init (.ptr { allocId := 2, offsetBytes := 0 } 8),
    .init (.ptr { allocId := 3, offsetBytes := 0 } 8)]

/-- Borrow table of `d5TrustedLocals`. -/
def d5TrustedBorrows : List BorrowEntry := claimDerefBorrows

/-- After `move (*_2)`: `_1` is deinitialized; nothing else changes. -/
def d5TrustedAfterMove : List LocalSlot :=
  [.uninit, .uninit, .init (.ptr { allocId := 2, offsetBytes := 0 } 8),
    .init (.ptr { allocId := 3, offsetBytes := 0 } 8)]

/-- **`Deref` move canary** on the live `evalOperand`. -/
theorem trusted_evalOperand_deref_move_deinit :
    ∃ locals' : List LocalSlot,
      evalOperand
          [.uninit, .init (u8Value 5), .init (.ptr { allocId := 2, offsetBytes := 0 } 8),
            .init (.ptr { allocId := 3, offsetBytes := 0 } 8)]
          (.move ⟨2, [.deref]⟩) claimDerefBorrows [] emptyLayoutTable [] [] [] true =
        .ok (u8Value 5) locals' ∧
      Trusted.Sequence.get? locals' 1 = some .uninit ∧
      evalOperand locals' (.copy ⟨2, [.deref]⟩) claimDerefBorrows [] emptyLayoutTable [] [] []
        true = .ub ∧
      evalOperand locals' (.copy ⟨3, [.deref]⟩) claimDerefBorrows [] emptyLayoutTable [] [] []
        true = .ub ∧
      evalOperand locals' (.copy ⟨1, []⟩) [] [] emptyLayoutTable [] [] [] true = .ub :=
  ⟨d5TrustedAfterMove, rfl, rfl, rfl, rfl, rfl⟩

/-- `_1 = [(1, 2), (3, 4)]` after `move (*_2).0` (`_2 = &raw mut _1[1]` at byte offset `2`). -/
def d5TrustedTypedDerefAfterMove : List LocalSlot :=
  [.uninit,
    .init (.aggregate 0 [.aggregate 0 [u8Value 1, u8Value 2],
      .aggregate 0 [movedUninitValue, u8Value 4]]),
    .init (.ptr { allocId := 2, offsetBytes := 2 } 8),
    .init (.ptr { allocId := 3, offsetBytes := 2 } 8)]

/-- **Typed thin-pointer `Deref` + field move** (`deinitTypedThinPtrDeref`) on
the live `evalOperand`. -/
theorem trusted_evalOperand_typed_deref_move_deinit :
    ∃ locals' : List LocalSlot,
      evalOperand
          [.uninit,
            .init (.aggregate 0 [.aggregate 0 [u8Value 1, u8Value 2],
              .aggregate 0 [u8Value 3, u8Value 4]]),
            .init (.ptr { allocId := 2, offsetBytes := 2 } 8),
            .init (.ptr { allocId := 3, offsetBytes := 2 } 8)]
          (.move ⟨2, [.deref, .field 0 claimU8Ty]⟩) claimDerefBorrows [] claimPairArrLayouts []
          claimPairArrDecls [] true = .ok (u8Value 3) locals' ∧
      evalOperand locals' (.copy ⟨2, [.deref, .field 1 claimU8Ty]⟩) claimDerefBorrows []
        claimPairArrLayouts [] claimPairArrDecls [] true = .ok (u8Value 4) locals' ∧
      evalOperand locals' (.copy ⟨3, [.deref, .field 1 claimU8Ty]⟩) claimDerefBorrows []
        claimPairArrLayouts [] claimPairArrDecls [] true = .ok (u8Value 4) locals' ∧
      evalOperand locals' (.copy ⟨1, [.constantIndex 0 2 false]⟩) claimDerefBorrows []
        claimPairArrLayouts [] claimPairArrDecls [] true =
          .ok (.aggregate 0 [u8Value 1, u8Value 2]) locals' ∧
      evalOperand locals' (.copy ⟨2, [.deref, .field 0 claimU8Ty]⟩) claimDerefBorrows []
        claimPairArrLayouts [] claimPairArrDecls [] true = .ub ∧
      evalOperand locals' (.copy ⟨3, [.deref]⟩) claimDerefBorrows [] claimPairArrLayouts []
        claimPairArrDecls [] true = .ub ∧
      evalOperand locals' (.copy ⟨1, [.constantIndex 1 2 false]⟩) claimDerefBorrows []
        claimPairArrLayouts [] claimPairArrDecls [] true = .ub ∧
      evalOperand locals' (.copy ⟨1, []⟩) claimDerefBorrows [] claimPairArrLayouts []
        claimPairArrDecls [] true = .ub :=
  ⟨d5TrustedTypedDerefAfterMove, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `_1 = [10, 11, 12, 13]` and `_2 : *mut [u8]` after `move (*_2)[1]`. -/
def d9TrustedSliceAfterElem : List LocalSlot :=
  [.uninit,
    .init (.aggregate 0 [u8Value 10, movedUninitValue, u8Value 12, u8Value 13]),
    .init (.aggregate 0 [.ptr { allocId := 2, offsetBytes := 0 } 8,
      .scalar { bits := 4, sizeBytes := 8 }])]

/-- `_1 = [10, 11, 12, 13]` and `_2 : *mut [u8]` after `move (*_2)[1..3]`. -/
def d9TrustedSliceAfterSub : List LocalSlot :=
  [.uninit,
    .init (.aggregate 0 [u8Value 10, movedUninitValue, movedUninitValue, u8Value 13]),
    .init (.aggregate 0 [.ptr { allocId := 2, offsetBytes := 0 } 8,
      .scalar { bits := 4, sizeBytes := 8 }])]

/-- **Slice fat-pointer `Deref` element and subslice moves**
(`deinitSliceFatPtrDeref`) on the live `evalOperand`. -/
theorem trusted_evalOperand_slice_deref_move_deinit :
    ∃ localsElem localsSub : List LocalSlot,
      let initSliceLocals : List LocalSlot :=
        [.uninit,
          .init (.aggregate 0 [u8Value 10, u8Value 11, u8Value 12, u8Value 13]),
          .init (.aggregate 0 [.ptr { allocId := 2, offsetBytes := 0 } 8,
            .scalar { bits := 4, sizeBytes := 8 }])]
      evalOperand initSliceLocals (.move ⟨2, [.deref, .constantIndex 1 4 false]⟩) claimDerefBorrows
        [] emptyLayoutTable [] [] [] true = .ok (u8Value 11) localsElem ∧
      evalOperand localsElem (.copy ⟨2, [.deref, .constantIndex 0 4 false]⟩) claimDerefBorrows
        [] emptyLayoutTable [] [] [] true = .ok (u8Value 10) localsElem ∧
      evalOperand localsElem (.copy ⟨2, [.deref, .constantIndex 2 4 false]⟩) claimDerefBorrows
        [] emptyLayoutTable [] [] [] true = .ok (u8Value 12) localsElem ∧
      evalOperand localsElem (.copy ⟨2, [.deref, .constantIndex 3 4 false]⟩) claimDerefBorrows
        [] emptyLayoutTable [] [] [] true = .ok (u8Value 13) localsElem ∧
      evalOperand localsElem (.copy ⟨2, [.deref, .constantIndex 1 4 false]⟩) claimDerefBorrows
        [] emptyLayoutTable [] [] [] true = .ub ∧
      evalOperand initSliceLocals (.move ⟨2, [.deref, .subslice 1 3 false]⟩) claimDerefBorrows
        [] emptyLayoutTable [] [] [] true =
          .ok (.aggregate 0 [u8Value 11, u8Value 12]) localsSub ∧
      evalOperand localsSub (.copy ⟨1, [.constantIndex 0 4 false]⟩) claimDerefBorrows
        [] emptyLayoutTable [] [] [] true = .ok (u8Value 10) localsSub ∧
      evalOperand localsSub (.copy ⟨1, [.constantIndex 1 4 false]⟩) claimDerefBorrows
        [] emptyLayoutTable [] [] [] true = .ub ∧
      evalOperand localsSub (.copy ⟨1, [.constantIndex 2 4 false]⟩) claimDerefBorrows
        [] emptyLayoutTable [] [] [] true = .ub ∧
      evalOperand localsSub (.copy ⟨1, [.constantIndex 3 4 false]⟩) claimDerefBorrows
        [] emptyLayoutTable [] [] [] true = .ok (u8Value 13) localsSub :=
  ⟨d9TrustedSliceAfterElem, d9TrustedSliceAfterSub, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Any read in `deinitProjectedMoves` mode faults on a value containing a
moved-out leaf. -/
theorem trusted_evalOperand_movedUninit_read_ub
    (locals : List LocalSlot) (p : Place) (borrows : List BorrowEntry)
    (globals : List CapturedAllocation) (layouts : LayoutTable)
    (callerLocals : List LocalSlot) (localDecls : List LocalDecl)
    (callStack : List SavedCallerFrame) (v : Value) (locals' : List LocalSlot)
    (hread : evalOperand locals (.copy p) borrows globals layouts callerLocals localDecls
      callStack = .ok v locals')
    (hmoved : valueContainsMovedUninit v = true) :
    evalOperand locals (.copy p) borrows globals layouts callerLocals localDecls callStack true =
        .ub ∧
      evalOperand locals (.move p) borrows globals layouts callerLocals localDecls callStack
        true = .ub := by
  have hcopy : evalOperand locals (.copy p) borrows globals layouts callerLocals localDecls
      callStack true =
      guardMovedUninitRead
        (evalOperand locals (.copy p) borrows globals layouts callerLocals localDecls callStack) :=
    rfl
  have hmove : evalOperand locals (.move p) borrows globals layouts callerLocals localDecls
      callStack true =
      evalMoveOperandDeinit p borrows globals layouts callerLocals localDecls callStack
        (evalOperand locals (.copy p) borrows globals layouts callerLocals localDecls callStack) :=
    rfl
  refine ⟨?_, ?_⟩
  · rw [hcopy, hread]; simp only [guardMovedUninitRead, hmoved]
  · rw [hmove, hread]; simp only [evalMoveOperandDeinit, hmoved]

/-- **Non-vacuity of the read guard**: after `move _1[1..3]`, a default-mode
`copy _1` returns the array with its two moved-out leaves (so the premises of
`trusted_evalOperand_movedUninit_read_ub` are satisfiable). -/
theorem trusted_evalOperand_movedUninit_read_nonvacuous :
    ∃ (locals : List LocalSlot) (p : Place) (v : Value) (locals' : List LocalSlot),
      evalOperand locals (.copy p) [] [] emptyLayoutTable [] [] [] = .ok v locals' ∧
      valueContainsMovedUninit v = true :=
  ⟨d9TrustedAfterSubslice, ⟨1, []⟩,
   .aggregate 0 [u8Value 10, movedUninitValue, movedUninitValue, u8Value 13],
   d9TrustedAfterSubslice, rfl, rfl⟩

/-- **`D4` root-local left-to-right ordering on the live `evalOperands` (all states).**
`[copy _l, move _l]` returns `[v, v]` and sets `_l` to `.uninit`, while
`[move _l, copy _l]` and `[move _l, move _l]` fault with `.ub`. -/
theorem trusted_evalOperands_root_move_order
    (locals locals' : List LocalSlot) (l : Local) (v : Value)
    (borrows : List BorrowEntry) (globals : List CapturedAllocation) (layouts : LayoutTable)
    (callerLocals : List LocalSlot) (callStack : List SavedCallerFrame)
    (hget : Trusted.Sequence.get? locals l = some (.init v))
    (hset : Trusted.Sequence.set? locals l .uninit = some locals')
    (hunit : v ≠ .unit) (hmv : valueContainsMovedUninit v = false) :
    evalOperands locals [.copy ⟨l, []⟩, .move ⟨l, []⟩] borrows globals layouts callerLocals []
      callStack true = .ok [v, v] locals' ∧
    evalOperands locals [.move ⟨l, []⟩, .copy ⟨l, []⟩] borrows globals layouts callerLocals []
      callStack true = .ub ∧
    evalOperands locals [.move ⟨l, []⟩, .move ⟨l, []⟩] borrows globals layouts callerLocals []
      callStack true = .ub := by
  have hr := (trusted_evalOperand_root_move_deinits locals locals' l v borrows globals layouts
    callerLocals [] callStack hget hset).2.2 hunit hmv
  have hll := seq_lt_of_get? hget
  have hsl := seq_set?_of_lt hll LocalSlot.uninit
  have heq : locals' = locals.set l .uninit := by
    rw [hsl] at hset; exact (Option.some.inj hset).symm
  have hget' : Trusted.Sequence.get? locals' l = some .uninit := by
    rw [heq]; exact seq_get?_set_self hll _
  have hmub : evalOperand locals' (.move ⟨l, []⟩) borrows globals layouts callerLocals []
      callStack true = .ub := by
    simp [evalOperand, evalMoveOperandDeinit, evalCopyPlaceRead, hget']
  refine ⟨?_, ?_, ?_⟩
  · simp [evalOperands, hr.1, hr.2.1]
  · simp [evalOperands, hr.1, hr.2.2]
  · simp [evalOperands, hr.1, hmub]

/-- **`D4` projected field left-to-right ordering on the live `evalOperands`
(all states, no local declarations).**
`[copy _l.idx, move _l.idx]` returns `[v, v]` and deinitializes field `idx`,
`[move _l.idx, copy _l.idx]` and `[move _l.idx, move _l.idx]` fault with `.ub`,
`[move _l.idx, copy _l.j]` (`j ≠ idx`) returns `[v, w]`, and legacy `false`
mode returns `[v, v]` on `[move _l.idx, copy _l.idx]`. -/
theorem trusted_evalOperands_field_move_order
    (locals : List LocalSlot) (l : Local) (variant : VariantIdx) (fields : List Value)
    (idx : FieldIdx) (fty : Ty) (v : Value) (borrows : List BorrowEntry)
    (globals : List CapturedAllocation) (layouts : LayoutTable)
    (callerLocals : List LocalSlot) (callStack : List SavedCallerFrame)
    (hl : Trusted.Sequence.get? locals l = some (.init (.aggregate variant fields)))
    (hv : Trusted.Sequence.get? fields idx = some v)
    (hunit : v ≠ .unit) (hmv : valueContainsMovedUninit v = false) :
    ∃ locals',
      evalOperands locals [.copy ⟨l, [.field idx fty]⟩, .move ⟨l, [.field idx fty]⟩]
        borrows globals layouts callerLocals [] callStack true = .ok [v, v] locals' ∧
      evalOperands locals [.move ⟨l, [.field idx fty]⟩, .copy ⟨l, [.field idx fty]⟩]
        borrows globals layouts callerLocals [] callStack true = .ub ∧
      evalOperands locals [.move ⟨l, [.field idx fty]⟩, .move ⟨l, [.field idx fty]⟩]
        borrows globals layouts callerLocals [] callStack true = .ub ∧
      evalOperands locals [.move ⟨l, [.field idx fty]⟩, .copy ⟨l, [.field idx fty]⟩]
        borrows globals layouts callerLocals [] callStack false = .ok [v, v] locals ∧
      ∀ (j : FieldIdx) (jty : Ty) (w : Value), j ≠ idx →
        Trusted.Sequence.get? fields j = some w → valueContainsMovedUninit w = false →
        evalOperands locals [.move ⟨l, [.field idx fty]⟩, .copy ⟨l, [.field j jty]⟩]
          borrows globals layouts callerLocals [] callStack true = .ok [v, w] locals' := by
  have hidx := seq_lt_of_get? hv
  have hll := seq_lt_of_get? hl
  have hmark : valueContainsMovedUninit (movedMarkerValue [.field idx fty] v) = true :=
    movedMarkerValue_contains_of_not_subslice _ v (by intro a b c h; cases h)
  let locals' := locals.set l
    (.init (.aggregate variant (fields.set idx (movedMarkerValue [.field idx fty] v))))
  have hl' : Trusted.Sequence.get? locals' l =
      some (.init (.aggregate variant (fields.set idx (movedMarkerValue [.field idx fty] v)))) :=
    seq_get?_set_self hll _
  have hm' : Trusted.Sequence.get? (fields.set idx (movedMarkerValue [.field idx fty] v)) idx =
      some (movedMarkerValue [.field idx fty] v) :=
    seq_get?_set_self hidx _
  have hzst := moveValueIsZeroSized_nil_of_ne_unit layouts
    (placeTyResolved [] layouts ⟨l, [.field idx fty]⟩) v hunit
  have hsf := seq_set?_of_lt hidx (movedMarkerValue [.field idx fty] v)
  have hsl := seq_set?_of_lt hll
    (LocalSlot.init (.aggregate variant (fields.set idx (movedMarkerValue [.field idx fty] v))))
  have hmove : evalOperand locals (.move ⟨l, [.field idx fty]⟩) borrows globals layouts
      callerLocals [] callStack true = .ok v locals' := by
    simp only [evalOperand, evalMoveOperandDeinit, evalCopyPlaceRead, hl, readProjectedValue, hv,
      hmv, hzst, deinitMovedSubPlace, projHasDeref, writeProjectedValue, hsf, hsl, locals']
  have hcopy : evalOperand locals (.copy ⟨l, [.field idx fty]⟩) borrows globals layouts
      callerLocals [] callStack true = .ok v locals := by
    simp only [evalOperand, guardMovedUninitRead, evalCopyPlaceRead, hl, readProjectedValue, hv,
      hmv]
  have hcopy_after : evalOperand locals' (.copy ⟨l, [.field idx fty]⟩) borrows globals layouts
      callerLocals [] callStack true = .ub := by
    simp only [evalOperand, guardMovedUninitRead, evalCopyPlaceRead, hl', readProjectedValue, hm',
      hmark]
  have hmove_after : evalOperand locals' (.move ⟨l, [.field idx fty]⟩) borrows globals layouts
      callerLocals [] callStack true = .ub := by
    simp only [evalOperand, evalMoveOperandDeinit, evalCopyPlaceRead, hl', readProjectedValue, hm',
      hmark]
  have hlegacy_move : evalOperand locals (.move ⟨l, [.field idx fty]⟩) borrows globals layouts
      callerLocals [] callStack false = .ok v locals := by
    simp only [evalOperand, hl, readProjectedValue, hv]
  have hlegacy_copy : evalOperand locals (.copy ⟨l, [.field idx fty]⟩) borrows globals layouts
      callerLocals [] callStack false = .ok v locals := by
    simp only [evalOperand, hl, readProjectedValue, hv]
  refine ⟨locals', ?_, ?_, ?_, ?_, ?_⟩
  · simp only [evalOperands, hcopy, hmove]
  · simp only [evalOperands, hmove, hcopy_after]
  · simp only [evalOperands, hmove, hmove_after]
  · simp only [evalOperands, hlegacy_move, hlegacy_copy]
  · intro j jty w hj hw hmw
    have hw' : Trusted.Sequence.get? (fields.set idx (movedMarkerValue [.field idx fty] v)) j =
        some w := by
      rw [seq_get?_set_ne _ _ hj]; exact hw
    have hcopy_sib : evalOperand locals' (.copy ⟨l, [.field j jty]⟩) borrows globals layouts
        callerLocals [] callStack true = .ok w locals' := by
      simp only [evalOperand, guardMovedUninitRead, evalCopyPlaceRead, hl', readProjectedValue, hw',
        hmw]
    simp only [evalOperands, hmove, hcopy_sib]

/-- **`D7` multi-operand `Deref` evaluation on the live `evalOperands` with a
sibling `.frozen` borrow** (untyped `*mut u8` and typed `*mut (u8, u8)` at byte
offset `2`). -/
theorem trusted_evalOperands_deref_move_order :
    ∃ localsDeref localsTyped : List LocalSlot,
      let initDeref : List LocalSlot :=
        [.uninit, .init (u8Value 5), .init (.ptr { allocId := 2, offsetBytes := 0 } 8),
          .init (.ptr { allocId := 3, offsetBytes := 0 } 8)]
      let initTyped : List LocalSlot :=
        [.uninit,
          .init (.aggregate 0 [.aggregate 0 [u8Value 1, u8Value 2],
            .aggregate 0 [u8Value 3, u8Value 4]]),
          .init (.ptr { allocId := 2, offsetBytes := 2 } 8),
          .init (.ptr { allocId := 3, offsetBytes := 2 } 8)]
      evalOperands initDeref [.copy ⟨2, [.deref]⟩, .move ⟨2, [.deref]⟩] claimDerefBorrows []
        emptyLayoutTable [] [] [] true = .ok [u8Value 5, u8Value 5] localsDeref ∧
      evalOperands initDeref [.copy ⟨3, [.deref]⟩, .move ⟨2, [.deref]⟩] claimDerefBorrows []
        emptyLayoutTable [] [] [] true = .ok [u8Value 5, u8Value 5] localsDeref ∧
      evalOperands initDeref [.move ⟨2, [.deref]⟩, .copy ⟨2, [.deref]⟩] claimDerefBorrows []
        emptyLayoutTable [] [] [] true = .ub ∧
      evalOperands initDeref [.move ⟨2, [.deref]⟩, .copy ⟨3, [.deref]⟩] claimDerefBorrows []
        emptyLayoutTable [] [] [] true = .ub ∧
      evalOperands initDeref [.move ⟨2, [.deref]⟩, .copy ⟨2, [.deref]⟩] claimDerefBorrows []
        emptyLayoutTable [] [] [] false = .ok [u8Value 5, u8Value 5] initDeref ∧
      evalOperands initTyped
        [.copy ⟨2, [.deref, .field 0 claimU8Ty]⟩, .move ⟨2, [.deref, .field 0 claimU8Ty]⟩]
        claimDerefBorrows [] claimPairArrLayouts [] claimPairArrDecls [] true =
          .ok [u8Value 3, u8Value 3] localsTyped ∧
      evalOperands initTyped
        [.move ⟨2, [.deref, .field 0 claimU8Ty]⟩, .copy ⟨2, [.deref, .field 0 claimU8Ty]⟩]
        claimDerefBorrows [] claimPairArrLayouts [] claimPairArrDecls [] true = .ub ∧
      evalOperands initTyped
        [.move ⟨2, [.deref, .field 0 claimU8Ty]⟩, .copy ⟨3, [.deref, .field 0 claimU8Ty]⟩]
        claimDerefBorrows [] claimPairArrLayouts [] claimPairArrDecls [] true = .ub ∧
      evalOperands initTyped
        [.move ⟨2, [.deref, .field 0 claimU8Ty]⟩, .copy ⟨3, [.deref, .field 1 claimU8Ty]⟩]
        claimDerefBorrows [] claimPairArrLayouts [] claimPairArrDecls [] true =
          .ok [u8Value 3, u8Value 4] localsTyped :=
  ⟨d5TrustedAfterMove, d5TrustedTypedDerefAfterMove,
   rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **Root moves in every typed context, both zero-sized polarities (all
states).** For *any* local declarations (not only the untyped `[]` context of
`trusted_evalOperand_root_move_deinits`), copying an initialized root local `_l`
without a moved-out leaf returns its value. When the moved value is not
zero-sized (`moveValueIsZeroSized … = false`, which without local declarations
holds exactly for non-`unit` values) the move returns the value and sets the slot
to `.uninit`, `[copy _l, move _l]` returns `[v, v]`, and `[move _l, copy _l]` /
`[move _l, move _l]` fault with `.ub`. When it is zero-sized (a `0`-byte
declared type) the move deinitializes nothing, so `[move _l, copy _l]` returns
`[v, v]` with `locals` unchanged, as in `lean-miri`, where a zero-sized
deinitialization writes no byte. -/
theorem trusted_evalOperand_root_move_typed
    (locals locals' : List LocalSlot) (l : Local) (v : Value)
    (borrows : List BorrowEntry) (globals : List CapturedAllocation) (layouts : LayoutTable)
    (callerLocals : List LocalSlot) (localDecls : List LocalDecl)
    (callStack : List SavedCallerFrame)
    (hget : Trusted.Sequence.get? locals l = some (.init v))
    (hset : Trusted.Sequence.set? locals l .uninit = some locals')
    (hmv : valueContainsMovedUninit v = false) :
    evalOperand locals (.copy ⟨l, []⟩) borrows globals layouts callerLocals localDecls callStack
      true = .ok v locals ∧
    (moveValueIsZeroSized localDecls layouts (placeTyResolved localDecls layouts ⟨l, []⟩) v =
        false →
      evalOperand locals (.move ⟨l, []⟩) borrows globals layouts callerLocals localDecls
        callStack true = .ok v locals' ∧
      evalOperands locals [.copy ⟨l, []⟩, .move ⟨l, []⟩] borrows globals layouts callerLocals
        localDecls callStack true = .ok [v, v] locals' ∧
      evalOperands locals [.move ⟨l, []⟩, .copy ⟨l, []⟩] borrows globals layouts callerLocals
        localDecls callStack true = .ub ∧
      evalOperands locals [.move ⟨l, []⟩, .move ⟨l, []⟩] borrows globals layouts callerLocals
        localDecls callStack true = .ub) ∧
    (moveValueIsZeroSized localDecls layouts (placeTyResolved localDecls layouts ⟨l, []⟩) v =
        true →
      evalOperand locals (.move ⟨l, []⟩) borrows globals layouts callerLocals localDecls
        callStack true = .ok v locals ∧
      evalOperands locals [.move ⟨l, []⟩, .copy ⟨l, []⟩] borrows globals layouts callerLocals
        localDecls callStack true = .ok [v, v] locals) := by
  have hll := seq_lt_of_get? hget
  have hsl := seq_set?_of_lt hll LocalSlot.uninit
  have heq : locals' = locals.set l .uninit := by
    rw [hsl] at hset; exact (Option.some.inj hset).symm
  have hget' : Trusted.Sequence.get? locals' l = some .uninit := by
    rw [heq]; exact seq_get?_set_self hll _
  have hcopy : evalOperand locals (.copy ⟨l, []⟩) borrows globals layouts callerLocals localDecls
      callStack true = .ok v locals := by
    simp [evalOperand, guardMovedUninitRead, evalCopyPlaceRead, hget, readProjectedValue, hmv]
  have hcopy' : evalOperand locals' (.copy ⟨l, []⟩) borrows globals layouts callerLocals
      localDecls callStack true = .ub := by
    simp [evalOperand, guardMovedUninitRead, evalCopyPlaceRead, hget']
  have hmove' : evalOperand locals' (.move ⟨l, []⟩) borrows globals layouts callerLocals
      localDecls callStack true = .ub := by
    simp [evalOperand, evalMoveOperandDeinit, evalCopyPlaceRead, hget']
  refine ⟨hcopy, fun hzst => ?_, fun hzst => ?_⟩
  · have hmove : evalOperand locals (.move ⟨l, []⟩) borrows globals layouts callerLocals
        localDecls callStack true = .ok v locals' := by
      simp [evalOperand, evalMoveOperandDeinit, evalCopyPlaceRead, hget, readProjectedValue, hmv,
        hzst, deinitMovedSubPlace, hset]
    refine ⟨hmove, ?_, ?_, ?_⟩
    · simp [evalOperands, hcopy, hmove]
    · simp [evalOperands, hmove, hcopy']
    · simp [evalOperands, hmove, hmove']
  · have hmove : evalOperand locals (.move ⟨l, []⟩) borrows globals layouts callerLocals
        localDecls callStack true = .ok v locals := by
      simp [evalOperand, evalMoveOperandDeinit, evalCopyPlaceRead, hget, readProjectedValue, hmv,
        hzst]
    refine ⟨hmove, ?_⟩
    simp [evalOperands, hmove, hcopy]

/-- A `0`-byte `()` layout for the typed zero-sized root-move witness. -/
def typedZstUnitLayout : TypeLayout :=
  { size := ⟨0⟩, align := ⟨1⟩, backendRepr := .memory, fields := .arbitrary [] [],
    variants := .single 0, isUninhabited := false, fieldLayouts := [] }

/-- Layout table whose only entry is `typedZstUnitLayout`. -/
def typedZstLayouts : LayoutTable := { emptyLayoutTable with entries := [typedZstUnitLayout] }

/-- Local declarations `_0 : (), _1 : ()` (both at the `0`-byte layout `0`). -/
def typedZstDecls : List LocalDecl :=
  [{ mutability := .mut, ty := { kind := .tuple [], layoutIdx := 0 }, debugName := .none },
   { mutability := .mut, ty := { kind := .tuple [], layoutIdx := 0 }, debugName := .none }]

/-- The field-less aggregate of the typed zero-sized witness is not `unit`. -/
theorem typedZst_value_ne_unit : (Value.aggregate 0 [] : Value) ≠ Value.unit := by
  intro h
  cases h

/-- **Non-vacuity of the zero-sized polarity of `trusted_evalOperand_root_move_typed`
for a non-`unit` value.** `_1 : ()` declared at a `0`-byte layout holds the
field-less aggregate `.aggregate 0 []` (which the untyped context would treat as
a non-zero-sized value and deinitialize); in the typed context it is zero-sized,
so `[move _1, copy _1]` returns it twice and leaves `locals` unchanged. -/
theorem trusted_evalOperand_root_move_typed_zst_nonvacuous :
    ∃ (locals : List LocalSlot) (l : Local) (v : Value) (layouts : LayoutTable)
        (localDecls : List LocalDecl),
      v ≠ .unit ∧ Trusted.Sequence.get? locals l = some (.init v) ∧
      moveValueIsZeroSized localDecls layouts (placeTyResolved localDecls layouts ⟨l, []⟩) v =
        true ∧
      moveValueIsZeroSized [] layouts (placeTyResolved [] layouts ⟨l, []⟩) v = false ∧
      evalOperands locals [.move ⟨l, []⟩, .copy ⟨l, []⟩] [] [] layouts [] localDecls [] true =
        .ok [v, v] locals :=
  ⟨[.uninit, .init (.aggregate 0 [])], 1, .aggregate 0 [], typedZstLayouts, typedZstDecls,
   typedZst_value_ne_unit, rfl, rfl, rfl, rfl⟩

/-- **Projected field moves in every non-union typed context (all states, any
`localDecls`).** Generalizes `trusted_evalOperand_field_move_deinit` and
`trusted_evalOperands_field_move_order` from `localDecls = []` to arbitrary
typed frames in which `_l.idx` does not touch a union, covering both non-ZST
sub-place deinitialization and ZST sub-field preservation (`D2`). -/
theorem trusted_evalOperand_field_move_typed
    (locals : List LocalSlot) (l : Local) (variant : VariantIdx) (fields : List Value)
    (idx : FieldIdx) (fty : Ty) (v : Value) (borrows : List BorrowEntry)
    (globals : List CapturedAllocation) (layouts : LayoutTable)
    (callerLocals : List LocalSlot) (localDecls : List LocalDecl)
    (callStack : List SavedCallerFrame)
    (hl : Trusted.Sequence.get? locals l = some (.init (.aggregate variant fields)))
    (hv : Trusted.Sequence.get? fields idx = some v)
    (hnu : placeTouchesUnion localDecls layouts ⟨l, [.field idx fty]⟩ = false)
    (hmv : valueContainsMovedUninit v = false) :
    evalOperand locals (.copy ⟨l, [.field idx fty]⟩) borrows globals layouts callerLocals
      localDecls callStack true = .ok v locals ∧
    (moveValueIsZeroSized localDecls layouts
        (placeTyResolved localDecls layouts ⟨l, [.field idx fty]⟩) v = false →
      ∃ locals',
        evalOperand locals (.move ⟨l, [.field idx fty]⟩) borrows globals layouts callerLocals
          localDecls callStack true = .ok v locals' ∧
        evalOperands locals [.copy ⟨l, [.field idx fty]⟩, .move ⟨l, [.field idx fty]⟩]
          borrows globals layouts callerLocals localDecls callStack true = .ok [v, v] locals' ∧
        evalOperands locals [.move ⟨l, [.field idx fty]⟩, .copy ⟨l, [.field idx fty]⟩]
          borrows globals layouts callerLocals localDecls callStack true = .ub ∧
        evalOperands locals [.move ⟨l, [.field idx fty]⟩, .move ⟨l, [.field idx fty]⟩]
          borrows globals layouts callerLocals localDecls callStack true = .ub ∧
        ∀ (j : FieldIdx) (jty : Ty) (w : Value), j ≠ idx →
          Trusted.Sequence.get? fields j = some w →
          placeTouchesUnion localDecls layouts ⟨l, [.field j jty]⟩ = false →
          valueContainsMovedUninit w = false →
          evalOperands locals [.move ⟨l, [.field idx fty]⟩, .copy ⟨l, [.field j jty]⟩]
            borrows globals layouts callerLocals localDecls callStack true =
              .ok [v, w] locals') ∧
    (moveValueIsZeroSized localDecls layouts
        (placeTyResolved localDecls layouts ⟨l, [.field idx fty]⟩) v = true →
      evalOperand locals (.move ⟨l, [.field idx fty]⟩) borrows globals layouts callerLocals
        localDecls callStack true = .ok v locals ∧
      evalOperands locals [.move ⟨l, [.field idx fty]⟩, .copy ⟨l, [.field idx fty]⟩]
        borrows globals layouts callerLocals localDecls callStack true = .ok [v, v] locals ∧
      (valueListContainsMovedUninit fields = false →
        evalOperands locals [.move ⟨l, [.field idx fty]⟩, .copy ⟨l, []⟩]
          borrows globals layouts callerLocals localDecls callStack true =
            .ok [v, .aggregate variant fields] locals)) := by
  have hidx := seq_lt_of_get? hv
  have hll := seq_lt_of_get? hl
  have hcopy : evalOperand locals (.copy ⟨l, [.field idx fty]⟩) borrows globals layouts
      callerLocals localDecls callStack true = .ok v locals := by
    simp only [evalOperand, guardMovedUninitRead, evalCopyPlaceRead, hl, hnu, readProjectedValue,
      hv, hmv]
  refine ⟨hcopy, fun hzst => ?_, fun hzst => ?_⟩
  · let mval := movedMarkerValue [.field idx fty] v
    let fields' := fields.set idx mval
    let locals' := locals.set l (.init (.aggregate variant fields'))
    have hmark : valueContainsMovedUninit mval = true :=
      movedMarkerValue_contains_of_not_subslice _ v (by intro a b c h; cases h)
    have hl' : Trusted.Sequence.get? locals' l = some (.init (.aggregate variant fields')) :=
      seq_get?_set_self hll _
    have hm' : Trusted.Sequence.get? fields' idx = some mval :=
      seq_get?_set_self hidx _
    have hsf := seq_set?_of_lt hidx mval
    have hsl := seq_set?_of_lt hll (LocalSlot.init (.aggregate variant fields'))
    have hmove : evalOperand locals (.move ⟨l, [.field idx fty]⟩) borrows globals layouts
        callerLocals localDecls callStack true = .ok v locals' := by
      simp only [evalOperand, evalMoveOperandDeinit, evalCopyPlaceRead, hl, hnu, readProjectedValue,
        hv, hmv, hzst, deinitMovedSubPlace, projHasDeref, writeProjectedValue, hsf, hsl, locals',
        fields', mval]
    have hcopy' : evalOperand locals' (.copy ⟨l, [.field idx fty]⟩) borrows globals layouts
        callerLocals localDecls callStack true = .ub := by
      simp only [evalOperand, guardMovedUninitRead, evalCopyPlaceRead, hl', hnu, readProjectedValue,
        hm', hmark]
    have hmove' : evalOperand locals' (.move ⟨l, [.field idx fty]⟩) borrows globals layouts
        callerLocals localDecls callStack true = .ub := by
      simp only [evalOperand, evalMoveOperandDeinit, evalCopyPlaceRead, hl', hnu,
        readProjectedValue, hm', hmark]
    refine ⟨locals', hmove, ?_, ?_, ?_, ?_⟩
    · simp only [evalOperands, hcopy, hmove]
    · simp only [evalOperands, hmove, hcopy']
    · simp only [evalOperands, hmove, hmove']
    · intro j jty w hj hw hnuj hmw
      have hw' : Trusted.Sequence.get? fields' j = some w := by
        dsimp only [fields']; rw [seq_get?_set_ne _ _ hj]; exact hw
      have hcopyJ : evalOperand locals' (.copy ⟨l, [.field j jty]⟩) borrows globals layouts
          callerLocals localDecls callStack true = .ok w locals' := by
        simp only [evalOperand, guardMovedUninitRead, evalCopyPlaceRead, hl', hnuj,
          readProjectedValue, hw', hmw]
      simp only [evalOperands, hmove, hcopyJ]
  · have hmove : evalOperand locals (.move ⟨l, [.field idx fty]⟩) borrows globals layouts
        callerLocals localDecls callStack true = .ok v locals := by
      simp only [evalOperand, evalMoveOperandDeinit, evalCopyPlaceRead, hl, hnu, readProjectedValue,
        hv, hmv, hzst]
    refine ⟨hmove, ?_, fun hfields => ?_⟩
    · simp only [evalOperands, hmove, hcopy]
    · have hrootCopy : evalOperand locals (.copy ⟨l, []⟩) borrows globals layouts callerLocals
          localDecls callStack true = .ok (.aggregate variant fields) locals := by
        simp only [evalOperand, guardMovedUninitRead, evalCopyPlaceRead, hl, readProjectedValue,
          valueContainsMovedUninit, hfields]
      simp only [evalOperands, hmove, hrootCopy]

/-- Local declarations `_0 : (), _1 : ((), u8)` for the typed projected field-move witness. -/
def typedPairZstDecls : List LocalDecl :=
  [{ mutability := .mut, ty := { kind := .tuple [], layoutIdx := 0 }, debugName := .none },
   { mutability := .mut,
     ty := { kind := .tuple [.tuple [], .uint .u8], layoutIdx := 99 },
     debugName := .none }]

/-- **Non-vacuity of both polarities of `trusted_evalOperand_field_move_typed`.**
On `_1 : ((), u8)` holding `(.aggregate 0 [], 42u8)`, `[move _1.0, copy _1]`
returns `[.aggregate 0 [], (.aggregate 0 [], 42u8)]` in the typed context while
faulting with `.ub` in the untyped context (`localDecls = []`), and
`[move _1.1, copy _1]` faults with `.ub` in the typed context. -/
theorem trusted_evalOperand_field_move_typed_zst_nonvacuous :
    ∃ (locals : List LocalSlot) (l : Local) (fty0 fty1 : Ty) (v0 v1 root : Value)
        (layouts : LayoutTable) (localDecls : List LocalDecl),
      v0 ≠ .unit ∧
      Trusted.Sequence.get? locals l = some (.init root) ∧
      placeTouchesUnion localDecls layouts ⟨l, [.field 0 fty0]⟩ = false ∧
      placeTouchesUnion localDecls layouts ⟨l, [.field 1 fty1]⟩ = false ∧
      moveValueIsZeroSized localDecls layouts
        (placeTyResolved localDecls layouts ⟨l, [.field 0 fty0]⟩) v0 = true ∧
      moveValueIsZeroSized [] layouts
        (placeTyResolved [] layouts ⟨l, [.field 0 fty0]⟩) v0 = false ∧
      moveValueIsZeroSized localDecls layouts
        (placeTyResolved localDecls layouts ⟨l, [.field 1 fty1]⟩) v1 = false ∧
      evalOperands locals [.move ⟨l, [.field 0 fty0]⟩, .copy ⟨l, []⟩] [] [] layouts [] localDecls
        [] true = .ok [v0, root] locals ∧
      evalOperands locals [.move ⟨l, [.field 0 fty0]⟩, .copy ⟨l, []⟩] [] [] layouts [] []
        [] true = .ub ∧
      evalOperands locals [.move ⟨l, [.field 1 fty1]⟩, .copy ⟨l, []⟩] [] [] layouts [] localDecls
        [] true = .ub :=
  ⟨[.uninit, .init (.aggregate 0 [.aggregate 0 [], u8Value 42])],
   1,
   { kind := .tuple [], layoutIdx := 0 },
   claimU8Ty,
   .aggregate 0 [],
   u8Value 42,
   .aggregate 0 [.aggregate 0 [], u8Value 42],
   typedZstLayouts,
   typedPairZstDecls,
   typedZst_value_ne_unit, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **Transparent-projection moves (`unwrapUnsafeBinder` / `opaqueCast`) mark the
root slot with `movedMarkerValue` in every state**, faulting on re-read, and
typed `Deref` sub-place `writePlaceValue` (`writeStackThinPtrTypedDeref`)
re-initializes a moved-out `movedUninitValue` field cleanly. -/
theorem trusted_evalOperand_transparent_root_move :
    (∀ (locals locals' : List LocalSlot) (l : Local) (v : Value) (ty : Ty)
        (borrows : List BorrowEntry) (globals : List CapturedAllocation) (layouts : LayoutTable)
        (callerLocals : List LocalSlot) (localDecls : List LocalDecl)
        (callStack : List SavedCallerFrame),
      Trusted.Sequence.get? locals l = some (.init v) →
      Trusted.Sequence.set? locals l (.init (movedMarkerValue [] v)) = some locals' →
      valueContainsMovedUninit v = false →
      (placeTouchesUnion localDecls layouts ⟨l, [.unwrapUnsafeBinder ty]⟩ = false →
        moveValueIsZeroSized localDecls layouts
            (placeTyResolved localDecls layouts ⟨l, [.unwrapUnsafeBinder ty]⟩) v = false →
        evalOperand locals (.move ⟨l, [.unwrapUnsafeBinder ty]⟩) borrows globals layouts
          callerLocals localDecls callStack true = .ok v locals') ∧
      (placeTouchesUnion localDecls layouts ⟨l, [.opaqueCast ty]⟩ = false →
        moveValueIsZeroSized localDecls layouts
            (placeTyResolved localDecls layouts ⟨l, [.opaqueCast ty]⟩) v = false →
        evalOperand locals (.move ⟨l, [.opaqueCast ty]⟩) borrows globals layouts callerLocals
          localDecls callStack true = .ok v locals')) ∧
    evalOperand [.uninit, .init (u8Value 5), .init (.ptr { allocId := 2, offsetBytes := 0 } 8)]
        (.move ⟨1, [.unwrapUnsafeBinder claimU8Ty]⟩) claimDerefBorrows [] claimScalarDerefLayouts
        [] claimU8ScalarDerefDecls [] true =
      .ok (u8Value 5)
        [.uninit, .init movedUninitValue, .init (.ptr { allocId := 2, offsetBytes := 0 } 8)] ∧
    evalOperand
        [.uninit, .init movedUninitValue, .init (.ptr { allocId := 2, offsetBytes := 0 } 8)]
        (.copy ⟨1, []⟩) claimDerefBorrows [] claimScalarDerefLayouts [] claimU8ScalarDerefDecls
        [] true = .ub ∧
    (∃ localsMoved localsReinit : List LocalSlot,
      evalOperand
          [.uninit,
           .init (.aggregate 0 [.aggregate 0 [u8Value 1, u8Value 2],
             .aggregate 0 [u8Value 3, u8Value 4]]),
           .init (.ptr { allocId := 2, offsetBytes := 2 } 8),
           .init (.ptr { allocId := 3, offsetBytes := 2 } 8)]
          (.move ⟨2, [.deref, .field 0 claimU8Ty]⟩) claimDerefBorrows [] claimPairArrLayouts []
          claimPairArrDecls [] true = .ok (u8Value 3) localsMoved ∧
      writePlaceValue localsMoved claimDerefBorrows ⟨2, [.deref, .field 0 claimU8Ty]⟩ (u8Value 9)
          claimPairArrDecls claimPairArrLayouts = .ok localsReinit ∧
      evalOperand localsReinit (.copy ⟨2, [.deref, .field 0 claimU8Ty]⟩) claimDerefBorrows []
          claimPairArrLayouts [] claimPairArrDecls [] true = .ok (u8Value 9) localsReinit ∧
      evalOperand localsReinit (.copy ⟨1, [.constantIndex 1 2 false]⟩) claimDerefBorrows []
          claimPairArrLayouts [] claimPairArrDecls [] true =
        .ok (.aggregate 0 [u8Value 9, u8Value 4]) localsReinit) := by
  refine ⟨?_, rfl, rfl,
    d5TrustedTypedDerefAfterMove,
    [.uninit,
     .init (.aggregate 0 [.aggregate 0 [u8Value 1, u8Value 2],
       .aggregate 0 [u8Value 9, u8Value 4]]),
     .init (.ptr { allocId := 2, offsetBytes := 2 } 8),
     .init (.ptr { allocId := 3, offsetBytes := 2 } 8)],
    rfl, rfl, rfl, rfl⟩
  intro locals locals' l v ty borrows globals layouts callerLocals localDecls callStack hl hset hmv
  refine ⟨fun hnu hzst => ?_, fun hnu hzst => ?_⟩
  · have hm : movedMarkerValue [.unwrapUnsafeBinder ty] v = movedMarkerValue [] v := rfl
    simp only [evalOperand, evalMoveOperandDeinit, evalCopyPlaceRead, hl, hnu, readProjectedValue,
      hmv, hzst, deinitMovedSubPlace, projHasDeref, writeProjectedValue, hm, hset]
  · have hm : movedMarkerValue [.opaqueCast ty] v = movedMarkerValue [] v := rfl
    simp only [evalOperand, evalMoveOperandDeinit, evalCopyPlaceRead, hl, hnu, readProjectedValue,
      hmv, hzst, deinitMovedSubPlace, projHasDeref, writeProjectedValue, hm, hset]

/-- **Full-scalar vs strict-sub-scalar fail-closed vs union byte-window `Deref`
moves (`deinitSubPlaceByteWindow`).** Full-width scalar `Deref` moves set `_1`
to `.uninit` (allowing `*_2 = v` re-initialization); strict sub-scalar `Deref`
moves on a non-union scalar fail closed with `.unsupported` rather than
overwriting `_1` with `movedUninitValue` and poisoning unmoved sibling bytes;
whereas sub-byte `Deref` moves on `union U { a: u8, b: u16 }` deinitialize byte
`0` via its `AbstractByte` overlay while preserving the unmoved byte `1`. -/
theorem trusted_evalOperand_subscalar_vs_union_deref_move :
    let u16Init : List LocalSlot :=
      [.uninit, .init (.scalar ⟨770, 2⟩),
       .init (.ptr { allocId := 2, offsetBytes := 0 } 8),
       .init (.ptr { allocId := 2, offsetBytes := 0 } 8),
       .init (.ptr { allocId := 3, offsetBytes := 1 } 8)]
    let u16Moved : List LocalSlot :=
      [.uninit, .uninit,
       .init (.ptr { allocId := 2, offsetBytes := 0 } 8),
       .init (.ptr { allocId := 2, offsetBytes := 0 } 8),
       .init (.ptr { allocId := 3, offsetBytes := 1 } 8)]
    evalOperand u16Init (.move ⟨2, [.deref]⟩) claimDerefBorrows [] claimScalarDerefLayouts []
       claimU16ScalarDerefDecls [] true = .ok (.scalar ⟨770, 2⟩) u16Moved ∧
    writePlaceValue u16Moved claimDerefBorrows ⟨2, [.deref]⟩ (.scalar ⟨1284, 2⟩)
       claimU16ScalarDerefDecls claimScalarDerefLayouts =
      .ok [.uninit, .init (.scalar ⟨1284, 2⟩),
           .init (.ptr { allocId := 2, offsetBytes := 0 } 8),
           .init (.ptr { allocId := 2, offsetBytes := 0 } 8),
           .init (.ptr { allocId := 3, offsetBytes := 1 } 8)] ∧
    evalOperand u16Init (.copy ⟨3, [.deref]⟩) claimDerefBorrows [] claimScalarDerefLayouts []
       claimU16ScalarDerefDecls [] true = .ok (u8Value 2) u16Init ∧
    evalOperand u16Init (.copy ⟨4, [.deref]⟩) claimDerefBorrows [] claimScalarDerefLayouts []
       claimU16ScalarDerefDecls [] true = .ok (u8Value 3) u16Init ∧
    evalOperand u16Init (.move ⟨3, [.deref]⟩) claimDerefBorrows [] claimScalarDerefLayouts []
       claimU16ScalarDerefDecls [] true = .unsupported ∧
    ∃ localsUnion' : List LocalSlot,
      evalOperand
          [.uninit, .init (.aggregate 0 [.unit, .scalar ⟨770, 2⟩]),
           .init (.ptr { allocId := 2, offsetBytes := 0 } 8),
           .init (.ptr { allocId := 3, offsetBytes := 1 } 8)]
          (.move ⟨2, [.deref]⟩) claimDerefBorrows [] claimUnionPtrLayouts [] claimUnionPtrDecls []
          true = .ok (u8Value 2) localsUnion' ∧
      evalOperand localsUnion' (.copy ⟨2, [.deref]⟩) claimDerefBorrows [] claimUnionPtrLayouts []
        claimUnionPtrDecls [] true = .ub ∧
      evalOperand localsUnion' (.copy ⟨1, [.field 1 claimU16Ty]⟩) claimDerefBorrows []
        claimUnionPtrLayouts [] claimUnionPtrDecls [] true = .ub ∧
      evalOperand localsUnion' (.copy ⟨3, [.deref]⟩) claimDerefBorrows [] claimUnionPtrLayouts []
        claimUnionPtrDecls [] true = .ok (u8Value 3) localsUnion' :=
  ⟨rfl, rfl, rfl, rfl, rfl,
   [.uninit, .init (.aggregate 0 [.unit, .unit, .aggregate 0 [.scalar ⟨0, 0⟩, .scalar ⟨3, 1⟩]]),
    .init (.ptr { allocId := 2, offsetBytes := 0 } 8),
    .init (.ptr { allocId := 3, offsetBytes := 1 } 8)],
   rfl, rfl, rfl, rfl⟩

/-- **Projected `.constantIndex` and dynamic `.index` element moves in every
non-union typed context (all states, any `localDecls`).** Generalizes
`trusted_evalOperand_elem_move_deinit` and `trusted_evalOperand_index_move_deinit`
from `localDecls = []` to arbitrary typed frames in which the element projection
does not touch a union, covering both non-ZST element deinitialization (with
left-to-right `evalOperands` ordering and sibling preservation) and ZST element
preservation (`D9`). -/
theorem trusted_evalOperand_elem_and_index_move_typed :
    (∀ (locals : List LocalSlot) (l : Local) (elems : List Value) (idx minLen : Nat) (v : Value)
        (borrows : List BorrowEntry) (globals : List CapturedAllocation) (layouts : LayoutTable)
        (callerLocals : List LocalSlot) (localDecls : List LocalDecl)
        (callStack : List SavedCallerFrame),
      Trusted.Sequence.get? locals l = some (.init (.aggregate 0 elems)) →
      minLen ≤ elems.length →
      Trusted.Sequence.get? elems idx = some v →
      placeTouchesUnion localDecls layouts ⟨l, [.constantIndex idx minLen false]⟩ = false →
      valueContainsMovedUninit v = false →
      evalOperand locals (.copy ⟨l, [.constantIndex idx minLen false]⟩) borrows globals layouts
        callerLocals localDecls callStack true = .ok v locals ∧
      (moveValueIsZeroSized localDecls layouts
          (placeTyResolved localDecls layouts ⟨l, [.constantIndex idx minLen false]⟩) v = false →
        ∃ locals',
          evalOperand locals (.move ⟨l, [.constantIndex idx minLen false]⟩) borrows globals
            layouts callerLocals localDecls callStack true = .ok v locals' ∧
          evalOperands locals
            [.copy ⟨l, [.constantIndex idx minLen false]⟩,
             .move ⟨l, [.constantIndex idx minLen false]⟩]
            borrows globals layouts callerLocals localDecls callStack true = .ok [v, v] locals' ∧
          evalOperands locals
            [.move ⟨l, [.constantIndex idx minLen false]⟩,
             .copy ⟨l, [.constantIndex idx minLen false]⟩]
            borrows globals layouts callerLocals localDecls callStack true = .ub ∧
          evalOperands locals
            [.move ⟨l, [.constantIndex idx minLen false]⟩,
             .move ⟨l, [.constantIndex idx minLen false]⟩]
            borrows globals layouts callerLocals localDecls callStack true = .ub ∧
          ∀ (j : Nat) (w : Value), j ≠ idx →
            Trusted.Sequence.get? elems j = some w →
            placeTouchesUnion localDecls layouts ⟨l, [.constantIndex j minLen false]⟩ = false →
            valueContainsMovedUninit w = false →
            evalOperands locals
              [.move ⟨l, [.constantIndex idx minLen false]⟩,
               .copy ⟨l, [.constantIndex j minLen false]⟩]
              borrows globals layouts callerLocals localDecls callStack true =
                .ok [v, w] locals') ∧
      (moveValueIsZeroSized localDecls layouts
          (placeTyResolved localDecls layouts ⟨l, [.constantIndex idx minLen false]⟩) v = true →
        evalOperand locals (.move ⟨l, [.constantIndex idx minLen false]⟩) borrows globals layouts
          callerLocals localDecls callStack true = .ok v locals ∧
        evalOperands locals
          [.move ⟨l, [.constantIndex idx minLen false]⟩,
           .copy ⟨l, [.constantIndex idx minLen false]⟩]
          borrows globals layouts callerLocals localDecls callStack true = .ok [v, v] locals ∧
        (valueListContainsMovedUninit elems = false →
          evalOperands locals
            [.move ⟨l, [.constantIndex idx minLen false]⟩, .copy ⟨l, []⟩]
            borrows globals layouts callerLocals localDecls callStack true =
              .ok [v, .aggregate 0 elems] locals))) ∧
    (∀ (locals : List LocalSlot) (l idxLocal : Local) (elems : List Value) (idx : Nat) (v : Value)
        (borrows : List BorrowEntry) (globals : List CapturedAllocation) (layouts : LayoutTable)
        (callerLocals : List LocalSlot) (localDecls : List LocalDecl)
        (callStack : List SavedCallerFrame),
      l ≠ idxLocal →
      Trusted.Sequence.get? locals l = some (.init (.aggregate 0 elems)) →
      Trusted.Sequence.get? locals idxLocal =
        some (.init (.scalar { bits := idx, sizeBytes := 8 })) →
      Trusted.Sequence.get? elems idx = some v →
      placeTouchesUnion localDecls layouts ⟨l, [.index idxLocal]⟩ = false →
      valueContainsMovedUninit v = false →
      evalOperand locals (.copy ⟨l, [.index idxLocal]⟩) borrows globals layouts
        callerLocals localDecls callStack true = .ok v locals ∧
      (moveValueIsZeroSized localDecls layouts
          (placeTyResolved localDecls layouts ⟨l, [.index idxLocal]⟩) v = false →
        ∃ locals',
          evalOperand locals (.move ⟨l, [.index idxLocal]⟩) borrows globals layouts
            callerLocals localDecls callStack true = .ok v locals' ∧
          evalOperands locals [.copy ⟨l, [.index idxLocal]⟩, .move ⟨l, [.index idxLocal]⟩]
            borrows globals layouts callerLocals localDecls callStack true = .ok [v, v] locals' ∧
          evalOperands locals [.move ⟨l, [.index idxLocal]⟩, .copy ⟨l, [.index idxLocal]⟩]
            borrows globals layouts callerLocals localDecls callStack true = .ub ∧
          evalOperands locals [.move ⟨l, [.index idxLocal]⟩, .move ⟨l, [.index idxLocal]⟩]
            borrows globals layouts callerLocals localDecls callStack true = .ub ∧
          ∀ (j : Nat) (w : Value), j ≠ idx →
            Trusted.Sequence.get? elems j = some w →
            placeTouchesUnion localDecls layouts ⟨l, [.constantIndex j 0 false]⟩ = false →
            valueContainsMovedUninit w = false →
            evalOperands locals
              [.move ⟨l, [.index idxLocal]⟩, .copy ⟨l, [.constantIndex j 0 false]⟩]
              borrows globals layouts callerLocals localDecls callStack true =
                .ok [v, w] locals') ∧
      (moveValueIsZeroSized localDecls layouts
          (placeTyResolved localDecls layouts ⟨l, [.index idxLocal]⟩) v = true →
        evalOperand locals (.move ⟨l, [.index idxLocal]⟩) borrows globals layouts callerLocals
          localDecls callStack true = .ok v locals ∧
        evalOperands locals [.move ⟨l, [.index idxLocal]⟩, .copy ⟨l, [.index idxLocal]⟩]
          borrows globals layouts callerLocals localDecls callStack true = .ok [v, v] locals ∧
        (valueListContainsMovedUninit elems = false →
          evalOperands locals [.move ⟨l, [.index idxLocal]⟩, .copy ⟨l, []⟩]
            borrows globals layouts callerLocals localDecls callStack true =
              .ok [v, .aggregate 0 elems] locals))) := by
  refine ⟨?_, ?_⟩
  · intro locals l elems idx minLen v borrows globals layouts callerLocals localDecls callStack
      hl hmin hv hnu hmv
    have hidx := seq_lt_of_get? hv
    have hll := seq_lt_of_get? hl
    have hble : Nat.ble minLen (Trusted.Sequence.length elems) = true := Nat.ble_eq.mpr hmin
    have hcopy : evalOperand locals (.copy ⟨l, [.constantIndex idx minLen false]⟩) borrows globals
        layouts callerLocals localDecls callStack true = .ok v locals := by
      simp only [evalOperand, guardMovedUninitRead, evalCopyPlaceRead, hl, hnu, readProjectedValue,
        hble, hv, hmv]
    refine ⟨hcopy, fun hzst => ?_, fun hzst => ?_⟩
    · let mval := movedMarkerValue [.constantIndex idx minLen false] v
      let elems' := elems.set idx mval
      let locals' := locals.set l (.init (.aggregate 0 elems'))
      have hmark : valueContainsMovedUninit mval = true :=
        movedMarkerValue_contains_of_not_subslice _ v (by intro a b c h; cases h)
      have hl' : Trusted.Sequence.get? locals' l = some (.init (.aggregate 0 elems')) :=
        seq_get?_set_self hll _
      have hm' : Trusted.Sequence.get? elems' idx = some mval :=
        seq_get?_set_self hidx _
      have hble' : Nat.ble minLen (Trusted.Sequence.length elems') = true := by
        simp only [elems', Trusted.Sequence.length, List.length_set]; exact Nat.ble_eq.mpr hmin
      have hse := seq_set?_of_lt hidx mval
      have hsl := seq_set?_of_lt hll (LocalSlot.init (.aggregate 0 elems'))
      have hmove : evalOperand locals (.move ⟨l, [.constantIndex idx minLen false]⟩) borrows
          globals layouts callerLocals localDecls callStack true = .ok v locals' := by
        simp only [evalOperand, evalMoveOperandDeinit, evalCopyPlaceRead, hl, hnu,
          readProjectedValue, hble, hv, hmv, hzst, deinitMovedSubPlace, projHasDeref,
          writeProjectedValue, hse, hsl, locals', elems', mval]
      have hcopy' : evalOperand locals' (.copy ⟨l, [.constantIndex idx minLen false]⟩) borrows
          globals layouts callerLocals localDecls callStack true = .ub := by
        simp only [evalOperand, guardMovedUninitRead, evalCopyPlaceRead, hl', hnu,
          readProjectedValue, hble', hm', hmark]
      have hmove' : evalOperand locals' (.move ⟨l, [.constantIndex idx minLen false]⟩) borrows
          globals layouts callerLocals localDecls callStack true = .ub := by
        simp only [evalOperand, evalMoveOperandDeinit, evalCopyPlaceRead, hl', hnu,
          readProjectedValue, hble', hm', hmark]
      refine ⟨locals', hmove, ?_, ?_, ?_, ?_⟩
      · simp only [evalOperands, hcopy, hmove]
      · simp only [evalOperands, hmove, hcopy']
      · simp only [evalOperands, hmove, hmove']
      · intro j w hj hw hnuj hmw
        have hw' : Trusted.Sequence.get? elems' j = some w := by
          dsimp only [elems']; rw [seq_get?_set_ne _ _ hj]; exact hw
        have hcopyJ : evalOperand locals' (.copy ⟨l, [.constantIndex j minLen false]⟩) borrows
            globals layouts callerLocals localDecls callStack true = .ok w locals' := by
          simp only [evalOperand, guardMovedUninitRead, evalCopyPlaceRead, hl', hnuj,
            readProjectedValue, hble', hw', hmw]
        simp only [evalOperands, hmove, hcopyJ]
    · have hmove : evalOperand locals (.move ⟨l, [.constantIndex idx minLen false]⟩) borrows
          globals layouts callerLocals localDecls callStack true = .ok v locals := by
        simp only [evalOperand, evalMoveOperandDeinit, evalCopyPlaceRead, hl, hnu,
          readProjectedValue, hble, hv, hmv, hzst]
      refine ⟨hmove, ?_, fun helems => ?_⟩
      · simp only [evalOperands, hmove, hcopy]
      · have hrootCopy : evalOperand locals (.copy ⟨l, []⟩) borrows globals layouts callerLocals
            localDecls callStack true = .ok (.aggregate 0 elems) locals := by
          simp only [evalOperand, guardMovedUninitRead, evalCopyPlaceRead, hl, readProjectedValue,
            valueContainsMovedUninit, helems]
        simp only [evalOperands, hmove, hrootCopy]
  · intro locals l idxLocal elems idx v borrows globals layouts callerLocals localDecls callStack
      hne hl hidxLocal hv hnu hmv
    have hidx := seq_lt_of_get? hv
    have hll := seq_lt_of_get? hl
    have hcopy : evalOperand locals (.copy ⟨l, [.index idxLocal]⟩) borrows globals layouts
        callerLocals localDecls callStack true = .ok v locals := by
      simp only [evalOperand, guardMovedUninitRead, evalCopyPlaceRead, hl, hnu, readProjectedValue,
        hidxLocal, hv, hmv]
    refine ⟨hcopy, fun hzst => ?_, fun hzst => ?_⟩
    · let mval := movedMarkerValue [.index idxLocal] v
      let elems' := elems.set idx mval
      let locals' := locals.set l (.init (.aggregate 0 elems'))
      have hmark : valueContainsMovedUninit mval = true :=
        movedMarkerValue_contains_of_not_subslice _ v (by intro a b c h; cases h)
      have hl' : Trusted.Sequence.get? locals' l = some (.init (.aggregate 0 elems')) :=
        seq_get?_set_self hll _
      have hidxLocal' : Trusted.Sequence.get? locals' idxLocal =
          some (.init (.scalar { bits := idx, sizeBytes := 8 })) := by
        dsimp only [locals']; rw [seq_get?_set_ne _ _ (Ne.symm hne)]; exact hidxLocal
      have hm' : Trusted.Sequence.get? elems' idx = some mval :=
        seq_get?_set_self hidx _
      have hble0 : Nat.ble 0 (Trusted.Sequence.length elems') = true := by
        simp only [Nat.ble_eq]; omega
      have hse := seq_set?_of_lt hidx mval
      have hsl := seq_set?_of_lt hll (LocalSlot.init (.aggregate 0 elems'))
      have hmove : evalOperand locals (.move ⟨l, [.index idxLocal]⟩) borrows globals layouts
          callerLocals localDecls callStack true = .ok v locals' := by
        simp only [evalOperand, evalMoveOperandDeinit, evalCopyPlaceRead, hl, hnu,
          readProjectedValue, hidxLocal, hv, hmv, hzst, deinitMovedSubPlace, projHasDeref,
          writeProjectedValue, hse, hsl, locals', elems', mval]
      have hcopy' : evalOperand locals' (.copy ⟨l, [.index idxLocal]⟩) borrows globals layouts
          callerLocals localDecls callStack true = .ub := by
        simp only [evalOperand, guardMovedUninitRead, evalCopyPlaceRead, hl', hnu,
          readProjectedValue, hidxLocal', hm', hmark]
      have hmove' : evalOperand locals' (.move ⟨l, [.index idxLocal]⟩) borrows globals layouts
          callerLocals localDecls callStack true = .ub := by
        simp only [evalOperand, evalMoveOperandDeinit, evalCopyPlaceRead, hl', hnu,
          readProjectedValue, hidxLocal', hm', hmark]
      refine ⟨locals', hmove, ?_, ?_, ?_, ?_⟩
      · simp only [evalOperands, hcopy, hmove]
      · simp only [evalOperands, hmove, hcopy']
      · simp only [evalOperands, hmove, hmove']
      · intro j w hj hw hnuj hmw
        have hw' : Trusted.Sequence.get? elems' j = some w := by
          dsimp only [elems']; rw [seq_get?_set_ne _ _ hj]; exact hw
        have hcopyJ : evalOperand locals' (.copy ⟨l, [.constantIndex j 0 false]⟩) borrows globals
            layouts callerLocals localDecls callStack true = .ok w locals' := by
          simp only [evalOperand, guardMovedUninitRead, evalCopyPlaceRead, hl', hnuj,
            readProjectedValue, hble0, hw', hmw]
        simp only [evalOperands, hmove, hcopyJ]
    · have hmove : evalOperand locals (.move ⟨l, [.index idxLocal]⟩) borrows globals layouts
          callerLocals localDecls callStack true = .ok v locals := by
        simp only [evalOperand, evalMoveOperandDeinit, evalCopyPlaceRead, hl, hnu,
          readProjectedValue, hidxLocal, hv, hmv, hzst]
      refine ⟨hmove, ?_, fun helems => ?_⟩
      · simp only [evalOperands, hmove, hcopy]
      · have hrootCopy : evalOperand locals (.copy ⟨l, []⟩) borrows globals layouts callerLocals
            localDecls callStack true = .ok (.aggregate 0 elems) locals := by
          simp only [evalOperand, guardMovedUninitRead, evalCopyPlaceRead, hl, readProjectedValue,
            valueContainsMovedUninit, helems]
        simp only [evalOperands, hmove, hrootCopy]

/-- Layout table `[(), [(); 2], u8, [u8; 2], usize]` for typed element-move witnesses. -/
def typedArrElemLayouts : LayoutTable :=
  { emptyLayoutTable with
    entries := [
      typedZstUnitLayout,
      { size := ⟨0⟩, align := ⟨1⟩, backendRepr := .memory, fields := .array ⟨0⟩ 2,
        variants := .single 0, isUninhabited := false, fieldLayouts := [0] },
      claimU8Layout,
      { size := ⟨2⟩, align := ⟨1⟩, backendRepr := .memory, fields := .array ⟨1⟩ 2,
        variants := .single 0, isUninhabited := false, fieldLayouts := [2] },
      { size := ⟨8⟩, align := ⟨8⟩, backendRepr := .scalar (.initialized (.int 64 false)
          { start := 0, end_ := 18446744073709551615 }),
        fields := .primitive, variants := .single 0, isUninhabited := false }] }

/-- Local declarations `_0 : (), _1 : [(); 2], _2 : usize` for the ZST element-move witness. -/
def typedArrZstDecls : List LocalDecl :=
  [{ mutability := .mut, ty := { kind := .tuple [], layoutIdx := 0 }, debugName := .none },
   { mutability := .mut, ty := { kind := .array (.tuple []) 2, layoutIdx := 1 }, debugName := .none },
   { mutability := .not, ty := { kind := .uint .usize, layoutIdx := 4 }, debugName := .none }]

/-- Local declarations `_0 : u8, _1 : [u8; 2], _2 : usize` for the non-ZST element-move witness. -/
def typedArrU8Decls : List LocalDecl :=
  [{ mutability := .mut, ty := { kind := .uint .u8, layoutIdx := 2 }, debugName := .none },
   { mutability := .mut, ty := { kind := .array (.uint .u8) 2, layoutIdx := 3 }, debugName := .none },
   { mutability := .not, ty := { kind := .uint .usize, layoutIdx := 4 }, debugName := .none }]

/-- **Non-vacuity of both polarities of `trusted_evalOperand_elem_and_index_move_typed`.**
On `_1 : [(); 2]` holding non-`.unit` `.aggregate 0 []` elements, both
`[move _1[0], copy _1]` (`.constantIndex`) and `[move _1[_2], copy _1]` (`.index`)
succeed in the typed context while faulting with `.ub` in the untyped context,
whereas on `_1 : [u8; 2]` `[move _1[0], copy _1]` faults with `.ub`. -/
theorem trusted_evalOperand_elem_and_index_move_typed_zst_nonvacuous :
    ∃ (localsZst localsU8 : List LocalSlot) (l idxLocal : Local) (vZst rootZst vU8 : Value)
        (layouts : LayoutTable) (declsZst declsU8 : List LocalDecl),
      l ≠ idxLocal ∧ vZst ≠ .unit ∧
      Trusted.Sequence.get? localsZst l = some (.init rootZst) ∧
      placeTouchesUnion declsZst layouts ⟨l, [.constantIndex 0 2 false]⟩ = false ∧
      placeTouchesUnion declsZst layouts ⟨l, [.index idxLocal]⟩ = false ∧
      placeTouchesUnion declsU8 layouts ⟨l, [.constantIndex 0 2 false]⟩ = false ∧
      moveValueIsZeroSized declsZst layouts
        (placeTyResolved declsZst layouts ⟨l, [.constantIndex 0 2 false]⟩) vZst = true ∧
      moveValueIsZeroSized [] layouts
        (placeTyResolved [] layouts ⟨l, [.constantIndex 0 2 false]⟩) vZst = false ∧
      moveValueIsZeroSized declsU8 layouts
        (placeTyResolved declsU8 layouts ⟨l, [.constantIndex 0 2 false]⟩) vU8 = false ∧
      evalOperands localsZst [.move ⟨l, [.constantIndex 0 2 false]⟩, .copy ⟨l, []⟩] [] [] layouts
        [] declsZst [] true = .ok [vZst, rootZst] localsZst ∧
      evalOperands localsZst [.move ⟨l, [.index idxLocal]⟩, .copy ⟨l, []⟩] [] [] layouts []
        declsZst [] true = .ok [vZst, rootZst] localsZst ∧
      evalOperands localsZst [.move ⟨l, [.constantIndex 0 2 false]⟩, .copy ⟨l, []⟩] [] [] layouts
        [] [] [] true = .ub ∧
      evalOperands localsU8 [.move ⟨l, [.constantIndex 0 2 false]⟩, .copy ⟨l, []⟩] [] [] layouts
        [] declsU8 [] true = .ub :=
  ⟨[.uninit,
    .init (.aggregate 0 [.aggregate 0 [], .aggregate 0 []]),
    .init (.scalar { bits := 0, sizeBytes := 8 })],
   [.uninit,
    .init (.aggregate 0 [u8Value 10, u8Value 20]),
    .init (.scalar { bits := 0, sizeBytes := 8 })],
   1, 2, .aggregate 0 [], .aggregate 0 [.aggregate 0 [], .aggregate 0 []], u8Value 10,
   typedArrElemLayouts, typedArrZstDecls, typedArrU8Decls,
   by decide, typedZst_value_ne_unit, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **`TrustedProjectedMoveDeinitClaim`** (proved here; restated in
`Anneal.Mir.Correspondence.Claims`). -/
theorem trustedProjectedMoveDeinitClaim_proof : TrustedProjectedMoveDeinitClaim :=
  ⟨trusted_evalOperand_root_move_deinits,
   trusted_evalOperand_projected_move_eq_copy,
   trusted_evalOperand_field_move_deinit,
   trusted_evalOperand_elem_move_deinit,
   trusted_evalOperand_index_move_deinit,
   trusted_evalOperand_subslice_move_deinit,
   trusted_evalOperand_union_move_deinit,
   trusted_evalOperand_deref_move_deinit,
   trusted_evalOperand_typed_deref_move_deinit,
   trusted_evalOperand_slice_deref_move_deinit,
   trusted_evalOperand_movedUninit_read_ub,
   trusted_evalOperand_movedUninit_read_nonvacuous,
   trusted_evalOperands_field_move_order,
   trusted_evalOperands_deref_move_order,
   trusted_evalOperand_root_move_typed,
   trusted_evalOperand_root_move_typed_zst_nonvacuous,
   trusted_evalOperand_field_move_typed,
   trusted_evalOperand_field_move_typed_zst_nonvacuous,
   trusted_evalOperand_transparent_root_move,
   trusted_evalOperand_subscalar_vs_union_deref_move,
   trusted_evalOperand_elem_and_index_move_typed,
   trusted_evalOperand_elem_and_index_move_typed_zst_nonvacuous⟩

/-! ## Part 10c — Fail-closed pointer constants, destination-first
assignments, and a non-vacuity witness for the assignment Tree Borrows theorem -/

/-- Pointer constants (`ConstValue.scalar (.ptr ..)`) refer to *global*
allocations, which the shared machine does not model; resolving them into the
heap of stack locals would let a constant forge a pointer to a local (allocation
ids of globals and stack locals are different namespaces). They therefore fail
closed in both machines. -/
theorem constSem_ptr_fails_closed (sty : Option SemTy) (p : ProvenancePtr) (sz : Nat) :
    constSem sty (.scalar (.ptr p sz)) = none := by
  cases sty <;> rfl

/-- `_1 = (7, 8); _2 = const ptr{alloc 0, off 0}; _0 = copy (*_2)`: reading the
stack local `_1` through a *global* pointer constant fails closed. -/
def constPtrForgeProg : V2026Prog := prog1 <| mkBody "constptr" 0 [tU8, tPair, tRaw]
  [blk [asg (loc 1) (.aggregate .tuple [cU8 7, cU8 8]),
        asg (loc 2) (.use (.constant ⟨tRaw, .scalar (.ptr ⟨0, 0⟩ 8)⟩)),
        asg (loc 0) (.use (.copy (drf 2)))] .return_]

theorem canary_const_ptr_fails_closed :
    bothObs constPtrForgeProg = (.unsupported, .unsupported) := by decide

/-- The `D5` state just before `_4 = move (*_2)` (`_1` in memory with a sibling
`.frozen` shared borrow `_3` and the raw pointer `_2`). -/
def d5PreMoveState : Option PState :=
  let p := d5Prog (asg (loc 4) (.use (.move (drf 2)))) (.use (.copy (loc 4)))
  match annealInit p [] with
  | .ok st =>
    match annealRun p 3 st with
    | .running st' => some st'
    | _ => none
  | .error _ => none

def d5MoveOp : SemOperand := .move ⟨2, (.rawPtr .mut kU8, lay (.rawPtr .mut kU8)), [.deref]⟩

/-- Executable check of all premises and the conclusion of
`deinitMovedPlace_assignUse_preserves_tb_tags` on the `D5` move. -/
def tbAssignWitness : Bool :=
  match d5PreMoveState with
  | some st =>
    match twoPhaseAssignUse true 64 st d5MoveOp (.imm 4), nth? st.borrows 0 with
    | .ok st₁, some e =>
      permIsFrozen e.perm && !(entryOverlapsDest e (.imm 4)) &&
        decide ((nth? st₁.borrows 0).map (fun e' => permIsFrozen e'.perm) = some true) &&
        decide (st₁.borrows.length = st.borrows.length)
    | _, _ => false
  | none => false

/-- Non-vacuity: the premises of `deinitMovedPlace_assignUse_preserves_tb_tags`
are satisfiable (the `D5` move into `_4` succeeds with a sibling `.frozen`
borrow that does not overlap the destination, which stays `.frozen`). -/
theorem deinitMovedPlace_assignUse_preserves_tb_tags_nonvacuous : tbAssignWitness = true := by
  decide

/-! ## Part 10d — Step-boundary latch invariant (`pendingMoveDeinit = false`) -/

theorem setLocalE_latch {st st' : PState} {l : Local} {v : PSlot}
    (h : setLocalE st l v = .ok st') : st'.pendingMoveDeinit = st.pendingMoveDeinit := by
  unfold setLocalE at h
  cases hf : st.frames with
  | nil => rw [hf] at h; cases h
  | cons fr rest =>
    rw [hf] at h; simp only at h
    cases hs : setNth? fr.locals l v with
    | none => rw [hs] at h; cases h
    | some ls => rw [hs] at h; cases h; rfl

theorem putHeap_latch {st st' : PState} {a : Nat} {b : Bytes}
    (h : putHeap st a b = .ok st') : st'.pendingMoveDeinit = st.pendingMoveDeinit := by
  unfold putHeap at h
  cases hs : setNth? st.heap a (some b) with
  | none => rw [hs] at h; cases h
  | some hp => rw [hs] at h; cases h; rfl

theorem loadMPlace_latch {st st' : PState} {mp : MPlace} {b : Bytes}
    (h : loadMPlace st mp = .ok (b, st')) : st'.pendingMoveDeinit = st.pendingMoveDeinit := by
  unfold loadMPlace at h
  cases hg : heapGet st mp.alloc with
  | none => rw [hg] at h; cases h
  | some bs =>
    rw [hg] at h; simp only at h
    cases hb : Nat.ble (mp.offset + mp.size) bs.length with
    | false => rw [hb] at h; cases h
    | true =>
      rw [hb] at h
      cases ht : tbAccess .read st.borrows mp.alloc mp.tag mp.offset mp.size with
      | none => rw [ht] at h; cases h
      | some bs' => rw [ht] at h; cases h; rfl

theorem storeMPlace_latch {st st' : PState} {mp : MPlace} {b : Bytes}
    (h : storeMPlace st mp b = .ok st') : st'.pendingMoveDeinit = st.pendingMoveDeinit := by
  unfold storeMPlace at h
  cases hg : heapGet st mp.alloc with
  | none => rw [hg] at h; cases h
  | some bs =>
    rw [hg] at h; simp only at h
    cases hb : (Nat.ble (mp.offset + mp.size) bs.length && Nat.beq b.length mp.size) with
    | false => rw [hb] at h; cases h
    | true =>
      rw [hb] at h; simp only at h
      cases ht : tbAccess .write st.borrows mp.alloc mp.tag mp.offset mp.size with
      | none => rw [ht] at h; cases h
      | some bs' => rw [ht] at h; simp only at h; have hl := putHeap_latch h; exact hl

theorem deinitMPlaceRaw_latch {st st' : PState} {mp : MPlace}
    (h : deinitMPlaceRaw st mp = .ok st') : st'.pendingMoveDeinit = st.pendingMoveDeinit := by
  unfold deinitMPlaceRaw at h
  cases hg : heapGet st mp.alloc with
  | none => rw [hg] at h; cases h
  | some b =>
    rw [hg] at h; simp only at h
    cases hb : Nat.ble (mp.offset + mp.size) b.length with
    | false => rw [hb] at h; cases h
    | true => rw [hb] at h; exact putHeap_latch h

theorem writeDest_latch {st st' : PState} {d : DestPlace} {b : Bytes}
    (h : writeDest st d b = .ok st') : st'.pendingMoveDeinit = st.pendingMoveDeinit := by
  cases d with
  | imm l => exact setLocalE_latch h
  | mem mp => exact storeMPlace_latch h

theorem readOpBytes_latch {st st' : PState} {o : OpTy} {b : Bytes}
    (h : readOpBytes st o = .ok (b, st')) : st'.pendingMoveDeinit = st.pendingMoveDeinit := by
  cases o with
  | immediate _ => cases h; rfl
  | indirect mp => exact loadMPlace_latch h

theorem copyMemPath_latch {st st' : PState} {src : MPlace} {d : DestPlace}
    (h : copyMemPath st src d = .ok st') : st'.pendingMoveDeinit = st.pendingMoveDeinit := by
  cases d with
  | imm _ => cases h
  | mem dmp =>
    simp only [copyMemPath] at h
    cases hl : loadMPlace st src with
    | error e => rw [hl] at h; cases h
    | ok r =>
      rw [hl] at h; simp only at h
      cases ho : placesOverlap src dmp with
      | true => rw [ho] at h; cases h
      | false => rw [ho] at h; exact (storeMPlace_latch h).trans (loadMPlace_latch hl)

/-- Every successful `twoPhaseReadOperand true` (and `annealReadOperand`) step
leaves `pendingMoveDeinit = false`, regardless of the incoming latch state. -/
theorem twoPhaseReadOperand_true_latch_clear (pb : Nat) (st st' : PState)
    (op : SemOperand) (b : Bytes)
    (h : twoPhaseReadOperand true pb st op = .ok (b, st')) :
    st'.pendingMoveDeinit = false := by
  rw [twoPhaseReadOperand_true_eq] at h
  cases op with
  | const cb ty =>
    simp only [annealReadOperand] at h
    cases hv : checkValid ty cb <;> rw [hv] at h <;> cases h; rfl
  | copy p =>
    simp only [annealReadOperand] at h
    cases he : evalPlaceToOp pb (clearLatch st) p with
    | error e => rw [he] at h; cases h
    | ok r =>
      obtain ⟨o, ty⟩ := r; rw [he] at h; simp only at h
      cases hr : readOpBytes (clearLatch st) o with
      | error e => rw [hr] at h; cases h
      | ok r' =>
        obtain ⟨rb, st₁⟩ := r'; rw [hr] at h; simp only at h
        cases hv : checkValid ty rb <;> rw [hv] at h <;> cases h
        exact readOpBytes_latch hr
  | move p =>
    simp only [annealReadOperand] at h
    cases he : evalPlaceToOp pb (clearLatch st) p with
    | error e => rw [he] at h; cases h
    | ok r =>
      obtain ⟨o, ty⟩ := r; rw [he] at h
      cases o with
      | immediate bb =>
        simp only at h
        cases hp : p.projs with
        | cons _ _ => rw [hp] at h; cases h
        | nil =>
          rw [hp] at h; simp only at h
          cases hs : setLocalE (clearLatch st) p.local_ (.imm (uninitBytes bb.length)) with
          | error e => rw [hs] at h; cases h
          | ok st₁ =>
            rw [hs] at h; simp only at h
            cases hv : checkValid ty bb <;> rw [hv] at h <;> cases h; rfl
      | indirect mp =>
        simp only at h
        cases hl : loadMPlace (clearLatch st) mp with
        | error e => rw [hl] at h; cases h
        | ok r' =>
          obtain ⟨bb, st₁⟩ := r'; rw [hl] at h; simp only at h
          cases hv : checkValid ty bb with
          | error e => rw [hv] at h; cases h
          | ok u =>
            rw [hv] at h; simp only at h
            cases hd : deinitMPlaceRaw st₁ mp with
            | error e => rw [hd] at h; cases h
            | ok st₂ =>
              rw [hd] at h; cases h
              exact (deinitMPlaceRaw_latch hd).trans (loadMPlace_latch hl)

/-- Every successful `twoPhaseAssignUse true` (and `annealAssignUse`) step
leaves `pendingMoveDeinit = false`, regardless of the incoming latch state. -/
theorem twoPhaseAssignUse_true_latch_clear (pb : Nat) (st st' : PState)
    (op : SemOperand) (d : DestPlace)
    (h : twoPhaseAssignUse true pb st op d = .ok st') :
    st'.pendingMoveDeinit = false := by
  rw [twoPhaseAssignUse_true_eq] at h
  cases op with
  | const cb ty =>
    simp only [annealAssignUse] at h
    cases hv : checkValid ty cb with
    | error e => rw [hv] at h; cases h
    | ok u => rw [hv] at h; exact writeDest_latch h
  | copy p =>
    simp only [annealAssignUse] at h
    cases he : evalPlaceToOp pb (clearLatch st) p with
    | error e => rw [he] at h; cases h
    | ok r =>
      obtain ⟨o, ty⟩ := r; rw [he] at h
      cases o with
      | immediate bb =>
        simp only [readOpBytes] at h
        cases hv : checkValid ty bb with
        | error e => rw [hv] at h; cases h
        | ok u => rw [hv] at h; exact writeDest_latch h
      | indirect src =>
        simp only at h
        cases hm : usesMemoryPath ty (.indirect src) with
        | true => rw [hm] at h; exact copyMemPath_latch h
        | false =>
          rw [hm] at h; simp only [readOpBytes] at h
          cases hl : loadMPlace (clearLatch st) src with
          | error e => rw [hl] at h; cases h
          | ok r' =>
            obtain ⟨bb, st₁⟩ := r'; rw [hl] at h; simp only at h
            cases hv : checkValid ty bb with
            | error e => rw [hv] at h; cases h
            | ok u => rw [hv] at h; exact (writeDest_latch h).trans (loadMPlace_latch hl)
  | move p =>
    simp only [annealAssignUse] at h
    cases he : evalPlaceToOp pb (clearLatch st) p with
    | error e => rw [he] at h; cases h
    | ok r =>
      obtain ⟨o, ty⟩ := r; rw [he] at h
      cases o with
      | immediate bb =>
        simp only at h
        cases hp : p.projs with
        | cons _ _ => rw [hp] at h; cases h
        | nil =>
          rw [hp] at h; simp only at h
          cases hs : setLocalE (clearLatch st) p.local_ (.imm (uninitBytes bb.length)) with
          | error e => rw [hs] at h; cases h
          | ok st₁ =>
            rw [hs] at h; simp only at h
            cases hv : checkValid ty bb with
            | error e => rw [hv] at h; cases h
            | ok u => rw [hv] at h; exact writeDest_latch h
      | indirect src =>
        simp only at h
        cases hm : usesMemoryPath ty (.indirect src) with
        | true =>
          rw [hm] at h; simp only at h
          cases hc : copyMemPath (clearLatch st) src d with
          | error e => rw [hc] at h; cases h
          | ok st₁ =>
            rw [hc] at h; exact (deinitMPlaceRaw_latch h).trans (copyMemPath_latch hc)
        | false =>
          rw [hm] at h; simp only at h
          cases hl : loadMPlace (clearLatch st) src with
          | error e => rw [hl] at h; cases h
          | ok r' =>
            obtain ⟨bb, st₁⟩ := r'; rw [hl] at h; simp only at h
            cases hv : checkValid ty bb with
            | error e => rw [hv] at h; cases h
            | ok u =>
              rw [hv] at h; simp only at h
              cases hd : deinitMPlaceRaw st₁ src with
              | error e => rw [hd] at h; cases h
              | ok st₂ =>
                rw [hd] at h
                exact (writeDest_latch h).trans
                  ((deinitMPlaceRaw_latch hd).trans (loadMPlace_latch hl))

theorem forceAllocation_latch {st st' : PState} {l : Local}
    (h : forceAllocation st l = .ok st') : st'.pendingMoveDeinit = st.pendingMoveDeinit := by
  unfold forceAllocation at h
  cases hf : st.frames with
  | nil => rw [hf] at h; cases h
  | cons fr rest =>
    rw [hf] at h; simp only at h
    cases hn : nth? fr.locals l with
    | none => rw [hn] at h; cases h
    | some sl =>
      rw [hn] at h
      cases sl with
      | dead => cases h
      | mem _ => cases h; rfl
      | imm b =>
        simp only at h
        cases hs : setNth? fr.locals l (.mem st.heap.length) with
        | none => rw [hs] at h; cases h
        | some ls => rw [hs] at h; cases h; rfl

theorem placeToMPlace_latch {pb : Nat} {st st' : PState} {p : SemPlace} {mp : MPlace}
    (h : placeToMPlace pb st p = .ok (mp, st')) :
    st'.pendingMoveDeinit = st.pendingMoveDeinit := by
  unfold placeToMPlace at h
  cases hp : p.projs with
  | nil =>
    rw [hp] at h; simp only at h
    cases hf : forceAllocation st p.local_ with
    | error e => rw [hf] at h; cases h
    | ok st₁ =>
      rw [hf] at h; simp only at h
      cases he : evalPlaceToOp pb st₁ p with
      | error e => rw [he] at h; cases h
      | ok r =>
        obtain ⟨o, _⟩ := r; rw [he] at h
        cases o <;> cases h
        exact forceAllocation_latch hf
  | cons _ _ =>
    rw [hp] at h; simp only at h
    cases he : evalPlaceToOp pb st p with
    | error e => rw [he] at h; cases h
    | ok r =>
      obtain ⟨o, _⟩ := r; rw [he] at h
      cases o <;> cases h; rfl

theorem createRef_latch {st st' : PState} {mutbl : Bool} {mp : MPlace} {b : Bytes}
    (h : createRef st mutbl mp = .ok (b, st')) : st'.pendingMoveDeinit = st.pendingMoveDeinit := by
  unfold createRef at h
  cases ht : tbAccess .read st.borrows mp.alloc mp.tag mp.offset mp.size with
  | none => rw [ht] at h; cases h
  | some bs => rw [ht] at h; cases h; rfl

theorem writePlace_latch {pb : Nat} {st st' : PState} {dest : SemPlace} {b : Bytes}
    (h : writePlace pb st dest b = .ok st') : st'.pendingMoveDeinit = st.pendingMoveDeinit := by
  unfold writePlace at h
  cases he : evalPlaceToOp pb st dest with
  | error e => rw [he] at h; cases h
  | ok r =>
    obtain ⟨o, _⟩ := r; rw [he] at h
    cases o with
    | immediate _ => exact setLocalE_latch h
    | indirect _ => exact storeMPlace_latch h

theorem readOperandsWith_true_latch_clear (pb : Nat) :
    ∀ (st st' : PState) (ops : List SemOperand) (bs : List Bytes),
      st.pendingMoveDeinit = false →
      readOperandsWith (twoPhaseReadOperand true) pb st ops = .ok (bs, st') →
      st'.pendingMoveDeinit = false
  | st, st', [], bs, h0, h => by simp only [readOperandsWith] at h; cases h; exact h0
  | st, st', op :: ops, bs, _, h => by
    simp only [readOperandsWith] at h
    cases hr : twoPhaseReadOperand true pb st op with
    | error e => rw [hr] at h; cases h
    | ok r =>
      obtain ⟨b, st₁⟩ := r; rw [hr] at h; simp only at h
      cases hrs : readOperandsWith (twoPhaseReadOperand true) pb st₁ ops with
      | error e => rw [hrs] at h; cases h
      | ok r' =>
        obtain ⟨bs', st₂⟩ := r'; rw [hrs] at h; cases h
        exact readOperandsWith_true_latch_clear pb st₁ st' ops bs'
          (twoPhaseReadOperand_true_latch_clear pb st st₁ op b hr) hrs

theorem advance_latch (st : PState) : (advance st).pendingMoveDeinit = st.pendingMoveDeinit := by
  unfold advance; cases st.frames <;> rfl

theorem jump_latch (st : PState) (bb : Nat) :
    (jump st bb).pendingMoveDeinit = st.pendingMoveDeinit := by
  unfold jump; cases st.frames <;> rfl

theorem popFrame_latch (st : PState) : (popFrame st).pendingMoveDeinit = st.pendingMoveDeinit := by
  unfold popFrame; cases st.frames <;> rfl

theorem execStmt_true_latch_clear (pb : Nat) (st st' : PState) (s : SemStmt)
    (h0 : st.pendingMoveDeinit = false)
    (h : execStmt (twoPhaseStrategy true) pb st s = .ok st') :
    st'.pendingMoveDeinit = false := by
  cases s with
  | assign dest rv =>
    simp only [execStmt] at h
    cases hd : resolveDest pb st dest with
    | error e => rw [hd] at h; cases h
    | ok rd =>
      obtain ⟨d, dty⟩ := rd; rw [hd] at h; simp only at h
      cases rv with
      | use op => exact twoPhaseAssignUse_true_latch_clear pb st st' op d h
      | binaryOp o l r =>
        simp only [twoPhaseStrategy] at h
        cases hl : twoPhaseReadOperand true pb st l with
        | error e => rw [hl] at h; cases h
        | ok rl =>
          obtain ⟨lb, st₁⟩ := rl; rw [hl] at h; simp only at h
          cases hr : twoPhaseReadOperand true pb st₁ r with
          | error e => rw [hr] at h; cases h
          | ok rr =>
            obtain ⟨rb, st₂⟩ := rr; rw [hr] at h; simp only at h
            cases hb : evalBinOpBytes o lb rb with
            | error e => rw [hb] at h; cases h
            | ok res =>
              rw [hb] at h
              exact (writeDest_latch h).trans
                (twoPhaseReadOperand_true_latch_clear pb st₁ st₂ r rb hr)
      | aggregate ops =>
        simp only [readOperands, twoPhaseStrategy] at h
        cases hrs : readOperandsWith (twoPhaseReadOperand true) pb st ops with
        | error e => rw [hrs] at h; cases h
        | ok ro =>
          obtain ⟨bs, st₁⟩ := ro; rw [hrs] at h; simp only at h
          cases ha : buildAggregate dty.2 bs with
          | error e => rw [ha] at h; cases h
          | ok b =>
            rw [ha] at h
            exact (writeDest_latch h).trans
              (readOperandsWith_true_latch_clear pb st st₁ ops bs h0 hrs)
      | ref mutbl p =>
        simp only at h
        cases hp : placeToMPlace pb st p with
        | error e => rw [hp] at h; cases h
        | ok rp =>
          obtain ⟨mp, st₁⟩ := rp; rw [hp] at h; simp only at h
          cases hc : createRef st₁ mutbl mp with
          | error e => rw [hc] at h; cases h
          | ok rc =>
            obtain ⟨b, st₂⟩ := rc; rw [hc] at h
            exact (writeDest_latch h).trans
              ((createRef_latch hc).trans ((placeToMPlace_latch hp).trans h0))
      | rawPtr p =>
        simp only at h
        cases hp : placeToMPlace pb st p with
        | error e => rw [hp] at h; cases h
        | ok rp =>
          obtain ⟨mp, st₁⟩ := rp; rw [hp] at h
          exact (writeDest_latch h).trans ((placeToMPlace_latch hp).trans h0)
      | unsupported => cases h
  | deinit p =>
    simp only [execStmt] at h
    cases he : evalPlaceToOp pb st p with
    | error e => rw [he] at h; cases h
    | ok r =>
      obtain ⟨o, _⟩ := r; rw [he] at h
      cases o with
      | immediate _ => exact (setLocalE_latch h).trans h0
      | indirect _ => exact (storeMPlace_latch h).trans h0
  | storageLive l ty =>
    simp only [execStmt] at h
    cases hi : isImmKind ty.1 with
    | true => rw [hi] at h; exact (setLocalE_latch h).trans h0
    | false =>
      rw [hi] at h; simp only at h
      have hl := setLocalE_latch h
      exact hl.trans h0
  | storageDead l =>
    simp only [execStmt] at h
    cases hf : st.frames with
    | nil => rw [hf] at h; cases h
    | cons fr rest =>
      rw [hf] at h; simp only at h
      cases hn : nth? fr.locals l with
      | none => rw [hn] at h; exact (setLocalE_latch h).trans h0
      | some sl =>
        rw [hn] at h
        cases sl with
        | dead => exact (setLocalE_latch h).trans h0
        | imm _ => exact (setLocalE_latch h).trans h0
        | mem a =>
          simp only at h
          cases hs : setNth? st.heap a none with
          | none => rw [hs] at h; cases h
          | some hp => rw [hs] at h; have hl := setLocalE_latch h; exact hl.trans h0
  | nop => cases h; exact h0
  | unsupported => cases h

theorem execTerm_true_latch_clear (pb : Nat) (st st' : PState) (t : SemTerm)
    (h0 : st.pendingMoveDeinit = false)
    (h : execTerm (twoPhaseStrategy true) pb st t = .running st') :
    st'.pendingMoveDeinit = false := by
  cases t with
  | goto bb => cases h; rw [jump_latch]; exact h0
  | ret retTy site =>
    simp only [execTerm] at h
    cases he : evalPlaceToOp pb st ⟨0, retTy, []⟩ with
    | error e => rw [he] at h; cases h
    | ok r =>
      obtain ⟨o, _⟩ := r; rw [he] at h; simp only at h
      cases hr : readOpBytes st o with
      | error e => rw [hr] at h; cases h
      | ok ro =>
        obtain ⟨b, st₁⟩ := ro; rw [hr] at h; simp only at h
        have h1 : st₁.pendingMoveDeinit = false := (readOpBytes_latch hr).trans h0
        cases hv : checkValid retTy b with
        | error e => rw [hv] at h; cases h
        | ok u =>
          rw [hv] at h; simp only at h
          cases site with
          | none => cases h
          | some rs =>
            simp only at h
            split at h
            · cases h
            · next st₃ hw =>
              have h3 : st₃.pendingMoveDeinit = false := by
                split at hw
                · split at hw
                  · exact (writeDest_latch hw).trans ((popFrame_latch st₁).trans h1)
                  · exact (writePlace_latch hw).trans ((popFrame_latch st₁).trans h1)
                · exact (writePlace_latch hw).trans ((popFrame_latch st₁).trans h1)
              split at h
              · cases h
              · cases h; rw [jump_latch]; exact h3
  | switchInt d ts =>
    simp only [execTerm, twoPhaseStrategy] at h
    cases hr : twoPhaseReadOperand true pb st d with
    | error e => rw [hr] at h; cases h
    | ok r =>
      obtain ⟨b, st₁⟩ := r; rw [hr] at h; simp only at h
      cases hd : decodeLittleEndianBytes b with
      | none => rw [hd] at h; cases h
      | some p =>
        rw [hd] at h; cases h; rw [jump_latch]
        exact twoPhaseReadOperand_true_latch_clear pb st st₁ d b hr
  | assert c expected target unwind =>
    simp only [execTerm, twoPhaseStrategy] at h
    cases hr : twoPhaseReadOperand true pb st c with
    | error e => rw [hr] at h; cases h
    | ok r =>
      obtain ⟨b, st₁⟩ := r; rw [hr] at h; simp only at h
      have h1 := twoPhaseReadOperand_true_latch_clear pb st st₁ c b hr
      cases hd : decodeLittleEndianBytes b with
      | none => rw [hd] at h; cases h
      | some p =>
        rw [hd] at h; simp only at h
        cases hc : decide (Nat.beq p.1 1 = expected) with
        | true => rw [hc] at h; cases h; rw [jump_latch]; exact h1
        | false =>
          rw [hc] at h; simp only at h
          cases hu : unwind <;> rw [hu] at h <;> cases h
          rw [jump_latch]; exact h1
  | call callee argc calleeLocals args dest =>
    simp only [execTerm, twoPhaseStrategy] at h
    cases hd : resolveDest pb st dest with
    | error e => rw [hd] at h; cases h
    | ok rd =>
      rw [hd] at h; simp only at h
      cases hrs : readOperandsWith (twoPhaseReadOperand true) pb st args with
      | error e => rw [hrs] at h; cases h
      | ok ro =>
        obtain ⟨bs, st₁⟩ := ro; rw [hrs] at h; simp only at h
        cases callee with
        | none => cases h
        | some bi =>
          cases h
          exact readOperandsWith_true_latch_clear pb st st₁ args bs h0 hrs
  | unwindResume site =>
    simp only [execTerm] at h
    cases site with
    | none => cases h
    | some rs =>
      simp only at h
      cases hu : rs.unwind <;> rw [hu] at h <;> cases h
      rw [jump_latch, popFrame_latch]; exact h0
  | unreachable => cases h
  | unsupported => cases h

/-- **Whole-step latch invariant (`M_ref` and `M_anneal`)**: starting from any
state with `pendingMoveDeinit = false`, every `.running` step of `refStepCore
true (encodeProg p)` and `annealStep p` leaves `pendingMoveDeinit = false`. -/
theorem refStepCore_true_preserves_latch_clear (p : V2026Prog) (st st' : PState)
    (h0 : st.pendingMoveDeinit = false)
    (h : refStepCore true (encodeProg p) st = .running st') :
    st'.pendingMoveDeinit = false := by
  simp only [refStepCore, refStepCoreWith] at h
  cases hf : refFetch (encodeProg p) st with
  | error e => rw [hf] at h; cases h
  | ok i =>
    rw [hf] at h
    cases i with
    | stmt pb s =>
      simp only [runInstr] at h
      cases hs : execStmt (twoPhaseStrategy true) pb st s with
      | error e => rw [hs] at h; cases h
      | ok st₁ =>
        rw [hs] at h; cases h
        rw [advance_latch]; exact execStmt_true_latch_clear pb st st₁ s h0 hs
    | term pb t =>
      exact execTerm_true_latch_clear pb st st' t h0 h

theorem annealStep_preserves_latch_clear (p : V2026Prog) (st st' : PState)
    (h0 : st.pendingMoveDeinit = false)
    (h : annealStep p st = .running st') :
    st'.pendingMoveDeinit = false := by
  rw [← anneal_corresponds_to_miri] at h
  exact refStepCore_true_preserves_latch_clear p st st' h0 h

/-! ### Reachable-state latch invariant (entry states + bounded runs)

Closing the whole-step invariant under the entry states and the run loops
makes it a property of **every reachable** `M_anneal` / `M_ref`
statement-boundary state: `pendingMoveDeinit` latched by phase 1
(`evalOperand`) is always consumed by phase 2 (`readImmediate` /
`copyRuntimePlaceNoValidate`) inside the same step. -/

theorem annealInit_latch_clear (p : V2026Prog) (args : List Bytes) (st : PState)
    (h : annealInit p args = .ok st) : st.pendingMoveDeinit = false := by
  unfold annealInit at h
  split at h
  · cases h
  · split at h
    · cases h
    · cases h; rfl

theorem refInit_latch_clear (rp : RefProg) (args : List Bytes) (st : PState)
    (h : refInit rp args = .ok st) : st.pendingMoveDeinit = false := by
  unfold refInit at h
  split at h
  · cases h
  · split at h
    · cases h
    · cases h; rfl

theorem annealRun_preserves_latch_clear (p : V2026Prog) :
    ∀ (n : Nat) (st st' : PState), st.pendingMoveDeinit = false →
      annealRun p n st = .running st' → st'.pendingMoveDeinit = false
  | 0, st, st', h0, h => by
    rw [annealRun.eq_1] at h
    cases h; exact h0
  | n + 1, st, st', h0, h => by
    rw [annealRun.eq_2] at h
    cases hs : annealStep p st with
    | running st₁ =>
      rw [hs] at h
      exact annealRun_preserves_latch_clear p n st₁ st'
        (annealStep_preserves_latch_clear p st st₁ h0 hs) h
    | returned b => rw [hs] at h; cases h
    | panicked => rw [hs] at h; cases h
    | fault f => rw [hs] at h; cases h

theorem refStep_true_preserves_latch_clear (p : V2026Prog) (rs rs' : RefState)
    (h0 : rs.core.pendingMoveDeinit = false)
    (h : refStep true (encodeProg p) rs = .running rs') :
    rs'.core.pendingMoveDeinit = false := by
  unfold refStep at h
  cases hb : Nat.blt rs.stepsExecuted rs.maxSteps with
  | false => rw [hb] at h; cases h
  | true =>
    rw [hb] at h
    cases hc : refStepCore true (encodeProg p) rs.core with
    | running st' =>
      rw [hc] at h; cases h
      exact refStepCore_true_preserves_latch_clear p rs.core st' h0 hc
    | returned b => rw [hc] at h; cases h
    | panicked => rw [hc] at h; cases h
    | fault f =>
      rw [hc] at h
      cases f with
      | ub why => cases h
      | unsupported => cases h

theorem refRunFuel_true_preserves_latch_clear (p : V2026Prog) :
    ∀ (n : Nat) (rs rs' : RefState), rs.core.pendingMoveDeinit = false →
      refRunFuel true (encodeProg p) n rs = .running rs' → rs'.core.pendingMoveDeinit = false
  | 0, rs, rs', h0, h => by
    rw [refRunFuel.eq_1] at h
    cases h; exact h0
  | n + 1, rs, rs', h0, h => by
    rw [refRunFuel.eq_2] at h
    cases hs : refStep true (encodeProg p) rs with
    | running rs₁ =>
      rw [hs] at h
      exact refRunFuel_true_preserves_latch_clear p n rs₁ rs'
        (refStep_true_preserves_latch_clear p rs rs₁ h0 hs) h
    | returned b => rw [hs] at h; cases h
    | panicked => rw [hs] at h; cases h
    | ub why => rw [hs] at h; cases h
    | blocked => rw [hs] at h; cases h
    | exhaustedStepLimit => rw [hs] at h; cases h

/-- **Reachable-state latch invariant (`M_anneal`)**: every `.running` state of a
bounded run from an entry state has `pendingMoveDeinit = false`. -/
theorem annealReachable_latch_clear (p : V2026Prog) (args : List Bytes) (n : Nat)
    (st₀ st : PState) (hi : annealInit p args = .ok st₀)
    (hr : annealRun p n st₀ = .running st) : st.pendingMoveDeinit = false :=
  annealRun_preserves_latch_clear p n st₀ st (annealInit_latch_clear p args st₀ hi) hr

/-- **Reachable-state latch invariant (`M_ref`, `deinitMoves = true`)**: every
`.running` state of a bounded `refRunFuel` from an entry state of
`encodeProg p` (any step budget) has `pendingMoveDeinit = false`. -/
theorem refReachable_latch_clear (p : V2026Prog) (args : List Bytes) (n maxSteps : Nat)
    (st₀ : PState) (rs : RefState) (hi : refInit (encodeProg p) args = .ok st₀)
    (hr : refRunFuel true (encodeProg p) n ⟨st₀, 0, maxSteps⟩ = .running rs) :
    rs.core.pendingMoveDeinit = false :=
  refRunFuel_true_preserves_latch_clear p n ⟨st₀, 0, maxSteps⟩ rs
    (refInit_latch_clear (encodeProg p) args st₀ hi) hr

/-- Executable non-vacuity check for the reachable-state latch invariant on the
`D5` indirect move `_4 = move (*_2)`: (1) the pre-move state is reachable in both
machines; (2) phase 1 of `M_ref` (`refEvalOperand true`) **sets** the latch
mid-step, so the invariant is not a constant (a mutant step that stopped after
phase 1 would leak it); and (3) the full `M_ref` step consumes it again. -/
def reachableLatchWitness : Bool :=
  let p := d5Prog (asg (loc 4) (.use (.move (drf 2)))) (.use (.copy (loc 4)))
  match d5PreMoveState, refInit (encodeProg p) [] with
  | some st, .ok r₀ =>
    match refRunFuel true (encodeProg p) 3 ⟨r₀, 0, 100⟩, refEvalOperand true 64 st d5MoveOp,
        refStepCore true (encodeProg p) st with
    | .running rs, .ok (.indirect _, _, stMid), .running st' =>
      decide (rs.core.frames.length = st.frames.length) &&
        decide (rs.core.heap.length = st.heap.length) &&
        decide (rs.core.borrows.length = st.borrows.length) && decide (rs.stepsExecuted = 3) &&
        !rs.core.pendingMoveDeinit && !st.pendingMoveDeinit && stMid.pendingMoveDeinit &&
        !st'.pendingMoveDeinit
    | _, _, _ => false
  | _, _ => false

theorem reachable_latch_clear_nonvacuous : reachableLatchWitness = true := by
  decide

/-! ### Non-vacuity of the reachable-state latch and Tree Borrows claims

`MiriMoveDeinitWiringClaim` 8–10 exhibit, as `Prop`-level existentials over the
TCB's own definitions, reachable `D5` states (the entry state plus three
`M_anneal` steps, or three budgeted `M_ref` steps on `encodeProg`, i.e. just
before `_4 = move (*_2)`): phase 1 (`refEvalOperand true`) genuinely *sets* the
latch there and the full step consumes it again, and the Tree Borrows read /
assignment theorems apply to the `.frozen` sibling borrow `_3 = &_1`, which
overlaps the moved window `*_2` but not the destination `_4`. Each existential
is extracted from an executable `Bool` check decided by the kernel. -/

/-- The `D5` latch program (`_1 = 5; _3 = &_1; _2 = &raw mut _1; _4 = move (*_2);
_0 = copy _4`). -/
def d5LatchProg : V2026Prog := d5Prog (asg (loc 4) (.use (.move (drf 2)))) (.use (.copy (loc 4)))

/-- The resolved moved place `*_2` of `d5LatchProg`. -/
def d5MovePlace : SemPlace := ⟨2, (.rawPtr .mut kU8, lay (.rawPtr .mut kU8)), [.deref]⟩

theorem permIsFrozen_eq_true {p : TreeBorrowPerm} (h : permIsFrozen p = true) : p = .frozen := by
  cases p <;> first | rfl | cases h

/-- Executable check of `MiriMoveDeinitWiringClaim` 8 on `d5LatchProg`. -/
def annealReachableLatchWitness : Bool :=
  match annealInit d5LatchProg [] with
  | .error _ => false
  | .ok st₀ =>
    match annealRun d5LatchProg 3 st₀ with
    | .running st =>
      match refEvalOperand true 64 st (.move d5MovePlace) with
      | .ok (.indirect _, _, stMid) =>
        match annealStep d5LatchProg st with
        | .running st' => stMid.pendingMoveDeinit && !st'.pendingMoveDeinit
        | _ => false
      | _ => false
    | _ => false

theorem annealReachableLatchWitness_eq_true : annealReachableLatchWitness = true := by
  decide

/-- **Non-vacuity of the reachable `M_anneal` latch invariant**: a reachable
state in which phase 1 sets the latch and the full step clears it. -/
theorem annealReachable_latch_set_nonvacuous :
    ∃ (p : V2026Prog) (args : List Bytes) (n : Nat) (st₀ st : PState) (pb : Nat) (q : SemPlace)
      (mp : MPlace) (ty : SemTy) (stMid st' : PState),
      annealInit p args = .ok st₀ ∧ annealRun p n st₀ = .running st ∧
      refEvalOperand true pb st (.move q) = .ok (.indirect mp, ty, stMid) ∧
      stMid.pendingMoveDeinit = true ∧
      annealStep p st = .running st' ∧ st'.pendingMoveDeinit = false := by
  have hw := annealReachableLatchWitness_eq_true
  unfold annealReachableLatchWitness at hw
  split at hw
  · cases hw
  · next st₀ h₀ =>
    split at hw
    · next st h₁ =>
      split at hw
      · next mp ty stMid h₂ =>
        split at hw
        · next st' h₃ =>
          simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hw
          exact ⟨d5LatchProg, [], 3, st₀, st, 64, d5MovePlace, mp, ty, stMid, st', h₀, h₁, h₂,
            hw.1, h₃, hw.2⟩
        · cases hw
      · cases hw
    · cases hw

/-- Executable check of `MiriMoveDeinitWiringClaim` 9 on `encodeProg d5LatchProg`. -/
def refReachableLatchWitness : Bool :=
  match refInit (encodeProg d5LatchProg) [] with
  | .error _ => false
  | .ok st₀ =>
    match refRunFuel true (encodeProg d5LatchProg) 3 ⟨st₀, 0, 100⟩ with
    | .running rs =>
      match refEvalOperand true 64 rs.core (.move d5MovePlace) with
      | .ok (.indirect _, _, stMid) =>
        match refStep true (encodeProg d5LatchProg) rs with
        | .running rs' => stMid.pendingMoveDeinit && !rs'.core.pendingMoveDeinit
        | _ => false
      | _ => false
    | _ => false

theorem refReachableLatchWitness_eq_true : refReachableLatchWitness = true := by
  decide

/-- **Non-vacuity of the reachable `M_ref` latch invariant**: a reachable
budgeted state of `encodeProg d5LatchProg` in which phase 1 sets the latch and
the full budgeted step clears it. -/
theorem refReachable_latch_set_nonvacuous :
    ∃ (p : V2026Prog) (args : List Bytes) (n maxSteps : Nat) (st₀ : PState) (rs rs' : RefState)
      (pb : Nat) (q : SemPlace) (mp : MPlace) (ty : SemTy) (stMid : PState),
      refInit (encodeProg p) args = .ok st₀ ∧
      refRunFuel true (encodeProg p) n ⟨st₀, 0, maxSteps⟩ = .running rs ∧
      refEvalOperand true pb rs.core (.move q) = .ok (.indirect mp, ty, stMid) ∧
      stMid.pendingMoveDeinit = true ∧
      refStep true (encodeProg p) rs = .running rs' ∧ rs'.core.pendingMoveDeinit = false := by
  have hw := refReachableLatchWitness_eq_true
  unfold refReachableLatchWitness at hw
  split at hw
  · cases hw
  · next st₀ h₀ =>
    split at hw
    · next rs h₁ =>
      split at hw
      · next mp ty stMid h₂ =>
        split at hw
        · next rs' h₃ =>
          simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hw
          exact ⟨d5LatchProg, [], 3, 100, st₀, rs, rs', 64, d5MovePlace, mp, ty, stMid, h₀, h₁,
            h₂, hw.1, h₃, hw.2⟩
        · cases hw
      · cases hw
    · cases hw

/-- Executable check of `MiriMoveDeinitWiringClaim` 10 on `d5LatchProg`. -/
def tbReachableWitness : Bool :=
  match annealInit d5LatchProg [] with
  | .error _ => false
  | .ok st₀ =>
    match annealRun d5LatchProg 3 st₀ with
    | .running st =>
      match refEvalOperand true 64 st (.move d5MovePlace) with
      | .ok (.indirect mp, _, _) =>
        match twoPhaseReadOperand true 64 st (.move d5MovePlace) with
        | .ok _ =>
          match twoPhaseAssignUse true 64 st (.move d5MovePlace) (.imm 4) with
          | .ok _ =>
            match nth? st.borrows 0 with
            | some e =>
              permIsFrozen e.perm && entryOverlapsDest e (.mem mp) && !entryOverlapsDest e (.imm 4)
            | none => false
          | .error _ => false
        | .error _ => false
      | _ => false
    | _ => false

theorem tbReachableWitness_eq_true : tbReachableWitness = true := by
  decide

/-- **Non-vacuity of the Tree Borrows read and assignment theorems**: in a
reachable state, moving out of `*_2` succeeds as an operand read and as
`_4 = move (*_2)`, while the `.frozen` sibling borrow `_3 = &_1` overlaps the
moved window but not the destination. -/
theorem tbReachable_nonvacuous :
    ∃ (p : V2026Prog) (args : List Bytes) (n : Nat) (st₀ st : PState) (pb : Nat) (q : SemPlace)
      (mp : MPlace) (ty : SemTy) (stMid : PState) (b : Bytes) (st₁ : PState) (d : DestPlace)
      (st₂ : PState) (i : Nat) (e : BorrowEntry),
      annealInit p args = .ok st₀ ∧ annealRun p n st₀ = .running st ∧
      refEvalOperand true pb st (.move q) = .ok (.indirect mp, ty, stMid) ∧
      twoPhaseReadOperand true pb st (.move q) = .ok (b, st₁) ∧
      twoPhaseAssignUse true pb st (.move q) d = .ok st₂ ∧
      nth? st.borrows i = some e ∧ e.perm = .frozen ∧
      entryOverlapsDest e (.mem mp) = true ∧ entryOverlapsDest e d = false := by
  have hw := tbReachableWitness_eq_true
  unfold tbReachableWitness at hw
  split at hw
  · cases hw
  · next st₀ h₀ =>
    split at hw
    · next st h₁ =>
      split at hw
      · next mp ty stMid h₂ =>
        split at hw
        · next r h₃ =>
          obtain ⟨b, st₁⟩ := r
          split at hw
          · next st₂ h₄ =>
            split at hw
            · next e h₅ =>
              simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hw
              exact ⟨d5LatchProg, [], 3, st₀, st, 64, d5MovePlace, mp, ty, stMid, b, st₁, .imm 4,
                st₂, 0, e, h₀, h₁, h₂, h₃, h₄, h₅, permIsFrozen_eq_true hw.1.1, hw.1.2, hw.2⟩
            · cases hw
          · cases hw
        · cases hw
      · cases hw
    · cases hw

/-! ## Proofs of the correspondence claims -/

/-- **`CorrespondenceClaim`** (proved here; restated in
`Anneal.Mir.Correspondence.Claims`). -/
theorem correspondenceClaim_proof : CorrespondenceClaim :=
  ⟨anneal_corresponds_to_miri, refObs_encodeProg, refInit_encodeProg, simulationInv_bijective,
   ⟨d3Prog, [], 40, some 99, 1, by decide⟩,
   ⟨d1MoveThenRead, [], 40, .invalidUninitBytes, by decide⟩,
   no_correspondence_when_deinitMoves_false⟩

/-- **`FaultEquivalenceClaim`** (proved here; restated in
`Anneal.Mir.Correspondence.Claims`). -/
theorem faultEquivalenceClaim_proof : FaultEquivalenceClaim := by
  refine ⟨?_, reachesResult_fault_iff_refReachesOutcome, ?_, ?_⟩
  · intro p args fuel
    rw [refObs_encodeProg]
    exact ⟨fun _ => Iff.rfl, Iff.rfl, fun _ _ => Iff.rfl, Iff.rfl⟩
  · exact ⟨d1MoveThenRead, [], 40, .invalidUninitBytes, by decide, by decide⟩
  · exact ⟨d7Unresolved (cU8 1), [], 40, by decide, by decide⟩

/-- **`MiriMoveDeinitWiringClaim`** (proved here; restated in
`Anneal.Mir.Correspondence.Claims`). -/
theorem miriMoveDeinitWiringClaim_proof : MiriMoveDeinitWiringClaim :=
  ⟨twoPhaseStrategy_true_eq_eager, miriMoveDeinitWiring_holds, deinitMovedPlace_false_id,
   annealReachable_latch_clear, refReachable_latch_clear, refEvalOperand_sets_latch_nonvacuous,
   deinitMovedPlace_preserves_tb_tags, deinitMovedPlace_assignUse_preserves_tb_tags,
   annealReachable_latch_set_nonvacuous, refReachable_latch_set_nonvacuous,
   tbReachable_nonvacuous⟩

end Anneal.Mir.Correspondence
