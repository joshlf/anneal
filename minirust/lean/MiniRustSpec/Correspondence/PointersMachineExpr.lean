/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import MiniRustSpec.Correspondence.PointersMachineCodec

/-!
# Polymorphic `Machine<BM>` and `Mach` equivalence: place and value expressions

Second of the four submodules of `MiniRustSpec.Correspondence.PointersMachine`: binary
operators, pointer arithmetic, frame mutation helpers (`mutateCurFrameOutM_retag_bm_eq`),
and mutual expression evaluation (`evalPlaceM_bm_eq`, `evalValueM_bm_eq`,
`evalValuesM_bm_eq`).
-/

namespace MiniRustSpec.Correspondence

open MiniRustSpec
open MiniRustSpec.LibSpecr
open MiniRustSpec.Interp
open PointersMachineInternal

private theorem comparePtrM_bm_eq (lp rp : Gen.Pointer Prov) :
    comparePtrM lp rp = comparePtr lp rp := by
  unfold comparePtrM comparePtr
  rcases lp.metadata with _ | (_ | _) <;> rcases rp.metadata with _ | (_ | _) <;> rfl

private theorem evalRelOpM_bm_eq (relOp : Gen.RelOp) (ord : Ordering) :
    evalRelOpM (M := BM) relOp ord = evalRelOp relOp ord := by
  cases relOp <;> cases ord <;> rfl

private theorem evalBinOpM_bm_eq (op : Gen.BinOp) (l r : Val × Gen.«Type») :
    evalBinOpM (M := BM) op l r = evalBinOp op l r := by
  rcases l with ⟨lv, lty⟩
  rcases r with ⟨rv, rty⟩
  unfold evalBinOpM evalBinOp
  cases op with
  | Int _ =>
    cases lv with
    | Int _ =>
      cases lty with
      | Int _ =>
        cases rv with
        | Int _ => rfl
        | _ => rfl
      | _ => rfl
    | _ => rfl
  | IntWithOverflow _ =>
    cases lv with
    | Int _ =>
      cases lty with
      | Int _ =>
        cases rv with
        | Int _ => rfl
        | _ => rfl
      | _ => rfl
    | _ => rfl
  | Rel relOp =>
    cases lty with
    | Int _ =>
      cases lv with
      | Int l =>
        cases rv with
        | Int r => rfl
        | _ => rfl
      | _ => rfl
    | Bool =>
      cases lv with
      | Bool l =>
        cases rv with
        | Bool r => rfl
        | _ => rfl
      | _ => rfl
    | Ptr _ =>
      cases lv with
      | Ptr lp =>
        cases rv with
        | Ptr rp =>
          dsimp only
          exact bind_congr (comparePtrM_bm_eq lp rp) (fun ord =>
            congrArg pure (evalRelOpM_bm_eq relOp ord))
        | _ => rfl
      | _ => rfl
    | _ => rfl
  | _ => rfl

private theorem ptrOffsetWrappingM_bm_eq (ptr : Ptr) (off : Int) :
    ptrOffsetWrappingM ptr off = ptrOffsetWrapping ptr off := by
  cases ptr; rfl

private theorem ptrOffsetInboundsM_bm_eq (m : Mach) (ptr : Ptr) (off : Int) :
    ptrOffsetInboundsM (M := BM) m ptr off = ptrOffsetInbounds m ptr off := by
  unfold ptrOffsetInboundsM ptrOffsetInbounds
  exact bind_congr (cm_signed_deref_bm_eq m.mem ptr off) (fun _ => rfl)

private theorem evalPtrOffsetM_bm_eq (m : Mach) (inbounds : Bool) (l r : Val × Gen.«Type») :
    evalPtrOffsetM (M := BM) m inbounds l r = evalPtrOffset m inbounds l r := by
  rcases l with ⟨lv, lty⟩
  rcases r with ⟨rv, rty⟩
  unfold evalPtrOffsetM evalPtrOffset
  cases lv with
  | Ptr lp =>
    rcases lp with ⟨left, _ | _⟩
    · cases rv with
      | Int right =>
        cases inbounds with
        | false => dsimp only [ptrOffsetWrappingM_bm_eq]; rfl
        | true =>
          dsimp only
          exact bind_congr (ptrOffsetInboundsM_bm_eq m left right) (fun _ => rfl)
      | _ => rfl
    · rfl
  | _ => rfl

private theorem evalPtrOffsetFromM_bm_eq (m : Mach) (inbounds nonneg : Bool)
    (l r : Val × Gen.«Type») :
    evalPtrOffsetFromM (M := BM) m inbounds nonneg l r = evalPtrOffsetFrom m inbounds nonneg l r := by
  rcases l with ⟨lv, lty⟩
  rcases r with ⟨rv, rty⟩
  unfold evalPtrOffsetFromM evalPtrOffsetFrom
  cases lv with
  | Ptr lp =>
    rcases lp with ⟨left, _ | _⟩
    · cases rv with
      | Ptr rp =>
        rcases rp with ⟨right, _ | _⟩
        · dsimp only
          cases inbounds with
          | false => rfl
          | true =>
            refine bind_congr (cm_signed_deref_bm_eq m.mem left (-(left.addr - right.addr))) (fun _ => ?_)
            exact bind_congr (cm_signed_deref_bm_eq m.mem right (left.addr - right.addr)) (fun _ => rfl)
        · rfl
      | _ => rfl
    · rfl
  | _ => rfl

private theorem dropLast_append_getLast_cons {α : Type} :
    ∀ (x : α) (xs : List α),
      (x :: xs).dropLast ++ [(x :: xs).getLast (by simp)] = x :: xs
  | _, [] => rfl
  | x, y :: ys => by
    show x :: ((y :: ys).dropLast ++ [(y :: ys).getLast (by simp)]) = x :: y :: ys
    rw [dropLast_append_getLast_cons y ys]

namespace PointersMachineInternal

theorem curFrameM_bm_eq (m : Mach) :
    curFrameM (M := BM) m = curFrame m := by
  unfold curFrameM curFrame activeThreadM activeThread
  exact bind_congr_right _ (fun t => by cases t.stack.getLast? <;> rfl)

theorem mutateCurFrameM_bm_eq (m : Mach) (f : Frame → Frame) :
    mutateCurFrameM (M := BM) m f = mutateCurFrame m f := by
  unfold mutateCurFrameM mutateCurFrame activeThreadM activeThread
  refine bind_congr_right _ (fun t => ?_)
  cases t.stack.getLast? with
  | none => rfl
  | some fr => exact bind_congr_right _ (fun _ => rfl)

theorem tryMutateCurFrameM_bm_eq (m : Mach)
    (f g : Frame → Gen.ConcurrentMemory BM → Interp (Frame × Gen.ConcurrentMemory BM))
    (hfg : ∀ fr cm, f fr cm = g fr cm) :
    tryMutateCurFrameM (M := BM) m f = tryMutateCurFrame m g := by
  unfold tryMutateCurFrameM tryMutateCurFrame activeThreadM activeThread
  refine bind_congr_right _ (fun t => ?_)
  cases t.stack.getLast? with
  | none => rfl
  | some fr =>
    dsimp only
    exact bind_congr (hfg fr m.mem) (fun ⟨_, _⟩ => bind_congr_right _ (fun _ => rfl))

theorem jumpToBlockM_bm_eq (m : Mach) (b : Gen.BbName) :
    jumpToBlockM (M := BM) m b = jumpToBlock m b :=
  mutateCurFrameM_bm_eq m _

end PointersMachineInternal

/-- On `M = BM`, `mutateCurFrameOutM` wrapping `ConcurrentMemory.retag_ptr`
reduces unconditionally to `(retagPtrBM m ptr).map (·, m)` for every `m : Mach`. -/
theorem mutateCurFrameOutM_retag_bm_eq (m : Mach) (ptr : Gen.Pointer Prov)
    (ptrTy : Gen.PtrType) (fnEntry : Bool) (iw : Gen.StackFrame BM → Bool) :
    mutateCurFrameOutM (M := BM) m (fun fr cm => do
      let (ptr', cm', extra') ←
        ConcurrentMemory.retag_ptr cm fr.extra ptr ptrTy fnEntry (iw fr) (vtableLookupM m)
      pure (ptr', { fr with extra := extra' }, cm')) =
    (do let ptr' ← retagPtrBM m ptr; pure (ptr', m)) := by
  unfold mutateCurFrameOutM retagPtrBM listIndex
  by_cases hnonneg : 0 ≤ m.active_thread
  · simp only [hnonneg, ↓reduceIte]
    cases hget : m.threads[m.active_thread.toNat]? with
    | none => rfl
    | some t =>
      dsimp only [pure, Except.pure, bind, Except.bind]
      cases hst : t.stack with
      | nil => rfl
      | cons hd tl =>
        have hlast : (hd :: tl).getLast? = some ((hd :: tl).getLast (by simp)) :=
          List.getLast?_eq_some_getLast (by simp)
        have hdrop : (hd :: tl).dropLast ++ [(hd :: tl).getLast (by simp)] = hd :: tl :=
          dropLast_append_getLast_cons hd tl
        obtain ⟨hlt, hval⟩ := List.getElem?_eq_some_iff.mp hget
        have ht_self : ({ t with stack := hd :: tl } : Gen.Thread BM) = t := by
          cases t; simp at hst; subst hst; rfl
        have hset : listSet m.threads m.active_thread t "mutate_at" = .ok m.threads := by
          unfold listSet
          have hcond : 0 ≤ m.active_thread ∧ m.active_thread.toNat < m.threads.length :=
            ⟨hnonneg, hlt⟩
          simp [hcond, ← hval, List.set_getElem_self, pure, Except.pure]
        simp only [hlast, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte,
          ConcurrentMemory.retag_ptr, MemoryOps.retag_ptr,
          pure, Except.pure, bind, Except.bind, hdrop, ht_self, hset]
  · simp only [hnonneg, ↓reduceIte, bind, Except.bind, specPanic]

private theorem evalConstantM_bm_eq (m : Mach) (c : Gen.Constant) :
    evalConstantM (M := BM) m c = evalConstant m c := by
  cases c <;> rfl

private theorem evalPlaceM_local_bm_eq (m : Mach) (name : Gen.LocalName) :
    evalPlaceM (M := BM) m (.Local name) = evalPlace m (.Local name) := by
  unfold evalPlaceM evalPlace
  rw [curFrameM_bm_eq]
  cases curFrame m with
  | error _ => rfl
  | ok fr =>
    dsimp only [bind, Except.bind]
    cases mapIndex fr.func.locals name "self.cur_frame().func.locals[name]" with
    | error _ => rfl
    | ok _ =>
      dsimp only [bind, Except.bind]
      cases mapGet fr.locals name <;> rfl

private theorem evalPlaceM_field_bm_eq (m : Mach) (root : Gen.PlaceExpr) (field : Int)
    (ihRoot : evalPlaceM (M := BM) m root = evalPlace m root) :
    evalPlaceM (M := BM) m (.Field root field) = evalPlace m (.Field root field) := by
  unfold evalPlaceM evalPlace
  refine bind_congr ihRoot (fun ⟨⟨rootPl, ty⟩, m1⟩ => ?_)
  dsimp only
  have htail : ∀ (p : Gen.Offset × Gen.«Type»),
      (show Interp ((Gen.Place BM × Gen.«Type») × Mach) from do
        let rlay ← Type.layout ty
        let rootSize ← computeSizeM (M := BM) m1 rlay rootPl.ptr.metadata
        if (!decide (p.1.bytes ≤ rootSize.bytes)) = true then
          specPanic "assertion failed: offset <= self.compute_size(ty.layout::<M::T>(), root.ptr.metadata)"
        else do
          let ptr ← ptrOffsetInboundsM (M := BM) m1 rootPl.ptr.thin_pointer (p.1.bytes : Int)
          let flay ← Type.layout p.2
          pure ((({ ptr := (if (!LayoutStrategy.is_sized flay) = true then ThinPointer.widen ptr rootPl.ptr.metadata else ThinPointer.widen ptr none), aligned := rootPl.aligned } : Gen.Place BM), p.2), m1)) =
      (show Interp ((Gen.Place BM × Gen.«Type») × Mach) from do
        let rlay ← Type.layout ty
        let rootSize ← computeSize m1 rlay rootPl.ptr.metadata
        if (!decide (p.1.bytes ≤ rootSize.bytes)) = true then
          specPanic "assertion failed: offset <= self.compute_size(ty.layout::<M::T>(), root.ptr.metadata)"
        else do
          let ptr ← ptrOffsetInbounds m1 rootPl.ptr.thin_pointer (p.1.bytes : Int)
          let flay ← Type.layout p.2
          pure ((({ ptr := (if (!LayoutStrategy.is_sized flay) = true then ThinPointer.widen ptr rootPl.ptr.metadata else ThinPointer.widen ptr none), aligned := rootPl.aligned } : Gen.Place BM), p.2), m1)) := by
    intro p
    refine bind_congr_right _ (fun rlay => ?_)
    refine bind_congr (computeSizeM_bm_eq m1 rlay rootPl.ptr.metadata) (fun _ => ?_)
    split
    · rfl
    · exact bind_congr (ptrOffsetInboundsM_bm_eq m1 rootPl.ptr.thin_pointer _) (fun _ =>
        bind_congr_right _ (fun _ => rfl))
  cases ty with
  | Tuple sizedFields sizedHeadLayout unsizedField =>
    dsimp only
    split
    · exact bind_congr_right _ htail
    · split
      · cases unsizedField with
        | none => rfl
        | some tailTy =>
          dsimp only
          exact bind_congr_right _ (fun tlay =>
            bind_congr (computeAlignM_bm_eq m1 tlay rootPl.ptr.metadata) (fun tailAlign => by
              dsimp only [pure, Except.pure, bind, Except.bind]
              exact htail (TupleHeadLayout.tail_offset sizedHeadLayout tailAlign, tailTy)))
      · rfl
  | Union _ _ _ _ => dsimp only; exact bind_congr_right _ htail
  | _ => rfl

private theorem evalPlaceM_index_bm_eq (m : Mach) (root : Gen.PlaceExpr) (index : Gen.ValueExpr)
    (ihRoot : evalPlaceM (M := BM) m root = evalPlace m root)
    (ihIdx : ∀ m1, evalValueM (M := BM) m1 index = evalValue m1 index) :
    evalPlaceM (M := BM) m (.Index root index) = evalPlace m (.Index root index) := by
  unfold evalPlaceM evalPlace
  refine bind_congr ihRoot (fun ⟨⟨rootPl, ty⟩, m1⟩ => ?_)
  dsimp only
  refine bind_congr (ihIdx m1) (fun ⟨⟨idxVal, _⟩, m2⟩ => ?_)
  dsimp only
  have htail : ∀ (pm : Option (Gen.PointerMeta Prov)) (idx : Int) (p : Gen.«Type» × Int),
      (if idx < 0 ∨ idx ≥ p.2 then ub "access to out-of-bounds index"
       else do
         let elemLayout ← Type.layout p.1
         let elemSize ← LayoutStrategy.expect_size elemLayout "WF ensures array & slice elements are sized"
         let offset ← Size.mulInt elemSize idx
         let rlay ← Type.layout ty
         let rootSize ← computeSizeM (M := BM) m2 rlay pm
         if offset.bytes ≤ rootSize.bytes then do
           let ptr ← ptrOffsetInboundsM (M := BM) m2 rootPl.ptr.thin_pointer (offset.bytes : Int)
           pure ((({ ptr := ThinPointer.widen ptr none, aligned := rootPl.aligned } : Gen.Place BM), p.1), m2)
         else specPanic "sanity check: the indexed offset should not be outside what the type allows.") =
      (if idx < 0 ∨ idx ≥ p.2 then ub "access to out-of-bounds index"
       else do
         let elemLayout ← Type.layout p.1
         let elemSize ← LayoutStrategy.expect_size elemLayout "WF ensures array & slice elements are sized"
         let offset ← Size.mulInt elemSize idx
         let rlay ← Type.layout ty
         let rootSize ← computeSize m2 rlay pm
         if offset.bytes ≤ rootSize.bytes then do
           let ptr ← ptrOffsetInbounds m2 rootPl.ptr.thin_pointer (offset.bytes : Int)
           pure ((({ ptr := ThinPointer.widen ptr none, aligned := rootPl.aligned } : Gen.Place BM), p.1), m2)
         else specPanic "sanity check: the indexed offset should not be outside what the type allows.") := by
    intro pm idx p
    split
    · rfl
    · apply bind_congr_right; intro _
      apply bind_congr_right; intro _
      apply bind_congr_right; intro _
      apply bind_congr_right; intro rlay
      refine bind_congr (computeSizeM_bm_eq m2 rlay pm) (fun _ => ?_)
      split
      · exact bind_congr (ptrOffsetInboundsM_bm_eq m2 rootPl.ptr.thin_pointer _) (fun _ => rfl)
      · rfl
  cases idxVal with
  | Int i =>
    dsimp only [pure, Except.pure, bind, Except.bind]
    cases ty with
    | Array elem count =>
      dsimp only [pure, Except.pure, bind, Except.bind]
      exact htail rootPl.ptr.metadata i (elem, count)
    | Slice elem =>
      dsimp only
      rcases rootPl.ptr.metadata with _ | (count | _)
      · rfl
      · dsimp only [pure, Except.pure, bind, Except.bind]
        exact htail (some (.ElementCount count)) i (elem, count)
      · rfl
    | _ => rfl
  | _ => rfl

private theorem evalPlaceM_deref_bm_eq (m : Mach) (operand : Gen.ValueExpr) (ty : Gen.«Type»)
    (ihOp : evalValueM (M := BM) m operand = evalValue m operand) :
    evalPlaceM (M := BM) m (.Deref operand ty) = evalPlace m (.Deref operand ty) := by
  unfold evalPlaceM evalPlace
  refine bind_congr ihOp (fun ⟨⟨v, vTy⟩, m1⟩ => ?_)
  dsimp only
  cases v with
  | Ptr ptr =>
    cases vTy with
    | Ptr ptrType =>
      dsimp only
      have htail :
          (do
            let lay ← Type.layout ty
            let align ← computeAlignM (M := BM) m1 lay ptr.metadata
            pure ((({ ptr := ptr, aligned := Align.is_aligned align ptr.thin_pointer.addr } : Gen.Place BM), ty), m1)) =
          (do
            let lay ← Type.layout ty
            let align ← computeAlign m1 lay ptr.metadata
            pure ((({ ptr := ptr, aligned := Align.is_aligned align ptr.thin_pointer.addr } : Gen.Place BM), ty), m1)) :=
        bind_congr_right _ (fun lay =>
          bind_congr (computeAlignM_bm_eq m1 lay ptr.metadata) (fun _ => rfl))
      cases PtrType.safe_pointee ptrType with
      | none =>
        dsimp only [pure, Except.pure, bind, Except.bind]
        exact htail
      | some pointee =>
        dsimp only
        refine bind_congr (computeAlignM_bm_eq m1 pointee.layout ptr.metadata) (fun _ => ?_)
        split
        · rfl
        · refine bind_congr (computeSizeM_bm_eq m1 pointee.layout ptr.metadata) (fun pSize => ?_)
          dsimp only [cm_dereferenceable_bm_eq]
          generalize CM.dereferenceable m1.mem ptr.thin_pointer pSize = d
          rcases d with _ | ⟨⟩
          · rfl
          · dsimp only [pure, Except.pure, bind, Except.bind]
            exact htail
    | _ => rfl
  | _ => rfl

private theorem evalPlaceM_downcast_bm_eq (m : Mach) (root : Gen.PlaceExpr) (discriminant : Int)
    (ihRoot : evalPlaceM (M := BM) m root = evalPlace m root) :
    evalPlaceM (M := BM) m (.Downcast root discriminant) =
      evalPlace m (.Downcast root discriminant) := by
  unfold evalPlaceM evalPlace
  exact bind_congr ihRoot (fun ⟨⟨_, _⟩, _⟩ => rfl)

private theorem evalValueM_constant_bm_eq (m : Mach) (c : Gen.Constant) (ty : Gen.«Type») :
    evalValueM (M := BM) m (.Constant c ty) = evalValue m (.Constant c ty) := by
  unfold evalValueM evalValue
  rw [evalConstantM_bm_eq]

private theorem evalValueM_tuple_bm_eq (m : Mach) (exprs : List Gen.ValueExpr) (ty : Gen.«Type»)
    (ihExprs : evalValuesM (M := BM) m exprs = evalValues m exprs) :
    evalValueM (M := BM) m (.Tuple exprs ty) = evalValue m (.Tuple exprs ty) := by
  unfold evalValueM evalValue
  rw [ihExprs]

private theorem evalValueM_load_bm_eq (m : Mach) (source : Gen.PlaceExpr)
    (ihSrc : evalPlaceM (M := BM) m source = evalPlace m source) :
    evalValueM (M := BM) m (.Load source) = evalValue m (.Load source) := by
  unfold evalValueM evalValue
  rw [ihSrc]
  rcases evalPlace m source with _ | ⟨⟨place, ty⟩, m1⟩
  · rfl
  · dsimp only [bind, Except.bind]
    rw [placeLoadM_bm_eq]

private theorem evalValueM_addrOf_bm_eq (m : Mach) (target : Gen.PlaceExpr) (ptrTy : Gen.PtrType)
    (ihTgt : evalPlaceM (M := BM) m target = evalPlace m target) :
    evalValueM (M := BM) m (.AddrOf target ptrTy) = evalValue m (.AddrOf target ptrTy) := by
  unfold evalValueM evalValue
  refine bind_congr ihTgt (fun ⟨⟨place, _⟩, m1⟩ => ?_)
  dsimp only
  refine bind_congr (checkValueM_bm_eq (.Ptr place.ptr) (.Ptr ptrTy) (some m1)) (fun _ => ?_)
  rw [mutateCurFrameOutM_retag_bm_eq m1 place.ptr ptrTy false (fun _ => true)]
  cases retagPtrBM m1 place.ptr <;> rfl

private theorem evalValueM_unOp_bm_eq (m : Mach) (operator : Gen.UnOp) (operand : Gen.ValueExpr)
    (ihOp : evalValueM (M := BM) m operand = evalValue m operand) :
    evalValueM (M := BM) m (.UnOp operator operand) = evalValue m (.UnOp operator operand) := by
  unfold evalValueM evalValue
  rw [ihOp]
  rcases evalValue m operand with _ | ⟨arg, m1⟩
  · rfl
  · dsimp only [bind, Except.bind]
    rw [evalUnOpM_bm_eq]

private theorem evalValueM_binOp_bm_eq (m : Mach) (operator : Gen.BinOp)
    (left right : Gen.ValueExpr)
    (ihLeft : evalValueM (M := BM) m left = evalValue m left)
    (ihRight : ∀ m1, evalValueM (M := BM) m1 right = evalValue m1 right) :
    evalValueM (M := BM) m (.BinOp operator left right) =
      evalValue m (.BinOp operator left right) := by
  cases operator with
  | PtrOffset inbounds =>
    unfold evalValueM evalValue
    rw [ihLeft]
    rcases evalValue m left with _ | ⟨lp, m1⟩
    · rfl
    · dsimp only [bind, Except.bind]
      rw [ihRight m1]
      rcases evalValue m1 right with _ | ⟨rp, m2⟩
      · rfl
      · dsimp only [bind, Except.bind]
        rw [evalPtrOffsetM_bm_eq]
  | PtrOffsetFrom inbounds nonneg =>
    unfold evalValueM evalValue
    rw [ihLeft]
    rcases evalValue m left with _ | ⟨lp, m1⟩
    · rfl
    · dsimp only [bind, Except.bind]
      rw [ihRight m1]
      rcases evalValue m1 right with _ | ⟨rp, m2⟩
      · rfl
      · dsimp only [bind, Except.bind]
        rw [evalPtrOffsetFromM_bm_eq]
  | Int iop =>
    unfold evalValueM evalValue
    rw [ihLeft]
    rcases evalValue m left with _ | ⟨lp, m1⟩
    · rfl
    · dsimp only [bind, Except.bind]
      rw [ihRight m1]
      rcases evalValue m1 right with _ | ⟨rp, m2⟩
      · rfl
      · dsimp only [bind, Except.bind]
        rw [evalBinOpM_bm_eq]
  | IntWithOverflow iop =>
    unfold evalValueM evalValue
    rw [ihLeft]
    rcases evalValue m left with _ | ⟨lp, m1⟩
    · rfl
    · dsimp only [bind, Except.bind]
      rw [ihRight m1]
      rcases evalValue m1 right with _ | ⟨rp, m2⟩
      · rfl
      · dsimp only [bind, Except.bind]
        rw [evalBinOpM_bm_eq]
  | Rel rop =>
    unfold evalValueM evalValue
    rw [ihLeft]
    rcases evalValue m left with _ | ⟨lp, m1⟩
    · rfl
    · dsimp only [bind, Except.bind]
      rw [ihRight m1]
      rcases evalValue m1 right with _ | ⟨rp, m2⟩
      · rfl
      · dsimp only [bind, Except.bind]
        rw [evalBinOpM_bm_eq]
  | ConstructWidePointer _ =>
    unfold evalValueM evalValue
    rw [ihLeft]
    rcases evalValue m left with _ | ⟨lp, m1⟩
    · rfl
    · dsimp only [bind, Except.bind]
      rw [ihRight m1]
      rcases evalValue m1 right with _ | ⟨rp, m2⟩
      · rfl
      · dsimp only [bind, Except.bind]
        rw [evalBinOpM_bm_eq]

private theorem evalValueM_union_bm_eq (m : Mach) (field : Int) (expr : Gen.ValueExpr)
    (unionTy : Gen.«Type»)
    (ihExpr : evalValueM (M := BM) m expr = evalValue m expr) :
    evalValueM (M := BM) m (.Union field expr unionTy) =
      evalValue m (.Union field expr unionTy) := by
  unfold evalValueM evalValue
  cases unionTy with
  | Union fields chunks size align =>
    dsimp only [pure, Except.pure, bind, Except.bind]
    refine bind_congr_right _ (fun ⟨offset, exprTy⟩ => ?_)
    dsimp only
    refine bind_congr ihExpr (fun ⟨⟨val, _⟩, m1⟩ => ?_)
    dsimp only
    refine bind_congr (Type.encodeM_bm_eq exprTy val) (fun encoded => ?_)
    refine bind_congr_right _ (fun data => ?_)
    exact bind_congr (Type.decodeM_bm_eq (.Union fields chunks size align) data)
      (fun optV => by cases optV <;> rfl)
  | _ => rfl

private theorem evalValueM_variant_bm_eq (m : Mach) (discriminant : Int) (data : Gen.ValueExpr)
    (enumTy : Gen.«Type»)
    (ihData : evalValueM (M := BM) m data = evalValue m data) :
    evalValueM (M := BM) m (.Variant discriminant data enumTy) =
      evalValue m (.Variant discriminant data enumTy) := by
  unfold evalValueM evalValue
  exact bind_congr ihData (fun ⟨⟨_, _⟩, _⟩ => rfl)

private theorem evalValueM_getDiscriminant_bm_eq (m : Mach) (place : Gen.PlaceExpr)
    (ihPlace : evalPlaceM (M := BM) m place = evalPlace m place) :
    evalValueM (M := BM) m (.GetDiscriminant place) = evalValue m (.GetDiscriminant place) := by
  unfold evalValueM evalValue
  refine bind_congr ihPlace (fun ⟨⟨pl, ty⟩, m1⟩ => ?_)
  dsimp only
  cases ty with
  | Enum variants discriminantTy discriminator size align =>
    dsimp only
    split
    · rfl
    · have hacc :
          (fun (m : Mach) (idx : Gen.Offset) (sz : Size) => do
            let ptr ← ptrOffsetInboundsM (M := BM) m pl.ptr.thin_pointer (idx.bytes : Int)
            let (bytes, cm) ← ConcurrentMemory.load (M := BM) m.mem ptr sz ⟨1⟩ .None
            pure (bytes, { m with mem := cm })) =
          (fun (m : Mach) (idx : Gen.Offset) (sz : Size) => do
            let ptr ← ptrOffsetInbounds m pl.ptr.thin_pointer (idx.bytes : Int)
            let (bytes, cm) ← CM.load m.mem ptr sz ⟨1⟩ .None
            pure (bytes, { m with mem := cm })) := by
        funext m0 idx sz
        exact bind_congr (ptrOffsetInboundsM_bm_eq m0 pl.ptr.thin_pointer _) (fun ptr =>
          bind_congr (cm_load_bm_eq m0.mem ptr sz ⟨1⟩ .None) (fun ⟨_, _⟩ => rfl))
      rw [hacc]
      exact bind_congr (decodeDiscriminantM_bm_eq _ discriminator m1)
        (fun ⟨opt, _⟩ => by cases opt <;> rfl)
  | _ => rfl

private theorem evalValuesM_nil_bm_eq (m : Mach) :
    evalValuesM (M := BM) m [] = evalValues m [] := by
  unfold evalValuesM evalValues; rfl

private theorem evalValuesM_cons_bm_eq (m : Mach) (e : Gen.ValueExpr) (es : List Gen.ValueExpr)
    (ihHead : evalValueM (M := BM) m e = evalValue m e)
    (ihTail : ∀ m1, evalValuesM (M := BM) m1 es = evalValues m1 es) :
    evalValuesM (M := BM) m (e :: es) = evalValues m (e :: es) := by
  unfold evalValuesM evalValues
  rw [ihHead]
  rcases evalValue m e with _ | ⟨⟨val, _⟩, m1⟩
  · rfl
  · dsimp only [bind, Except.bind]
    rw [ihTail m1]

private theorem evalExprsM_bm_eq_fuel :
    ∀ (fuel : Nat),
      (∀ (pe : Gen.PlaceExpr), sizeOf pe < fuel → ∀ (m : Mach),
        evalPlaceM (M := BM) m pe = evalPlace m pe) ∧
      (∀ (ve : Gen.ValueExpr), sizeOf ve < fuel → ∀ (m : Mach),
        evalValueM (M := BM) m ve = evalValue m ve) ∧
      (∀ (es : List Gen.ValueExpr), sizeOf es < fuel → ∀ (m : Mach),
        evalValuesM (M := BM) m es = evalValues m es)
  | 0 =>
    ⟨fun _ h => absurd h (Nat.not_lt_zero _),
     fun _ h => absurd h (Nat.not_lt_zero _),
     fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | fuel + 1 =>
    let ⟨ihPlace, ihVal, ihVals⟩ := evalExprsM_bm_eq_fuel fuel
    ⟨fun pe hfuel m => by
      cases pe with
      | Local name => exact evalPlaceM_local_bm_eq m name
      | Field root field =>
        exact evalPlaceM_field_bm_eq m root field
          (ihPlace root (by revert hfuel; simp_wf; omega) m)
      | Index root index =>
        exact evalPlaceM_index_bm_eq m root index
          (ihPlace root (by revert hfuel; simp_wf; omega) m)
          (ihVal index (by revert hfuel; simp_wf; omega))
      | Deref operand ty =>
        exact evalPlaceM_deref_bm_eq m operand ty
          (ihVal operand (by revert hfuel; simp_wf; omega) m)
      | Downcast root discriminant =>
        exact evalPlaceM_downcast_bm_eq m root discriminant
          (ihPlace root (by revert hfuel; simp_wf; omega) m),
     fun ve hfuel m => by
      cases ve with
      | Constant c ty => exact evalValueM_constant_bm_eq m c ty
      | Tuple exprs ty =>
        exact evalValueM_tuple_bm_eq m exprs ty
          (ihVals exprs (by revert hfuel; simp_wf; omega) m)
      | Load source =>
        exact evalValueM_load_bm_eq m source
          (ihPlace source (by revert hfuel; simp_wf; omega) m)
      | AddrOf target ptrTy =>
        exact evalValueM_addrOf_bm_eq m target ptrTy
          (ihPlace target (by revert hfuel; simp_wf; omega) m)
      | UnOp operator operand =>
        exact evalValueM_unOp_bm_eq m operator operand
          (ihVal operand (by revert hfuel; simp_wf; omega) m)
      | BinOp operator left right =>
        exact evalValueM_binOp_bm_eq m operator left right
          (ihVal left (by revert hfuel; simp_wf; omega) m)
          (ihVal right (by revert hfuel; simp_wf; omega))
      | Union field expr unionTy =>
        exact evalValueM_union_bm_eq m field expr unionTy
          (ihVal expr (by revert hfuel; simp_wf; omega) m)
      | Variant discriminant data enumTy =>
        exact evalValueM_variant_bm_eq m discriminant data enumTy
          (ihVal data (by revert hfuel; simp_wf; omega) m)
      | GetDiscriminant place =>
        exact evalValueM_getDiscriminant_bm_eq m place
          (ihPlace place (by revert hfuel; simp_wf; omega) m),
     fun es hfuel m => by
      cases es with
      | nil => exact evalValuesM_nil_bm_eq m
      | cons e es =>
        exact evalValuesM_cons_bm_eq m e es
          (ihVal e (by revert hfuel; simp_wf; omega) m)
          (ihVals es (by revert hfuel; simp_wf; omega))⟩

theorem evalPlaceM_bm_eq :
    ∀ (m : Mach) (pe : Gen.PlaceExpr),
      evalPlaceM (M := BM) m pe = evalPlace m pe :=
  fun m pe => (evalExprsM_bm_eq_fuel (sizeOf pe + 1)).1 pe (Nat.lt_succ_self _) m

theorem evalValueM_bm_eq :
    ∀ (m : Mach) (ve : Gen.ValueExpr),
      evalValueM (M := BM) m ve = evalValue m ve :=
  fun m ve => (evalExprsM_bm_eq_fuel (sizeOf ve + 1)).2.1 ve (Nat.lt_succ_self _) m

theorem evalValuesM_bm_eq :
    ∀ (m : Mach) (es : List Gen.ValueExpr),
      evalValuesM (M := BM) m es = evalValues m es :=
  fun m es => (evalExprsM_bm_eq_fuel (sizeOf es + 1)).2.2 es (Nat.lt_succ_self _) m

end MiniRustSpec.Correspondence
