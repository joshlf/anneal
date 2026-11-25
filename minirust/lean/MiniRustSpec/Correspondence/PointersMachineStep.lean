/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import MiniRustSpec.Correspondence.PointersMachineExpr

/-!
# Polymorphic `Machine<BM>` and `Mach` equivalence: statements, terminators, and machine steps

Third of the four submodules of `MiniRustSpec.Correspondence.PointersMachine`: value
retagging (`retagValM_bm_eq`), statement and terminator evaluation (`evalStatementM_bm_eq`,
`evalTerminatorM_bm_eq`), and machine stepping (`stepM_bm_eq`, `stepsM_bm_eq`).
-/

namespace MiniRustSpec.Correspondence

open MiniRustSpec
open MiniRustSpec.LibSpecr
open MiniRustSpec.Interp
open PointersMachineInternal

mutual

theorem retagValM_bm_eq :
    ∀ (m : Mach) (fnEntry : Bool) (val : Val) (ty : Gen.«Type»),
      retagValM (M := BM) m fnEntry val ty =
        (do let v' ← retagVal m fnEntry val ty; pure (v', m))
  | m, fnEntry, .Int _, _ => by unfold retagValM retagVal; rfl
  | m, fnEntry, .Bool _, _ => by unfold retagValM retagVal; rfl
  | m, fnEntry, .Union _, _ => by unfold retagValM retagVal; rfl
  | m, fnEntry, .Ptr ptr, .Ptr ptrType => by
    unfold retagValM retagVal
    dsimp only
    have hret := mutateCurFrameOutM_retag_bm_eq m ptr ptrType fnEntry (fun fr => fr.func.implicit_writes)
    rw [hret]
    cases retagPtrBM m ptr <;> rfl
  | m, fnEntry, .Ptr _, .Int _ | m, fnEntry, .Ptr _, .Bool | m, fnEntry, .Ptr _, .Union _ _ _ _
  | m, fnEntry, .Ptr _, .Tuple _ _ _ | m, fnEntry, .Ptr _, .Array _ _
  | m, fnEntry, .Ptr _, .Enum _ _ _ _ _ | m, fnEntry, .Ptr _, .Slice _
  | m, fnEntry, .Ptr _, .TraitObject _ => by unfold retagValM retagVal; rfl
  | m, fnEntry, .Tuple vals, .Tuple sizedFields _ _ => by
    unfold retagValM retagVal
    rw [retagTupleFieldsM_bm_eq m fnEntry vals sizedFields]
    cases retagTupleFields m fnEntry vals sizedFields <;> rfl
  | m, fnEntry, .Tuple vals, .Array elemTy _ => by
    unfold retagValM retagVal
    rw [retagArrayElemsM_bm_eq m fnEntry elemTy vals]
    cases vals.mapM (fun val => retagVal m fnEntry val elemTy) <;> rfl
  | m, fnEntry, .Tuple _, .Int _ | m, fnEntry, .Tuple _, .Bool | m, fnEntry, .Tuple _, .Union _ _ _ _
  | m, fnEntry, .Tuple _, .Ptr _ | m, fnEntry, .Tuple _, .Enum _ _ _ _ _
  | m, fnEntry, .Tuple _, .Slice _ | m, fnEntry, .Tuple _, .TraitObject _ => by
    unfold retagValM retagVal; rfl
  | m, fnEntry, .Variant discriminant data, .Enum variants _ _ _ _ => by
    unfold retagValM retagVal
    cases mapIndex variants discriminant "variants[discriminant]" with
    | error _ => rfl
    | ok variant =>
      dsimp only [bind, Except.bind]
      rw [retagValM_bm_eq m fnEntry data variant.ty]
      cases retagVal m fnEntry data variant.ty <;> rfl
  | m, fnEntry, .Variant _ _, .Int _ | m, fnEntry, .Variant _ _, .Bool
  | m, fnEntry, .Variant _ _, .Union _ _ _ _ | m, fnEntry, .Variant _ _, .Ptr _
  | m, fnEntry, .Variant _ _, .Tuple _ _ _ | m, fnEntry, .Variant _ _, .Array _ _
  | m, fnEntry, .Variant _ _, .Slice _ | m, fnEntry, .Variant _ _, .TraitObject _ => by
    unfold retagValM retagVal; rfl

theorem retagTupleFieldsM_bm_eq :
    ∀ (m : Mach) (fnEntry : Bool) (vals : List Val) (fields : List (Gen.Offset × Gen.«Type»)),
      retagTupleFieldsM (M := BM) m fnEntry vals fields =
        (do let vs' ← retagTupleFields m fnEntry vals fields; pure (vs', m))
  | m, _, [], [] => by unfold retagTupleFieldsM retagTupleFields; rfl
  | _, _, [], _ :: _ => by unfold retagTupleFieldsM retagTupleFields; rfl
  | _, _, _ :: _, [] => by unfold retagTupleFieldsM retagTupleFields; rfl
  | m, fnEntry, val :: vals, (_, ty) :: fields => by
    unfold retagTupleFieldsM retagTupleFields
    rw [retagValM_bm_eq m fnEntry val ty]
    cases retagVal m fnEntry val ty with
    | error _ => rfl
    | ok v' =>
      dsimp only [bind, Except.bind, pure, Except.pure]
      rw [retagTupleFieldsM_bm_eq m fnEntry vals fields]
      cases retagTupleFields m fnEntry vals fields <;> rfl

theorem retagArrayElemsM_bm_eq :
    ∀ (m : Mach) (fnEntry : Bool) (elemTy : Gen.«Type») (vals : List Val),
      retagArrayElemsM (M := BM) m fnEntry elemTy vals =
        (do let vs' ← vals.mapM (fun val => retagVal m fnEntry val elemTy); pure (vs', m))
  | m, _, _, [] => by
    unfold retagArrayElemsM
    rfl
  | m, fnEntry, elemTy, val :: vals => by
    unfold retagArrayElemsM
    rw [retagValM_bm_eq m fnEntry val elemTy]
    have hmapM : ∀ (f : Val → Interp Val) (acc : List Val),
        List.mapM.loop f vals acc =
          (do let tl ← List.mapM.loop f vals []; pure (acc.reverse ++ tl)) := by
      intro f
      induction vals with
      | nil =>
        intro acc
        simp [List.mapM.loop, pure, Except.pure, bind, Except.bind]
      | cons w ws ih =>
        intro acc
        simp only [List.mapM.loop]
        cases f w with
        | error _ => rfl
        | ok w' =>
          dsimp only [bind, Except.bind]
          rw [ih (w' :: acc), ih [w']]
          cases List.mapM.loop f ws [] with
          | error _ => rfl
          | ok tl =>
            simp [pure, Except.pure, bind, Except.bind, List.append_assoc]
    unfold List.mapM
    simp only [List.mapM.loop]
    cases retagVal m fnEntry val elemTy with
    | error _ => rfl
    | ok v' =>
      dsimp only [bind, Except.bind, pure, Except.pure]
      rw [retagArrayElemsM_bm_eq m fnEntry elemTy vals]
      unfold List.mapM
      rw [hmapM _ [v']]
      cases List.mapM.loop (fun v => retagVal m fnEntry v elemTy) vals [] <;> rfl

end

theorem evalStatementM_bm_eq (m : Mach) (stmt : Gen.Statement) :
    evalStatementM (M := BM) m stmt = evalStatement m stmt := by
  cases stmt with
  | Assign dst src =>
    dsimp only [evalStatementM, evalStatement]
    rw [evalPlaceM_bm_eq]
    rcases evalPlace m dst with _ | ⟨⟨place, ty⟩, m1⟩
    · rfl
    · dsimp only [bind, Except.bind]
      rw [evalValueM_bm_eq]
      rcases evalValue m1 src with _ | ⟨⟨val, _⟩, m2⟩
      · rfl
      · exact placeStoreM_bm_eq m2 place val ty
  | PlaceMention place =>
    dsimp only [evalStatementM, evalStatement]
    rw [evalPlaceM_bm_eq]
  | Validate place fnEntry =>
    dsimp only [evalStatementM, evalStatement]
    rw [evalPlaceM_bm_eq]
    rcases evalPlace m place with _ | ⟨⟨p, ty⟩, m1⟩
    · rfl
    · dsimp only [bind, Except.bind]
      rw [placeLoadM_bm_eq]
      rcases placeLoad m1 p ty with _ | ⟨val, m2⟩
      · rfl
      · dsimp only [bind, Except.bind]
        rw [retagValM_bm_eq]
        cases retagVal m2 fnEntry val ty with
        | error _ => rfl
        | ok v' =>
          dsimp only [bind, Except.bind, pure, Except.pure]
          exact placeStoreM_bm_eq m2 p v' ty
  | StorageLive local_ =>
    dsimp only [evalStatementM, evalStatement]
    exact tryMutateCurFrameM_bm_eq m _ _ (fun fr cm => storageLiveM_bm_eq fr cm local_)
  | StorageDead local_ =>
    dsimp only [evalStatementM, evalStatement]
    exact tryMutateCurFrameM_bm_eq m _ _ (fun fr cm => storageDeadM_bm_eq fr cm local_)
  | Deinit place =>
    dsimp only [evalStatementM, evalStatement]
    rw [evalPlaceM_bm_eq]
    rcases evalPlace m place with _ | ⟨⟨p, ty⟩, m1⟩
    · rfl
    · dsimp only [bind, Except.bind]
      split
      · rfl
      · cases Type.layout ty with
        | error _ => rfl
        | ok lay =>
          dsimp only [bind, Except.bind]
          cases LayoutStrategy.expect_size lay "WF ensures deinits are sized" with
          | error _ => rfl
          | ok sz =>
            dsimp only [bind, Except.bind, cm_deinit_bm_eq]
  | SetDiscriminant dst value =>
    dsimp only [evalStatementM, evalStatement]
    unfold evalSetDiscriminantM evalSetDiscriminant
    refine bind_congr (evalPlaceM_bm_eq m dst) (fun ⟨⟨place, ty⟩, m1⟩ => ?_)
    dsimp only
    cases ty with
    | Enum variants _ _ _ _ =>
      dsimp only
      split
      · rfl
      · cases mapGet variants value with
        | none => rfl
        | some variant =>
          dsimp only
          rw [encodeDiscriminantM_bm_eq]
          rfl
    | _ => rfl

private theorem deallocAllM_bm_eq :
    ∀ (fuel : Nat) (fr : Frame) (cm : Gen.ConcurrentMemory BM),
      deallocAllM (M := BM) fuel fr cm = deallocAll fuel fr cm
  | 0, fr, cm => by
    unfold deallocAllM deallocAll
    rcases fr.locals.entries with _ | ⟨⟨_, _⟩, _⟩ <;> rfl
  | fuel + 1, fr, cm => by
    unfold deallocAllM deallocAll
    rcases fr.locals.entries with _ | ⟨⟨local_, _⟩, _⟩
    · rfl
    · dsimp only
      rw [storageDeadM_bm_eq]
      rcases storageDead fr cm local_ with _ | ⟨fr', cm'⟩
      · rfl
      · exact deallocAllM_bm_eq fuel fr' cm'

private theorem evalArgsM_bm_eq :
    ∀ (m : Mach) (es : List Gen.ValueExpr),
      evalArgsM (M := BM) m es = evalArgs m es
  | _, [] => rfl
  | m, e :: es => by
    unfold evalArgsM evalArgs
    rw [evalValueM_bm_eq m e]
    rcases evalValue m e with _ | ⟨arg, m1⟩
    · rfl
    · dsimp only [bind, Except.bind]
      rw [evalArgsM_bm_eq m1 es]

private theorem mutateCurStackM_bm_eq {α : Type} (m : Mach)
    (f : List Frame → Interp (α × List Frame)) :
    mutateCurStackM (M := BM) m f = mutateCurStack m f := rfl

private theorem fnFromPtrM_bm_eq (m : Mach) (v : Val) :
    fnFromPtrM (M := BM) m v = fnFromPtr m v := by
  cases v with
  | Ptr p =>
    rcases p with ⟨thinPtr, metadata⟩
    simp only [fnFromPtrM, fnFromPtr]
    split
    · rfl
    · split <;> split <;> simp_all
  | _ => rfl

private theorem prepareForInplacePassingM_bm_eq (m : Mach) (place : Gen.Place BM)
    (ty : Gen.«Type») :
    prepareForInplacePassingM (M := BM) m place ty = prepareForInplacePassing m place ty := by
  unfold prepareForInplacePassingM prepareForInplacePassing
  refine bind_congr_right _ (fun _ => ?_)
  refine bind_congr_right _ (fun sz => ?_)
  refine bind_congr_right _ (fun _ => ?_)
  refine bind_congr_right _ (fun al => ?_)
  exact bind_congr (cm_deinit_bm_eq m.mem place.ptr.thin_pointer sz al) (fun _ => rfl)

private theorem evalArgumentM_bm_eq (m : Mach) (arg : Gen.ArgumentExpr) :
    evalArgumentM (M := BM) m arg = evalArgument m arg := by
  cases arg with
  | ByValue v =>
    unfold evalArgumentM evalArgument
    exact evalValueM_bm_eq m v
  | InPlace p =>
    unfold evalArgumentM evalArgument
    refine bind_congr (evalPlaceM_bm_eq m p) (fun ⟨⟨place, ty⟩, m1⟩ => ?_)
    dsimp only
    refine bind_congr (placeLoadM_bm_eq m1 place ty) (fun ⟨v, m2⟩ => ?_)
    dsimp only
    exact bind_congr (prepareForInplacePassingM_bm_eq m2 place ty) (fun _ => rfl)

private theorem evalArgumentsM_bm_eq :
    ∀ (m : Mach) (args : List Gen.ArgumentExpr),
      evalArgumentsM (M := BM) m args = evalArguments m args
  | m, [] => by unfold evalArgumentsM evalArguments; rfl
  | m, a :: as => by
    unfold evalArgumentsM evalArguments
    refine bind_congr (evalArgumentM_bm_eq m a) (fun ⟨v, m1⟩ => ?_)
    dsimp only
    exact bind_congr (evalArgumentsM_bm_eq m1 as) (fun _ => rfl)

private theorem allocFrameArgsM_bm_eq :
    ∀ (fr : Frame) (cm : Gen.ConcurrentMemory BM) (ls : List Gen.LocalName),
      allocFrameArgsM (M := BM) fr cm ls = allocFrameArgs fr cm ls
  | fr, cm, [] => by unfold allocFrameArgsM allocFrameArgs; rfl
  | fr, cm, l :: ls => by
    unfold allocFrameArgsM allocFrameArgs
    refine bind_congr (storageLiveM_bm_eq fr cm l) (fun ⟨fr1, cm1⟩ => ?_)
    exact allocFrameArgsM_bm_eq fr1 cm1 ls

private theorem initFrameArgsM_bm_eq :
    ∀ (m : Mach) (frame : Frame) (ls : List Gen.LocalName) (args : List (Val × Gen.«Type»)),
      initFrameArgsM (M := BM) m frame ls args = initFrameArgs m frame ls args
  | m, frame, [], args => by unfold initFrameArgsM initFrameArgs; rfl
  | m, frame, _ :: _, [] => by unfold initFrameArgsM initFrameArgs; rfl
  | m, frame, l :: ls, (v, ty) :: args => by
    have ih : ∀ m', initFrameArgsM (M := BM) m' frame ls args = initFrameArgs m' frame ls args :=
      fun m' => initFrameArgsM_bm_eq m' frame ls args
    unfold initFrameArgsM initFrameArgs
    simp only [typedStoreM_bm_eq, ih]
    refine bind_congr_right _ (fun calleeTy => ?_)
    refine bind_congr_right _ (fun b => ?_)
    split
    · rfl
    · refine bind_congr_right _ (fun l => ?_)
      refine bind_congr_right _ (fun align => ?_)
      refine bind_congr_right _ (fun calleePtr => ?_)
      cases typedStore m calleePtr v ty align .None with
      | ok m' => rfl
      | error e => cases e <;> rfl

private theorem createFrameM_bm_eq (m : Mach) (func : Gen.Function)
    (spa : Gen.StackPopAction BM) (conv : Gen.CallingConvention) (retTy : Gen.«Type»)
    (args : List (Val × Gen.«Type»)) :
    createFrameM (M := BM) m func spa conv retTy args = createFrame m func spa conv retTy args := by
  unfold createFrameM createFrame
  refine bind_congr (storageLiveM_bm_eq _ m.mem func.ret) (fun ⟨fr1, cm1⟩ => ?_)
  dsimp only
  refine bind_congr (allocFrameArgsM_bm_eq fr1 cm1 func.args) (fun ⟨fr2, cm2⟩ => ?_)
  dsimp only
  split
  · rfl
  · refine bind_congr_right _ (fun _ => ?_)
    refine bind_congr_right _ (fun _ => ?_)
    split
    · rfl
    · split
      · rfl
      · exact bind_congr (initFrameArgsM_bm_eq _ fr2 func.args args) (fun _ => rfl)

private theorem evalCallM_bm_eq (m : Mach) (callee : Gen.Function) (conv : Gen.CallingConvention)
    (args : List (Val × Gen.«Type»)) (ret : Gen.Place BM × Gen.«Type»)
    (nb ub : Option Gen.BbName) :
    evalCallM (M := BM) m callee conv args ret nb ub = evalCall m callee conv args ret nb ub := by
  unfold evalCallM evalCall
  refine bind_congr (createFrameM_bm_eq _ _ _ _ _ _) (fun ⟨fr, m1⟩ => ?_)
  dsimp only
  exact bind_congr (mutateCurStackM_bm_eq m1 _) (fun _ => rfl)

private theorem machineExitM_bm_eq {α : Type} (m : Mach) :
    machineExitM (M := BM) (α := α) m = machineExit m := rfl

private theorem cm_allocate_bm_fun :
    @ConcurrentMemory.allocate BM _ _ = CM.allocate := by
  funext cm kind size align
  exact cm_allocate_bm_eq cm kind size align

private theorem cm_deallocate_bm_fun :
    @ConcurrentMemory.deallocate BM _ _ = CM.deallocate := by
  funext cm ptr kind size align
  exact cm_deallocate_bm_eq cm ptr kind size align

private theorem evalPrintM_bm_eq :
    ∀ (stream : DynWrite) (args : List (Val × Gen.«Type»)),
      evalPrintM (M := BM) stream args = evalPrint stream args
  | stream, [] => by unfold evalPrintM evalPrint; rfl
  | stream, (v, _) :: rest => by
    unfold evalPrintM evalPrint
    cases v <;> simp only [evalPrintM_bm_eq]

private theorem evalPrintM_bm_fun : @evalPrintM BM _ = evalPrint := by
  funext stream args
  exact evalPrintM_bm_eq stream args

private theorem loadRawDataM_bm_eq (m : Mach) (ptr : Gen.Pointer Prov) (ptrTy : Gen.PtrType) :
    loadRawDataM (M := BM) m ptr ptrTy = loadRawData m ptr ptrTy := by
  unfold loadRawDataM loadRawData
  rw [abstractByte_dataM_bm_eq]
  rfl

private theorem loadRawDataM_bm_fun : @loadRawDataM BM _ _ = loadRawData := by
  funext m ptr ptrTy
  exact loadRawDataM_bm_eq m ptr ptrTy

private theorem activeThreadM_bm_eq (m : Mach) : activeThreadM (M := BM) m = activeThread m :=
  rfl

private theorem evalIntrinsicM_bm_eq_rawEq (m : Mach) (args : List (Val × Gen.«Type»))
    (retTy : Gen.«Type») :
    evalIntrinsicM (M := BM) m .RawEq args retTy = evalIntrinsic m .RawEq args retTy := by
  simp only [evalIntrinsicM, evalIntrinsic, loadRawDataM_bm_fun]
  rcases args with _ | ⟨⟨lV, lT⟩, _ | ⟨⟨rV, rT⟩, _ | ⟨_, _⟩⟩⟩ <;> try rfl
  cases retTy with
  | Bool =>
    dsimp only
    by_cases hte : typeEq lT rT = true
    · simp only [hte, Bool.not_true]
      rcases lV with _ | _ | lp | _ | _ <;> try rfl
      rcases rV with _ | _ | rp | _ | _ <;> try rfl
    · simp only [Bool.not_eq_true] at hte
      simp only [hte, Bool.not_false]
      rfl
  | _ => rfl

private theorem evalIntrinsicM_bm_eq_allocate (m : Mach) (args : List (Val × Gen.«Type»))
    (retTy : Gen.«Type») :
    evalIntrinsicM (M := BM) m .Allocate args retTy = evalIntrinsic m .Allocate args retTy := by
  simp only [evalIntrinsicM, evalIntrinsic, cm_allocate_bm_fun]
  rcases args with _ | ⟨⟨sizeV, sT⟩, _ | ⟨⟨alignV, aT⟩, _ | ⟨_, _⟩⟩⟩ <;> try rfl
  cases sizeV with
  | Int size =>
    rcases hs : sizeFromBytes size with _ | sz <;> simp only [hs]
    cases alignV with
    | Int align =>
      rcases ha : alignFromBytesInt align with _ | al <;> simp only [ha]
      cases retTy with
      | Ptr retPtrTy => by_cases hk : PtrType.meta_kind retPtrTy = .None <;> simp [hk] <;> rfl
      | _ => rfl
    | _ => rfl
  | _ => rfl

private theorem evalIntrinsicM_bm_eq_deallocate (m : Mach) (args : List (Val × Gen.«Type»))
    (retTy : Gen.«Type») :
    evalIntrinsicM (M := BM) m .Deallocate args retTy =
      evalIntrinsic m .Deallocate args retTy := by
  simp only [evalIntrinsicM, evalIntrinsic, cm_deallocate_bm_fun]
  rcases args with _ | ⟨⟨ptrV, pT⟩, _ | ⟨⟨sizeV, sT⟩, _ | ⟨⟨alignV, aT⟩, _ | ⟨_, _⟩⟩⟩⟩ <;>
    try rfl
  rcases ptrV with _ | _ | ⟨ptr, _ | _⟩ | _ | _ <;> try rfl
  cases sizeV with
  | Int size =>
    rcases hs : sizeFromBytes size with _ | sz <;> simp only [hs]
    cases alignV with
    | Int align =>
      rcases ha : alignFromBytesInt align with _ | al <;> simp only [ha]
      split <;> rfl
    | _ => rfl
  | _ => rfl

private theorem evalIntrinsicM_bm_eq_assume (m : Mach) (args : List (Val × Gen.«Type»))
    (retTy : Gen.«Type») :
    evalIntrinsicM (M := BM) m .Assume args retTy = evalIntrinsic m .Assume args retTy := by
  simp only [evalIntrinsicM, evalIntrinsic]
  rcases args with _ | ⟨⟨v, vT⟩, _ | ⟨_, _⟩⟩ <;> try rfl
  cases v with
  | Bool b =>
    dsimp only
    split <;> rfl
  | _ => rfl

private theorem evalIntrinsicM_bm_eq_getUnwindPayload (m : Mach)
    (args : List (Val × Gen.«Type»)) (retTy : Gen.«Type») :
    evalIntrinsicM (M := BM) m .GetUnwindPayload args retTy =
      evalIntrinsic m .GetUnwindPayload args retTy := by
  simp only [evalIntrinsicM, evalIntrinsic]
  split
  · rfl
  · cases retTy with
    | Ptr retPtrTy =>
      by_cases hk : PtrType.meta_kind retPtrTy = .None
      · simp only [hk, ite_true, activeThreadM_bm_eq]
        congr 1
        funext t
        rcases h : t.unwind_payloads.getLast? with _ | tp <;> rfl
      · simp [hk]
    | _ => rfl

private theorem exposeM_bm_eq (ipc : Gen.IntPtrCast Prov) (ptr : Ptr) :
    IntPtrCast.exposeM ipc ptr = IntPtrCast.expose ipc ptr := by
  unfold IntPtrCast.exposeM IntPtrCast.expose
  cases ptr.provenance <;> rfl

private theorem int2ptrProvenanceM_bm_eq (m : Mach) (addr : Int) :
    int2ptrProvenanceM (M := BM) m addr = int2ptrProvenance m addr := by
  unfold int2ptrProvenanceM int2ptrProvenance
  rcases m.intptrcast.exposed.elems with _ | ⟨_, _ | _⟩
  · rfl
  · rfl
  · dsimp only [MemoryOps.exposedInBounds, instMemoryOpsBM]
    rcases int2ptrCandidates m.mem.memory.allocations m.intptrcast.exposed addr with _ | ⟨_, _ | _⟩ <;> rfl

private theorem int2ptrM_bm_eq (m : Mach) (addr : Int) :
    IntPtrCast.int2ptrM (M := BM) m addr = IntPtrCast.int2ptr m addr := by
  unfold IntPtrCast.int2ptrM IntPtrCast.int2ptr
  rw [int2ptrProvenanceM_bm_eq]
  cases int2ptrProvenance m addr <;> rfl

private theorem evalIntrinsicM_bm_eq (m : Mach) (intrinsic : Gen.IntrinsicOp)
    (arguments : List (Val × Gen.«Type»)) (retTy : Gen.«Type») :
    evalIntrinsicM (M := BM) m intrinsic arguments retTy =
      evalIntrinsic m intrinsic arguments retTy := by
  unfold evalIntrinsicM evalIntrinsic
  cases intrinsic with
  | PointerExposeProvenance =>
    dsimp only
    split
    · rfl
    · rename_i hlen
      rcases arguments with _ | ⟨⟨v, _⟩, _ | ⟨_, _⟩⟩
      · simp at hlen
      · cases v with
        | Ptr p =>
          rcases p with ⟨ptr, _ | _⟩
          · cases retTy with
            | Int it =>
              rcases it with ⟨_ | _, ⟨sz⟩⟩
              · by_cases hsz : sz = 8
                · subst hsz; dsimp only; rw [exposeM_bm_eq]
                · simp [hsz]
              · rfl
            | _ => rfl
          · rfl
        | _ => rfl
      · simp at hlen
  | PointerWithExposedProvenance =>
    dsimp only
    split
    · rfl
    · rename_i hlen
      rcases arguments with _ | ⟨⟨v, _⟩, _ | ⟨_, _⟩⟩
      · simp at hlen
      · cases v with
        | Int addr =>
          cases retTy with
          | Ptr retPtrTy =>
            dsimp only
            split
            · rfl
            · exact bind_congr (int2ptrM_bm_eq m addr) (fun _ => rfl)
          | _ => rfl
        | _ => rfl
      · simp at hlen
  | PrintStdout =>
    simp only [evalPrintM_bm_fun]
    split <;> rfl
  | PrintStderr =>
    simp only [evalPrintM_bm_fun]
    split <;> rfl
  | RawEq => exact evalIntrinsicM_bm_eq_rawEq m arguments retTy
  | Allocate => exact evalIntrinsicM_bm_eq_allocate m arguments retTy
  | Deallocate => exact evalIntrinsicM_bm_eq_deallocate m arguments retTy
  | Exit => exact machineExitM_bm_eq m
  | Assume => exact evalIntrinsicM_bm_eq_assume m arguments retTy
  | GetUnwindPayload => exact evalIntrinsicM_bm_eq_getUnwindPayload m arguments retTy
  | AtomicStore =>
    have hS : @typedStoreM BM _ _ = typedStore := by
      funext m ptr val ty align atomicity
      exact typedStoreM_bm_eq m ptr val ty align atomicity
    simp only [hS]
    rcases arguments with _ | ⟨⟨ptrV, _⟩, _ | ⟨⟨val, ty⟩, _ | ⟨_, _⟩⟩⟩ <;> try rfl
    rcases ptrV with _ | _ | ⟨ptr, _ | _⟩ | _ | _ <;> rfl
  | AtomicLoad =>
    have hL : @typedLoadM BM _ _ = typedLoad := by
      funext m ptr ty align atomicity
      exact typedLoadM_bm_eq m ptr ty align atomicity
    simp only [hL]
    rcases arguments with _ | ⟨⟨ptrV, _⟩, _ | ⟨_, _⟩⟩ <;> try rfl
    rcases ptrV with _ | _ | ⟨ptr, _ | _⟩ | _ | _ <;> rfl
  | AtomicCompareExchange =>
    have hL : @typedLoadM BM _ _ = typedLoad := by
      funext m ptr ty align atomicity
      exact typedLoadM_bm_eq m ptr ty align atomicity
    have hS : @typedStoreM BM _ _ = typedStore := by
      funext m ptr val ty align atomicity
      exact typedStoreM_bm_eq m ptr val ty align atomicity
    simp only [hL, hS]
    rcases arguments with
      _ | ⟨⟨ptrV, _⟩, _ | ⟨⟨current, currTy⟩, _ | ⟨⟨next, nextTy⟩, _ | ⟨_, _⟩⟩⟩⟩ <;> try rfl
    rcases ptrV with _ | _ | ⟨ptr, _ | _⟩ | _ | _ <;> rfl
  | AtomicFetchAndOp binOp =>
    have hL : @typedLoadM BM _ _ = typedLoad := by
      funext m ptr ty align atomicity
      exact typedLoadM_bm_eq m ptr ty align atomicity
    have hS : @typedStoreM BM _ _ = typedStore := by
      funext m ptr val ty align atomicity
      exact typedStoreM_bm_eq m ptr val ty align atomicity
    simp only [hL, hS]
    rcases arguments with _ | ⟨⟨ptrV, _⟩, _ | ⟨⟨other, otherTy⟩, _ | ⟨_, _⟩⟩⟩ <;> try rfl
    rcases ptrV with _ | _ | ⟨ptr, _ | _⟩ | _ | _ <;> try rfl
    rcases other with _ | _ | _ | _ | _ | _ <;> try rfl
    dsimp only
    split
    · rfl
    · cases retTy <;> try rfl
      refine bind_congr_right _ (fun _ => ?_)
      refine bind_congr_right _ (fun _ => ?_)
      split <;> try rfl
      split <;> try rfl
      refine bind_congr_right _ (fun x => ?_)
      rcases x with ⟨previous, m1⟩
      cases previous <;> rfl
  | _ => rfl

private theorem terminateActiveThreadM_bm_eq (m : Mach) :
    terminateActiveThreadM (M := BM) m = terminateActiveThread m := by
  unfold terminateActiveThreadM terminateActiveThread activeThreadM activeThread
  dsimp only
  split
  · rfl
  · refine bind_congr_right _ (fun t => ?_)
    split
    · rfl
    · refine bind_congr_right _ (fun threads => ?_)
      let q : Nat → Bool := fun i =>
        (threads[i]?.map (fun th => decide (th.state = .BlockedOnJoin m.active_thread))).getD false
      conv =>
        lhs
        rw [filter_eq_of_eq (q := q) (by intro i; dsimp only [q]; cases threads[i]? <;> rfl)]
        rw [map_eq_of_eq
          (g := fun p : Gen.Thread BM × Nat =>
            if ((List.range threads.length).filter q).contains p.2 then
              { p.1 with state := .Enabled }
            else p.1)
          (by intro ⟨_, _⟩; rfl)]
      conv =>
        rhs
        rw [filter_eq_of_eq (q := q) (by intro i; dsimp only [q]; cases threads[i]? <;> rfl)]
        rw [map_eq_of_eq
          (g := fun p : Gen.Thread BM × Nat =>
            if ((List.range threads.length).filter q).contains p.2 then
              { p.1 with state := .Enabled }
            else p.1)
          (by intro ⟨_, _⟩; rfl)]

private theorem evalReturnM_bm_eq (m : Mach) :
    evalReturnM (M := BM) m = evalReturn m := by
  unfold evalReturnM evalReturn activeThreadM activeThread
  cases listIndex m.threads m.active_thread "self.threads[self.active_thread]" with
  | error _ => rfl
  | ok t =>
    dsimp only [bind, Except.bind]
    cases t.stack.getLast? with
    | none => rfl
    | some frame =>
      dsimp only [pure, Except.pure, bind, Except.bind]
      cases listSet m.threads m.active_thread { t with stack := t.stack.dropLast } "pop" with
      | error _ => rfl
      | ok threads =>
        dsimp only [bind, Except.bind]
        cases mapIndex frame.func.locals frame.func.ret "frame.func.locals[frame.func.ret]" with
        | error _ => rfl
        | ok calleeTy =>
          dsimp only [bind, Except.bind]
          cases Type.layout calleeTy with
          | error _ => rfl
          | ok lay =>
            dsimp only [bind, Except.bind]
            cases LayoutStrategy.expect_align lay "the return value is a local and thus sized" with
            | error _ => rfl
            | ok align =>
              dsimp only [bind, Except.bind]
              cases mapIndex frame.locals frame.func.ret "frame.locals[frame.func.ret]" with
              | error _ => rfl
              | ok retPtr =>
                dsimp only [bind, Except.bind]
                rw [typedLoadM_bm_eq]
                rcases typedLoad { m with threads := threads } retPtr calleeTy align .None with
                  _ | ⟨retVal, m1⟩
                · rfl
                · dsimp only [bind, Except.bind]
                  rw [deallocAllM_bm_eq]
                  rcases deallocAll frame.locals.entries.length frame m1.mem with _ | ⟨fr2, cm2⟩
                  · rfl
                  · have hend : ConcurrentMemory.end_call (M := BM) cm2 fr2.extra = .ok cm2 := rfl
                    dsimp only [bind, Except.bind]
                    rw [hend]
                    dsimp only
                    cases fr2.stack_pop_action with
                    | BottomOfStack => exact terminateActiveThreadM_bm_eq { m1 with mem := cm2 }
                    | BackToCaller nextBlock _ callerRetPtr =>
                      dsimp only
                      cases listIndex m1.threads m1.active_thread "self.threads[self.active_thread]" with
                      | error _ => rfl
                      | ok t2 =>
                        dsimp only [bind, Except.bind]
                        split
                        · rfl
                        · rw [typedStoreM_bm_eq]
                          cases typedStore { m1 with mem := cm2 } callerRetPtr retVal calleeTy align .None with
                          | error _ => rfl
                          | ok m2 =>
                            dsimp only [bind, Except.bind]
                            cases nextBlock with
                            | none => rfl
                            | some nb => exact jumpToBlockM_bm_eq m2 nb

private theorem mutateActiveThreadM_bm_eq {α : Type} (m : Mach)
    (f : Gen.Thread BM → Interp (α × Gen.Thread BM)) :
    mutateActiveThreadM (M := BM) m f = mutateActiveThread m f := rfl

private theorem evalResumeUnwindM_bm_eq (m : Mach) :
    evalResumeUnwindM (M := BM) m = evalResumeUnwind m := by
  unfold evalResumeUnwindM evalResumeUnwind activeThreadM activeThread
  cases listIndex m.threads m.active_thread "self.threads[self.active_thread]" with
  | error _ => rfl
  | ok t =>
    dsimp only [bind, Except.bind]
    cases t.stack.getLast? with
    | none => rfl
    | some frame =>
      dsimp only [pure, Except.pure, bind, Except.bind]
      cases listSet m.threads m.active_thread { t with stack := t.stack.dropLast } "pop" with
      | error _ => rfl
      | ok threads =>
        dsimp only [bind, Except.bind]
        rw [deallocAllM_bm_eq]
        rcases deallocAll frame.locals.entries.length frame m.mem with _ | ⟨fr2, cm2⟩
        · rfl
        · have hend : ConcurrentMemory.end_call (M := BM) cm2 fr2.extra = .ok cm2 := rfl
          dsimp only [bind, Except.bind]
          rw [hend]
          dsimp only
          cases fr2.stack_pop_action with
          | BottomOfStack => rfl
          | BackToCaller _ unwindBlock _ =>
            dsimp only
            cases unwindBlock with
            | none => rfl
            | some unwindBlock => exact jumpToBlockM_bm_eq _ unwindBlock

theorem evalTerminatorM_bm_eq (m : Mach) (term : Gen.Terminator) :
    evalTerminatorM (M := BM) m term = evalTerminator m term := by
  cases term with
  | Goto nb => exact jumpToBlockM_bm_eq m nb
  | Switch value cases fallback =>
    unfold evalTerminatorM Interp.evalTerminator
    refine bind_congr (evalValueM_bm_eq m value) (fun ⟨⟨v, _⟩, m1⟩ => ?_)
    dsimp only
    cases v with
    | Int i => exact jumpToBlockM_bm_eq m1 ((mapGet cases i).getD fallback)
    | _ => rfl
  | Unreachable => rfl
  | Call callee conv arguments retExpr nextBlock unwindBlock =>
    unfold evalTerminatorM Interp.evalTerminator
    refine bind_congr (evalPlaceM_bm_eq m retExpr) (fun ⟨⟨retPlace, retTy⟩, m1⟩ => ?_)
    dsimp only
    refine bind_congr (prepareForInplacePassingM_bm_eq m1 retPlace retTy) (fun m2 => ?_)
    refine bind_congr (evalValueM_bm_eq m2 callee) (fun ⟨⟨calleeVal, _⟩, m3⟩ => ?_)
    dsimp only
    refine bind_congr (fnFromPtrM_bm_eq m3 calleeVal) (fun calleeFn => ?_)
    refine bind_congr (evalArgumentsM_bm_eq m3 arguments) (fun ⟨args, m4⟩ => ?_)
    exact evalCallM_bm_eq m4 calleeFn conv args (retPlace, retTy) nextBlock unwindBlock
  | Return => exact evalReturnM_bm_eq m
  | Intrinsic intrinsic arguments retExpr nextBlock =>
    unfold evalTerminatorM Interp.evalTerminator
    refine bind_congr (evalPlaceM_bm_eq m retExpr) (fun ⟨⟨retPlace, retTy⟩, m1⟩ => ?_)
    dsimp only
    refine bind_congr (evalArgsM_bm_eq m1 arguments) (fun ⟨args, m2⟩ => ?_)
    dsimp only
    refine bind_congr (evalIntrinsicM_bm_eq m2 intrinsic args retTy) (fun ⟨val, m3⟩ => ?_)
    dsimp only
    refine bind_congr (placeStoreM_bm_eq m3 retPlace val retTy) (fun m4 => ?_)
    cases nextBlock with
    | none => rfl
    | some nb => exact jumpToBlockM_bm_eq m4 nb
  | StartUnwind payload blk =>
    unfold evalTerminatorM Interp.evalTerminator
    refine bind_congr (evalValueM_bm_eq m payload) (fun ⟨⟨v, ty⟩, m1⟩ => ?_)
    dsimp only
    split
    · exact bind_congr (mutateActiveThreadM_bm_eq m1 _)
        (fun ⟨_, m2⟩ => jumpToBlockM_bm_eq m2 blk)
    · split
      · rename_i hne
        exact (hne _ rfl rfl).elim
      · rfl
  | StopUnwind blk =>
    unfold evalTerminatorM Interp.evalTerminator
    refine bind_congr ?_ (fun ⟨_, m1⟩ => jumpToBlockM_bm_eq m1 blk)
    rw [mutateActiveThreadM_bm_eq]
    congr 1
    funext thread
    cases thread.unwind_payloads.getLast? <;> rfl
  | ResumeUnwind => exact evalResumeUnwindM_bm_eq m

private theorem pickActiveThreadM_bm_eq (m : Mach) :
    pickActiveThreadM (M := BM) m = pickActiveThread m := by
  unfold pickActiveThreadM pickActiveThread
  let q : Nat → Bool := fun i =>
    (m.threads[i]?.map (fun t => decide (t.state = .Enabled))).getD false
  conv =>
    lhs
    rw [filter_eq_of_eq (q := q) (by intro i; dsimp only [q]; cases m.threads[i]? <;> rfl)]
  conv =>
    rhs
    rw [filter_eq_of_eq (q := q) (by intro i; dsimp only [q]; cases m.threads[i]? <;> rfl)]

/-- Unconditional single-step specialization identity: polymorphic `stepM`
instantiated at `M = BM` (`BasicMemory<x86_64>`) is extensionally identical to
`Interp.step` on every machine state `m : Mach`. -/
theorem stepM_bm_eq (m : Mach) : stepM (M := BM) m = step m := by
  unfold stepM step
  split
  · rfl
  · have hrst : resetDataRaceTrackingM (M := BM) m = resetDataRaceTracking m := rfl
    rcases hrst_val : resetDataRaceTracking m with ⟨prev, m1⟩
    rw [hrst, hrst_val]
    dsimp only
    rw [pickActiveThreadM_bm_eq]
    cases pickActiveThread m1 with
    | error _ => rfl
    | ok tid =>
      dsimp only [bind, Except.bind]
      rw [curFrameM_bm_eq]
      cases curFrame { m1 with active_thread := tid } with
      | error _ => rfl
      | ok frame =>
        dsimp only [bind, Except.bind]
        cases mapIndex frame.func.blocks frame.next_block "frame.func.blocks[frame.next_block]" with
        | error _ => rfl
        | ok block =>
          dsimp only [bind, Except.bind]
          split
          · rw [evalTerminatorM_bm_eq]
            cases evalTerminator { m1 with active_thread := tid } block.terminator with
            | error _ => rfl
            | ok m2 =>
              dsimp only [bind, Except.bind]
              rw [cm_check_data_races_bm_eq]
          · cases listIndex block.statements frame.next_stmt "block.statements[frame.next_stmt]" with
            | error _ => rfl
            | ok stmt =>
              dsimp only [bind, Except.bind]
              rw [evalStatementM_bm_eq]
              cases evalStatement { m1 with active_thread := tid } stmt with
              | error _ => rfl
              | ok m2 =>
                dsimp only [bind, Except.bind]
                rw [mutateCurFrameM_bm_eq]
                cases mutateCurFrame m2 (fun fr => { fr with next_stmt := fr.next_stmt + 1 }) with
                | error _ => rfl
                | ok m3 =>
                  dsimp only [bind, Except.bind]
                  rw [cm_check_data_races_bm_eq]

/-- Unconditional `n`-step specialization identity: polymorphic `stepsM`
instantiated at `M = BM` equals `Interp.steps` for every `n : Nat` and `m : Mach`,
immediately lifting every `BasicMemory` correspondence theorem (`mirCall_ret`,
`mirCall_ub`, `mirCall_noUB`, `mirCall_progress_N`, `mirCall_steps_error`,
`mirCall_outcome_N`) to `stepsM (M := BM)`. -/
theorem stepsM_bm_eq : ∀ (n : Nat) (m : Mach), stepsM (M := BM) n m = steps n m
  | 0, _ => rfl
  | n + 1, m => by
    unfold stepsM steps
    rw [stepM_bm_eq m]
    cases step m with
    | error _ => rfl
    | ok m' => exact stepsM_bm_eq n m'

end MiniRustSpec.Correspondence
