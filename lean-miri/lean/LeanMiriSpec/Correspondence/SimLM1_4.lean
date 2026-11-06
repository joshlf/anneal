import LeanMiriSpec.Correspondence.Relation
import LeanMiriSpec.Correspondence.Translate

namespace LeanMiriSpec.Correspondence

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

theorem split_bind {α β σ E} {x : EStateM E σ α} {f : α → EStateM E σ β} {m m' : σ} {b : β}
  (h : EStateM.bind x f m = EStateM.Result.ok b m') : ∃ a m1, x m = EStateM.Result.ok a m1 ∧ f a m1 = EStateM.Result.ok b m' := by
  cases hx : x m with
  | error e m1 => rw [EStateM.bind, hx] at h; contradiction
  | ok a m1 => rw [EStateM.bind, hx] at h; exact ⟨a, m1, rfl, h⟩



theorem translateBody_basicBlocks_getElem? (body : CapturedMir) (i : Nat) :
    (translateBody body).basicBlocks[i]? =
      (get? body.basicBlocks i).map translateBasicBlockData := by
  simp [translateBody, get?]

theorem translateBasicBlockData_statements_getElem? (bb : BasicBlockData) (i : Nat) :
    (translateBasicBlockData bb).statements[i]? =
      (get? bb.statements i).map translateStmt := by
  simp [translateBasicBlockData, get?]

theorem array_set_self {α : Type} (arr : Array α) (idx : Nat) (hlt : idx < arr.size) :
    arr.set idx (arr[idx]'hlt) hlt = arr := by
  apply Array.ext
  · simp
  · intro i _ hi₂
    rw [Array.getElem_set]
    by_cases h : idx = i
    · subst h; simp
    · simp [h]

theorem annealLocalStorageHooks_veryTriviallySized
    (localDecls : List LocalDecl) (layouts : LayoutTable) (ty : Miri.MIR.TyId) :
    (annealLocalStorageHooks localDecls layouts).veryTriviallySized ty = .ok true := rfl

theorem annealLocalStorageHooks_afterLocalWrite
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (st : AnnealMemory) (l : Nat) (b : Bool) :
    (annealLocalStorageHooks localDecls layouts).afterLocalWrite st l b = ⟨st, .ok ()⟩ := rfl

theorem stack_currentFrame?_singleton
    {P L E : Type} (s : Miri.Interpreter.Stack P L E)
    (f : Miri.Interpreter.Frame P L E) (h : s.frames = #[f]) :
    s.currentFrame? = some f := by
  unfold Miri.Interpreter.Stack.currentFrame?
  rw [h]; rfl

theorem stepState_with_same_singleton
    (m : AnnealStepState)
    (f : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    (h : m.stack.frames = #[f]) :
    { m with stack := ⟨#[f]⟩ } = m := by
  rcases m with ⟨⟨frames⟩, machine⟩
  dsimp only at h
  subst h
  rfl

theorem frame_getLocal_of_getElem?
    {P L E : Type} (mf : Miri.Interpreter.Frame P L E) (i : Nat) (mls : Miri.Interpreter.LocalState P L)
    (h : mf.locals[i]? = some mls) :
    mf.getLocal i = .ok mls := by
  obtain ⟨hlt, heq⟩ := Array.getElem?_eq_some_iff.mp h
  unfold Miri.Interpreter.Frame.getLocal
  simp [hlt, heq, pure, Except.pure]

theorem frame_replaceLocalValue_of_lt
    {P L E : Type} (mf : Miri.Interpreter.Frame P L E) (i : Nat)
    (hlt : i < mf.locals.size) (val : Miri.Interpreter.LocalValue P) :
    mf.replaceLocalValue i val =
      .ok { mf with locals := mf.locals.set i { mf.locals[i] with value := val } hlt } := by
  unfold Miri.Interpreter.Frame.replaceLocalValue
  simp [hlt, pure, Except.pure]

theorem stepMirFn_eq_of_not_other (body : CapturedMir) (s : MachineState)
    (hcal : s.memory.activeCallee = none)
    (hphase : ∀ p, body.phase ≠ .other p) :
    stepMirFn body s =
      match get? body.basicBlocks s.frame.blockIdx with
      | none => MirStepNode.fail .ub
      | some bb =>
        match get? bb.statements s.frame.stmtIdx with
        | some stmt => evalStmt s stmt body.localDecls body.layouts
        | none =>
          if s.frame.stmtIdx == length bb.statements then
            evalTerminator s bb.terminator (some body)
          else
            MirStepNode.fail .ub := by
  unfold stepMirFn
  rw [hcal]
  dsimp only [Option.getD]
  cases hp : body.phase with
  | other p => exact False.elim (hphase p hp)
  | _ => rfl


def cacheFrameLocalLayout
    (mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    (idx : Nat) (hlt : idx < mf.locals.size)
    (lay : Miri.Interpreter.LocalLayout) :
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { mf with locals := mf.locals.set idx { mf.locals[idx]'hlt with layout := some lay } hlt }


theorem frame_getOrCacheLocalLayout_eq
    (topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    {idx : Nat} (hlt : idx < topFrame.locals.size)
    {computed : Miri.Interpreter.LocalLayout}
    (hcache : ∀ l, (topFrame.locals[idx]'hlt).layout = some l → l = computed) :
    topFrame.getOrCacheLocalLayout idx computed =
      .ok (cacheFrameLocalLayout topFrame idx hlt computed, computed) := by
  unfold Miri.Interpreter.Frame.getOrCacheLocalLayout Miri.Interpreter.Frame.getLocal
    cacheFrameLocalLayout
  simp only [hlt, ↓reduceDIte, bind, Except.bind, pure, Except.pure]
  cases hc : (topFrame.locals[idx]'hlt).layout with
  | none => rfl
  | some cached =>
    have h_eq := hcache cached hc
    subst h_eq
    have hls_eq : { topFrame.locals[idx]'hlt with layout := some cached } =
        topFrame.locals[idx]'hlt := by
      cases hls : topFrame.locals[idx]'hlt
      rw [hls] at hc
      dsimp only at hc
      subst hc
      rfl
    rw [hls_eq, array_set_self]


theorem translateBody_locals_getElem? (body : CapturedMir) (i : Nat) :
    (translateBody body).locals[i]? = (get? body.localDecls i).map (fun d => encodeTyId d.ty) := by
  simp [translateBody, get?]


theorem get?_eq_getElem? {α : Type u} (xs : List α) (i : Nat) :
    get? xs i = xs[i]? := rfl

@[simp]
theorem length_eq_length {α : Type u} (xs : List α) :
    length xs = xs.length := rfl

theorem set?_eq_some_set {α : Type u} {xs : List α} {i : Nat} (hlt : i < xs.length) (v : α) :
    set? xs i v = some (xs.set i v) := by
  unfold set?
  simp [hlt]


theorem cacheFrameLocalLayout_getLocal
    (mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    {idx : Nat} (hlt : idx < mf.locals.size)
    (lay : Miri.Interpreter.LocalLayout) :
    (cacheFrameLocalLayout mf idx hlt lay).getLocal idx =
      .ok { mf.locals[idx]'hlt with layout := some lay } := by
  unfold cacheFrameLocalLayout Miri.Interpreter.Frame.getLocal
  simp [hlt, pure, Except.pure]


inductive WellTypedLM1_4Stmt (body : CapturedMir) (topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit) : Statement → Prop where
  | storageLive (loc : Local) (decl : LocalDecl) (span : String) :
      get? body.localDecls loc = some decl →
      WellTypedLM1_4Stmt body topFrame ⟨.storageLive loc, span⟩
  | storageDead (loc : Local) (decl : LocalDecl) (span : String) :
      get? body.localDecls loc = some decl →
      WellTypedLM1_4Stmt body topFrame ⟨.storageDead loc, span⟩
  | deinit (place : Place) (decl : LocalDecl) (span : String) :
      get? body.localDecls place.local_ = some decl →
      place.projection = .nil →
      WellTypedLM1_4Stmt body topFrame ⟨.deinit place, span⟩
  | placeMention (place : Place) (decl : LocalDecl) (span : String) :
      get? body.localDecls place.local_ = some decl →
      place.projection = .nil →
      WellTypedLM1_4Stmt body topFrame ⟨.placeMention place, span⟩
  | assignMove (dstIdx : Local) (dstDecl : LocalDecl) (srcPlace : Place) (srcDecl : LocalDecl) (span : String) :
      get? body.localDecls dstIdx = some dstDecl →
      get? body.localDecls srcPlace.local_ = some srcDecl →
      srcPlace.projection = .nil →
      dstDecl.ty = srcDecl.ty →
      WellTypedLM1_4Stmt body topFrame ⟨.assign ⟨dstIdx, .nil⟩ (.use (.move srcPlace)), span⟩




theorem annealLocalStorageHooks_deallocateLocal_eq
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (st : AnnealMemory)
    (v : Miri.Interpreter.LocalValue AnnealProv) :
    Miri.Interpreter.Frame.deallocateLocal (annealLocalStorageHooks localDecls layouts) st v =
      ⟨st, .ok ()⟩ := by
  unfold Miri.Interpreter.Frame.deallocateLocal
  cases v with
  | dead => rfl
  | live op =>
    cases op with
    | immediate _ => rfl
    | indirect mp => rfl

theorem annealStepHooks_storageLive_eq
    {localDecls : List LocalDecl} {layouts : LayoutTable} {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {loc : Nat} (hframes : m.stack.frames = #[topFrame])
    (hlt : loc < topFrame.locals.size)
    (hty : ∃ ty, topFrame.body.locals[loc]? = some ty) :
    (annealStepHooks localDecls layouts).storageLive () loc m =
      ({ m with
          stack := ⟨#[{ topFrame with
            locals := topFrame.locals.set loc
              { topFrame.locals[loc]'hlt with value := .live (.immediate .uninit) } hlt }]⟩ },
        .ok ()) := by
  obtain ⟨ty, hty⟩ := hty
  have hget : topFrame.getLocal loc = .ok (topFrame.locals[loc]'hlt) := by
    unfold Miri.Interpreter.Frame.getLocal
    simp [hlt, pure, Except.pure]
  simp only [annealStepHooks, annealRunFrameStorage, stack_currentFrame?_singleton m.stack topFrame hframes]
  simp only [Miri.Interpreter.Frame.storageLive, Miri.Interpreter.Frame.storageLiveDyn, hget, hty,
    annealLocalStorageHooks_veryTriviallySized, annealLocalStorageHooks_afterLocalWrite,
    Miri.Interpreter.MemPlaceMeta.hasMeta,
    frame_replaceLocalValue_of_lt topFrame loc hlt,
    annealLocalStorageHooks_deallocateLocal_eq,
    Id.run, hframes, pure_bind, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rcases m with ⟨⟨frames⟩, ⟨mem, addr, bt⟩⟩
  rfl

theorem annealStepHooks_storageDead_eq
    {localDecls : List LocalDecl} {layouts : LayoutTable} {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {loc : Nat} (hframes : m.stack.frames = #[topFrame])
    (hlt : loc < topFrame.locals.size)
    (hne : loc ≠ 0) :
    (annealStepHooks localDecls layouts).storageDead () loc m =
      ({ m with
          stack := ⟨#[{ topFrame with
            locals := topFrame.locals.set loc
              { topFrame.locals[loc]'hlt with value := .dead } hlt }]⟩ },
        .ok ()) := by
  have hget : topFrame.getLocal loc = .ok (topFrame.locals[loc]'hlt) := by
    unfold Miri.Interpreter.Frame.getLocal
    simp [hlt, pure, Except.pure]
  simp only [annealStepHooks, annealRunFrameStorage, stack_currentFrame?_singleton m.stack topFrame hframes]
  have h_beq : (loc == 0) = false := beq_false_of_ne hne
  simp only [Miri.Interpreter.Frame.storageDead, hget, frame_replaceLocalValue_of_lt topFrame loc hlt,
    annealLocalStorageHooks_deallocateLocal_eq,
    Id.run, hframes, pure_bind, h_beq, not_false_eq_true, Bool.false_eq_true, ↓reduceIte]
  rcases m with ⟨⟨frames⟩, ⟨mem, addr, bt⟩⟩
  rfl

theorem List_get_eq_some_length_storage {α} {l : List α} {i : Nat} {a : α} (h : get? l i = some a) : i < l.length := by
  induction l generalizing i with
  | nil => contradiction
  | cons x xs ih =>
    cases i
    · simp [List.length]
    · simp only [get?] at h
      have h' := ih h
      simp [List.length]
      omega



theorem List_set_eq_some_of_lt_storage {α} {l : List α} {i : Nat} (hlt : i < l.length) (v : α) :
    set? l i v = some (l.set i v) := by
  unfold set?
  simp [hlt]



theorem List_get_eq_some_of_lt_storage {α} {l : List α} {i : Nat} (hlt : i < l.length) :
    ∃ a, get? l i = some a := by
  induction l generalizing i with
  | nil => contradiction
  | cons x xs ih =>
    cases i
    · exact ⟨x, rfl⟩
    · simp only [List.length] at hlt
      have hlt' : _ < _ := Nat.lt_of_succ_lt_succ hlt
      have ⟨a, hget⟩ := ih hlt'
      simp only [get?]
      exact ⟨a, hget⟩



theorem Array_get_eq_some_of_lt_storage {α} {a : Array α} {i : Nat} (hlt : i < a.size) :
    ∃ v, a[i]? = some v := by
  exact ⟨a[i]'hlt, Array.getElem?_eq_some_iff.mpr ⟨hlt, rfl⟩⟩



theorem FrameRel_update_local_storage
    {body : CapturedMir} {mach : AnnealMachine}
    {af : StackFrame} {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hrel : FrameRel body mach af mf)
    {idx : Nat} {decl : LocalDecl}
    (hdecl : get? body.localDecls idx = some decl)
    {hlt_mf : idx < mf.locals.size}
    (newSlot : LocalSlot) (newVal : Miri.Interpreter.LocalValue AnnealProv)
    (hnew : LocalRel mach decl body.layouts newSlot { mf.locals[idx]'hlt_mf with value := newVal }) :
    FrameRel body mach
      { af with locals := af.locals.set idx newSlot }
      { mf with locals := mf.locals.set idx { mf.locals[idx]'hlt_mf with value := newVal } hlt_mf } where
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
      exact hrel.locals_rel i decl_i slot_i mls_i hdecl_i hslot_i hmls_i



theorem miri_step_at_statement_ok_storage
    {PlaceTy : Type}
    (hooks : Miri.Interpreter.StepHooks AnnealProv Miri.Interpreter.LocalLayout Unit
      AnnealMachine Unit PlaceTy)
    {body : CapturedMir} {m m' : AnnealStepState}
    {topFrame topFrame' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {blockIdx stmtIdx : Nat} {bb : BasicBlockData} {stmt : Statement}
    (hframes : m.stack.frames = #[topFrame])
    (hbody : topFrame.body = translateBody body)
    (hloc : topFrame.location = .mir ⟨blockIdx, stmtIdx⟩)
    (hbb : get? body.basicBlocks blockIdx = some bb)
    (hstmt : get? bb.statements stmtIdx = some stmt)
    (heval : Miri.Interpreter.Step.evalStatement hooks () (translateStmt stmt) m = (m', .ok ()))
    (hframes' : m'.stack.frames = #[topFrame'])
    (hloc' : topFrame'.location = .mir ⟨blockIdx, stmtIdx⟩) :
    Miri.Interpreter.Step.step hooks () m =
      ({ m' with stack := ⟨#[{ topFrame' with location := .mir ⟨blockIdx, stmtIdx + 1⟩ }]⟩ },
        .ok true) := by
  unfold Miri.Interpreter.Step.step
  rw [stack_currentFrame?_singleton m.stack topFrame hframes]
  dsimp only
  rw [hloc, hbody]
  dsimp only
  rw [translateBody_basicBlocks_getElem?, hbb]
  dsimp only [Option.map]
  rw [translateBasicBlockData_statements_getElem?, hstmt]
  dsimp only [Option.map]
  rw [heval, stack_currentFrame?_singleton m'.stack topFrame' hframes']
  dsimp only
  rw [hloc', hframes, hframes']
  rfl



theorem cachedLayout_orElse_lookupLocalDeclLayout_orElse_storage
    {body : CapturedMir}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {idx : Nat} {hlt : idx < topFrame.locals.size} {decl : LocalDecl}
    (hdecl : get? body.localDecls idx = some decl)
    (hcache : ∀ l, (topFrame.locals[idx]'hlt).layout = some l →
      l = translateTy decl.ty body.layouts) :
    (topFrame.locals[idx]'hlt).layout.getD (translateTy decl.ty body.layouts) =
      translateTy decl.ty body.layouts := by
  cases hc : (topFrame.locals[idx]'hlt).layout with
  | none => rfl
  | some l => exact hcache l hc



theorem frame_getOrCacheLocalLayout_eq_storage
    (topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    {idx : Nat} (hlt : idx < topFrame.locals.size)
    {computed : Miri.Interpreter.LocalLayout}
    (hcache : ∀ l, (topFrame.locals[idx]'hlt).layout = some l → l = computed) :
    topFrame.getOrCacheLocalLayout idx computed =
      .ok (cacheFrameLocalLayout topFrame idx hlt computed, computed) := by
  unfold Miri.Interpreter.Frame.getOrCacheLocalLayout Miri.Interpreter.Frame.getLocal
    cacheFrameLocalLayout
  simp only [hlt, ↓reduceDIte, bind, Except.bind, pure, Except.pure]
  cases hc : (topFrame.locals[idx]'hlt).layout with
  | none => rfl
  | some l =>
    have hl := hcache l hc
    subst hl
    have hset : topFrame.locals.set idx { topFrame.locals[idx]'hlt with layout := some l } hlt = topFrame.locals := by
      apply Array.ext
      · simp
      · intro i hi_new hi_old
        rw [Array.getElem_set]
        split
        · subst i
          have heq_lay : (topFrame.locals[idx]'hi_old).layout = some l := by
            have h_eq_idx : topFrame.locals[idx]'hi_old = topFrame.locals[idx]'hlt := rfl
            rw [h_eq_idx]
            exact hc
          have h_eq : { value := (topFrame.locals[idx]'hi_old).value, layout := some l } = topFrame.locals[idx]'hi_old := by
            rw [← heq_lay]
          exact h_eq
        · rfl
    rw [hset]



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
  rcases hstate with ⟨topFrame, hframes, ht_ret, ht_retp, hfr, hcal_none, ht_stack, ht_bor, ht_prot, ht_caller, hdisj⟩
  rw [stepMirFn_eq_of_not_other body s hcal_none hphase]
  simp only [hbb, hstmt]
  have hwt' := hwt topFrame hframes
  cases hwt' with
  | storageLive _ decl _ hdecl =>
    have hlt_body : loc < body.localDecls.length := List_get_eq_some_length_storage hdecl
    have hlt_af : loc < s.frame.locals.length := by
      rw [hfr.af_locals_len]
      exact hlt_body
    have hlt_mf : loc < topFrame.locals.size := by
      rw [hfr.mf_locals_size]
      exact hlt_body
    have ⟨slot, hslot⟩ := List_get_eq_some_of_lt_storage hlt_af
    have ⟨mls, hmls⟩ := Array_get_eq_some_of_lt_storage hlt_mf
    have hset_af := List_set_eq_some_of_lt_storage hlt_af LocalSlot.uninit
    have ha : evalStmt s { kind := StatementKind.storageLive loc, span := span } body.localDecls body.layouts = MirStepNode.step (advanceStmt s (s.frame.locals.set loc LocalSlot.uninit)) := by
      unfold evalStmt
      dsimp only
      rw [hslot, hset_af]
    rw [ha]
    have hm : Miri.Interpreter.Step.evalStatement (annealStepHooks body.localDecls body.layouts) () (translateStmt ⟨.storageLive loc, span⟩) m = ({ m with stack := ⟨#[{ topFrame with locals := topFrame.locals.set loc { mls with value := .live (.immediate .uninit) } hlt_mf }]⟩ }, .ok ()) := by
      have hty : ∃ ty, topFrame.body.locals[loc]? = some ty := by
        rw [hfr.body_eq, translateBody_locals_getElem? body loc, hdecl]
        exact ⟨_, rfl⟩
      have h_getElem? := Array.getElem?_eq_getElem hlt_mf
      have heq_mls : topFrame.locals[loc]'hlt_mf = mls := by
        rw [h_getElem?] at hmls
        exact Option.some.inj hmls
      simp only [Miri.Interpreter.Step.evalStatement, translateStmt, translateStmtKind]
      have hlive := @annealStepHooks_storageLive_eq body.localDecls body.layouts m topFrame loc hframes hlt_mf hty
      rw [heq_mls] at hlive
      exact hlive
    rw [miri_step_at_statement_ok_storage (annealStepHooks body.localDecls body.layouts) hframes hfr.body_eq hfr.location_eq hbb hstmt hm rfl hfr.location_eq]
    apply StepRel.step
    have hfr_new : FrameRel body m.machine (advanceStmt s (s.frame.locals.set loc LocalSlot.uninit)).frame { topFrame with locals := topFrame.locals.set loc { mls with value := .live (.immediate .uninit) } hlt_mf, location := .mir ⟨s.frame.blockIdx, s.frame.stmtIdx + 1⟩ } := by
      refine ⟨hfr.body_eq, rfl, ?_, ?_, ?_⟩
      · dsimp only [advanceStmt]; rw [List.length_set, hfr.af_locals_len]
      · rw [Array.size_set, hfr.mf_locals_size]
      · intro i decl_i slot_i mls_i hdecl_i hslot_i hmls_i
        dsimp only [advanceStmt] at hslot_i
        dsimp only at hslot_i hmls_i
        rw [get?_eq_getElem?, List.getElem?_set] at hslot_i
        rw [Array.getElem?_set] at hmls_i
        by_cases heq : loc = i
        · subst heq
          simp only [hlt_af, ↓reduceIte, Option.some.injEq] at hslot_i hmls_i
          have hdecl_eq : decl_i = decl := by
            rw [hdecl] at hdecl_i; exact Option.some.inj hdecl_i.symm
          subst hdecl_eq hslot_i hmls_i
          apply LocalRel.immediate
          · intro lay hlay
            have hrel_old := hfr.locals_rel loc _ slot mls hdecl hslot hmls
            exact LocalRel.cachedLayout_eq hrel_old lay hlay
          · exact Or.inl ⟨rfl, rfl⟩
        · simp only [heq, ↓reduceIte] at hslot_i hmls_i
          exact hfr.locals_rel i decl_i slot_i mls_i hdecl_i hslot_i hmls_i
    exact StateRel.mk _ rfl ht_ret ht_retp hfr_new hcal_none ht_stack ht_bor ht_prot ht_caller (by
      apply MemoryAllocDisjoint.mono_immediate hdisj
      intro k
      by_cases hk : loc = k
      · subst hk
        right
        exact ⟨.uninit, mls.layout, by simp only [Array.getElem?_set, ↓reduceIte]⟩
      · left
        simp only [hk, Array.getElem?_set, ↓reduceIte]
    )




theorem step_storageDead_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRel body s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {loc : Local} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.storageDead loc, span⟩)
    (hwt : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedLM1_4Stmt body topFrame ⟨.storageDead loc, span⟩)
    (hne : loc ≠ 0) :
    StepRel body m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  rcases hstate with ⟨topFrame, hframes, ht_ret, ht_retp, hfr, hcal_none, ht_stack, ht_bor, ht_prot, ht_caller, hdisj⟩
  rw [stepMirFn_eq_of_not_other body s hcal_none hphase]
  simp only [hbb, hstmt]
  have hwt' := hwt topFrame hframes
  cases hwt' with
  | storageDead _ decl _ hdecl =>
    have hlt_body : loc < body.localDecls.length := List_get_eq_some_length_storage hdecl
    have hlt_af : loc < s.frame.locals.length := by
      rw [hfr.af_locals_len]
      exact hlt_body
    have hlt_mf : loc < topFrame.locals.size := by
      rw [hfr.mf_locals_size]
      exact hlt_body
    have ⟨slot, hslot⟩ := List_get_eq_some_of_lt_storage hlt_af
    have ⟨mls, hmls⟩ := Array_get_eq_some_of_lt_storage hlt_mf
    have hset_af := List_set_eq_some_of_lt_storage hlt_af LocalSlot.dead
    have ha : evalStmt s { kind := StatementKind.storageDead loc, span := span } body.localDecls body.layouts = MirStepNode.step (advanceStmt s (s.frame.locals.set loc LocalSlot.dead)) := by
      unfold evalStmt
      dsimp only
      rw [hslot, hset_af]
    rw [ha]
    have hm : Miri.Interpreter.Step.evalStatement (annealStepHooks body.localDecls body.layouts) () (translateStmt ⟨.storageDead loc, span⟩) m = ({ m with stack := ⟨#[{ topFrame with locals := topFrame.locals.set loc { mls with value := .dead } hlt_mf }]⟩ }, .ok ()) := by
      have h_getElem? := Array.getElem?_eq_getElem hlt_mf
      have heq_mls : topFrame.locals[loc]'hlt_mf = mls := by
        rw [h_getElem?] at hmls
        exact Option.some.inj hmls
      simp only [Miri.Interpreter.Step.evalStatement, translateStmt, translateStmtKind]
      have hdead := @annealStepHooks_storageDead_eq body.localDecls body.layouts m topFrame loc hframes hlt_mf hne
      rw [heq_mls] at hdead
      exact hdead
    rw [miri_step_at_statement_ok_storage (annealStepHooks body.localDecls body.layouts) hframes hfr.body_eq hfr.location_eq hbb hstmt hm rfl hfr.location_eq]
    apply StepRel.step
    have hfr_new : FrameRel body m.machine (advanceStmt s (s.frame.locals.set loc LocalSlot.dead)).frame { topFrame with locals := topFrame.locals.set loc { mls with value := .dead } hlt_mf, location := .mir ⟨s.frame.blockIdx, s.frame.stmtIdx + 1⟩ } := by
      refine ⟨hfr.body_eq, rfl, ?_, ?_, ?_⟩
      · dsimp only [advanceStmt]; rw [List.length_set, hfr.af_locals_len]
      · rw [Array.size_set, hfr.mf_locals_size]
      · intro i decl_i slot_i mls_i hdecl_i hslot_i hmls_i
        dsimp only [advanceStmt] at hslot_i
        dsimp only at hslot_i hmls_i
        rw [get?_eq_getElem?, List.getElem?_set] at hslot_i
        rw [Array.getElem?_set] at hmls_i
        by_cases heq : loc = i
        · subst heq
          simp only [hlt_af, ↓reduceIte, Option.some.injEq] at hslot_i hmls_i
          have hdecl_eq : decl_i = decl := by
            rw [hdecl] at hdecl_i; exact Option.some.inj hdecl_i.symm
          subst hdecl_eq hslot_i hmls_i
          apply LocalRel.dead
          intro lay hlay
          have hrel_old := hfr.locals_rel loc _ slot mls hdecl hslot hmls
          exact LocalRel.cachedLayout_eq hrel_old lay hlay
        · simp only [heq, ↓reduceIte] at hslot_i hmls_i
          exact hfr.locals_rel i decl_i slot_i mls_i hdecl_i hslot_i hmls_i
    exact StateRel.mk _ rfl ht_ret ht_retp hfr_new hcal_none ht_stack ht_bor ht_prot ht_caller (by
      apply MemoryAllocDisjoint.mono_dead hdisj
      intro k
      by_cases hk : loc = k
      · subst hk
        right
        exact ⟨mls.layout, by simp only [Array.getElem?_set, ↓reduceIte]⟩
      · left
        simp only [hk, Array.getElem?_set, ↓reduceIte]
    )


theorem size_singleton_sub_one {α} (x : α) : #[x].size - 1 < #[x].size := by
  have : #[x].size = 1 := rfl
  rw [this]
  decide

theorem set_singleton_sub_one {α} (x y : α) (h : #[x].size - 1 < #[x].size) : #[x].set (#[x].size - 1) y h = #[y] := by
  rfl

theorem evalStatement_placeMention_eq
    {body : CapturedMir} {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {loc : Nat} {decl : LocalDecl} {span : String}
    (hframes : m.stack.frames = #[topFrame])
    (hlt : loc < topFrame.locals.size)
    (hdecl : get? body.localDecls loc = some decl)
    (hcache : ∀ l, (topFrame.locals[loc]'hlt).layout = some l →
      l = translateTy decl.ty body.layouts) :
    Miri.Interpreter.Step.evalStatement (annealStepHooks body.localDecls body.layouts) () (translateStmt ⟨.placeMention ⟨loc, .nil⟩, span⟩) m =
      ({ m with
          stack := ⟨#[{ topFrame with
            locals := topFrame.locals.set loc
              { topFrame.locals[loc]'hlt with layout := some (translateTy decl.ty body.layouts) } hlt }]⟩ },
        .ok ()) := by
  have hget : topFrame.getLocal loc = .ok (topFrame.locals[loc]'hlt) := by
    unfold Miri.Interpreter.Frame.getLocal
    simp [hlt, pure, Except.pure]
  have hgor := frame_getOrCacheLocalLayout_eq_storage topFrame hlt hcache
  have h_proj : ((List.map translateProjectionElem []).toArray.isEmpty) = true := rfl
  simp only [Miri.Interpreter.Step.evalStatement, translateStmt, translateStmtKind, translatePlace,
    h_proj, Bool.not_true, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte, Miri.Interpreter.runRvalue, Except.map,
    annealStepHooks, annealEvalPlace, annealResolveAndCacheLocalLayout,
    stack_currentFrame?_singleton m.stack topFrame hframes, Option.isNone,
    Miri.Interpreter.Frame.getOrCacheLocalLayout, hget, bind, pure,
    Except.bind, Except.pure, EStateM.bind, EStateM.pure, EStateM.get, EStateM.set, get, set,
    getThe, MonadStateOf.get, MonadStateOf.set, HOrElse.hOrElse, OrElse.orElse, Option.orElse,
    Option.getD, hdecl, lookupLocalDeclLayout, Option.map, Option.bind, hframes,
    hlt, size_singleton_sub_one, set_singleton_sub_one]
  rcases m with ⟨⟨frames⟩, ⟨mem, addr, bt⟩⟩
  cases hc : (topFrame.locals[loc]'hlt).layout
  · simp only [hc, ↓reduceIte]
    rfl
  · have hl := hcache _ hc
    subst hl
    simp only [hc, ↓reduceIte]
    have hset : topFrame.locals.set loc { topFrame.locals[loc]'hlt with layout := some (translateTy decl.ty body.layouts) } hlt = topFrame.locals := by
      apply Array.ext
      · simp
      · intro i hi1 hi2
        rw [Array.getElem_set]
        split
        · subst i
          cases h_local : topFrame.locals[loc]
          rw [h_local] at hc
          subst hc
          rfl
        · rfl
    rw [hset]
    rfl

theorem step_placeMention_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRel body s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {place : Place} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.placeMention place, span⟩)
    (hwt : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedLM1_4Stmt body topFrame ⟨.placeMention place, span⟩)
    (hnotDead : ∃ val, get? s.frame.locals place.local_ = some val ∧ val ≠ .dead) :
    StepRel body m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  rcases hstate with ⟨topFrame, hframes, ht_ret, ht_retp, hfr, hcal_none, ht_stack, ht_bor, ht_prot, ht_caller, hdisj⟩
  rw [stepMirFn_eq_of_not_other body s hcal_none hphase]
  simp only [hbb, hstmt]
  have hwt' := hwt topFrame hframes
  cases hwt' with
  | placeMention _ decl _ hdecl hproj =>
    have hplace_eq : place = { local_ := place.local_, projection := [] } := by
      cases place
      dsimp only at hproj
      subst hproj
      rfl
    have hstmt' : get? bb.statements s.frame.stmtIdx = some ⟨.placeMention { local_ := place.local_, projection := [] }, span⟩ := by
      rw [hplace_eq] at hstmt
      exact hstmt
    have hlt_body : place.local_ < body.localDecls.length := List_get_eq_some_length_storage hdecl
    have hlt_af : place.local_ < s.frame.locals.length := by
      rw [hfr.af_locals_len]
      exact hlt_body
    have hlt_mf : place.local_ < topFrame.locals.size := by
      rw [hfr.mf_locals_size]
      exact hlt_body
    have ⟨slot, hslot⟩ := List_get_eq_some_of_lt_storage hlt_af
    have ⟨mls, hmls⟩ := Array_get_eq_some_of_lt_storage hlt_mf
    rcases hnotDead with ⟨val, hval, hndead⟩
    have hslot_eq : val = slot := by rw [hval] at hslot; exact Option.some.inj hslot
    rw [hslot_eq] at hndead hval
    have ha : evalStmt s { kind := StatementKind.placeMention place, span := span } body.localDecls body.layouts = MirStepNode.step (advanceStmt s s.frame.locals) := by
      unfold evalStmt
      dsimp only
      rw [hslot]
      split
      · rename_i hmatch
        contradiction
      · rename_i hmatch
        injection hmatch with hmatch
        exact False.elim (hndead hmatch)
      · rfl
    rw [ha]




    have heval_mf := evalStatement_placeMention_eq (span := span) hframes hlt_mf hdecl (by
      intro l hl
      have hrel := hfr.locals_rel place.local_ decl slot mls hdecl hslot hmls
      have h_getElem? := Array.getElem?_eq_getElem hlt_mf
      rw [h_getElem?] at hmls
      have heq_mls : topFrame.locals[place.local_]'hlt_mf = mls := Option.some.inj hmls
      rw [heq_mls] at hl
      exact LocalRel.cachedLayout_eq hrel l hl
    )
    rw [miri_step_at_statement_ok_storage (annealStepHooks body.localDecls body.layouts) hframes hfr.body_eq hfr.location_eq hbb hstmt' heval_mf rfl hfr.location_eq]
    apply StepRel.step
    have hfr_new : FrameRel body m.machine (advanceStmt s s.frame.locals).frame { topFrame with locals := topFrame.locals.set place.local_ { value := topFrame.locals[place.local_].value, layout := some (translateTy decl.ty body.layouts) } hlt_mf, location := .mir ⟨s.frame.blockIdx, s.frame.stmtIdx + 1⟩ } := by
      refine ⟨hfr.body_eq, rfl, ?_, ?_, ?_⟩
      · dsimp only [advanceStmt]; rw [hfr.af_locals_len]
      · rw [Array.size_set, hfr.mf_locals_size]
      · intro i decl_i slot_i mls_i hdecl_i hslot_i hmls_i
        dsimp only [advanceStmt] at hslot_i
        dsimp only at hslot_i hmls_i
        rw [Array.getElem?_set] at hmls_i
        by_cases heq : place.local_ = i
        · subst heq
          simp only [hlt_af, ↓reduceIte, Option.some.injEq] at hmls_i
          have hdecl_eq : decl = decl_i := by
            rw [hdecl] at hdecl_i; exact Option.some.inj hdecl_i
          have hslot_eq2 : slot = slot_i := by
            rw [hslot] at hslot_i; exact Option.some.inj hslot_i
          subst hdecl_eq hslot_eq2 hmls_i
          have h_src_val : topFrame.locals[place.local_].value = mls.value := by
            have h_getElem? := Array.getElem?_eq_getElem hlt_mf
            have hmls' := hmls
            rw [h_getElem?] at hmls'
            exact congrArg (fun x => x.value) (Option.some.inj hmls')
          rw [h_src_val]
          have hrel_old := hfr.locals_rel place.local_ decl slot mls hdecl hslot hmls
          cases hrel_old
          · constructor
            intro l hl; cases hl; rfl
          · constructor
            any_goals assumption
            any_goals { intro l hl; cases hl; rfl }
          · constructor
            any_goals assumption
            any_goals { intro l hl; cases hl; rfl }
        · simp only [heq, ↓reduceIte] at hmls_i
          exact hfr.locals_rel i decl_i slot_i mls_i hdecl_i hslot_i hmls_i
    exact StateRel.mk _ rfl ht_ret ht_retp hfr_new hcal_none ht_stack ht_bor ht_prot ht_caller (by
      apply MemoryAllocDisjoint.mono_layout hdisj
      intro k
      by_cases hk : place.local_ = k
      · subst hk
        exact ⟨some (translateTy decl.ty body.layouts), by
          rw [Array.getElem?_set]
          split
          · rename_i hlt_k
            have h_getElem? := Array.getElem?_eq_getElem hlt_mf
            have hmls' := hmls
            rw [h_getElem?] at hmls'
            have h_val_eq : topFrame.locals[place.local_] = mls := Option.some.inj hmls'
            rw [h_val_eq, hmls]
            rfl
          · contradiction⟩
      · exact ⟨(topFrame.locals[k]?).bind (fun x => x.layout), by
          rw [Array.getElem?_set]
          split
          · rename_i hlt_k
            contradiction
          · cases topFrame.locals[k]?
            · rfl
            · rfl⟩
    )

#print Trusted.Rustc.V2026_06_01.MirSemantics.evalOperand
theorem evalOperand_move_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRel body s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx : Local} {srcPlace : Place} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.assign ⟨dstIdx, .nil⟩ (.use (.move srcPlace)), span⟩)
    (hwt : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedLM1_4Stmt body topFrame ⟨.assign ⟨dstIdx, .nil⟩ (.use (.move srcPlace)), span⟩) :
    StepRel body m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  rcases hstate with ⟨topFrame, hframes, ht_ret, ht_retp, hfr, hcal_none, ht_stack, ht_bor, ht_prot, ht_caller, hdisj⟩
  rw [stepMirFn_eq_of_not_other body s hcal_none hphase]
  simp only [hbb, hstmt]
  have hwt' := hwt topFrame hframes
  cases hwt' with
  | assignMove _ dstDecl _ srcDecl _ hdst hsrc hproj hty =>
    have hlt_body_src : srcPlace.local_ < body.localDecls.length := List_get_eq_some_length_storage hsrc
    have hlt_af_src : srcPlace.local_ < s.frame.locals.length := by
      rw [hfr.af_locals_len]; exact hlt_body_src
    have hlt_mf_src : srcPlace.local_ < topFrame.locals.size := by
      rw [hfr.mf_locals_size]; exact hlt_body_src
    have ⟨slot_src, hslot_src⟩ := List_get_eq_some_of_lt_storage hlt_af_src
    have ⟨mls_src, hmls_src⟩ := Array_get_eq_some_of_lt_storage hlt_mf_src
    
    have hlt_body_dst : dstIdx < body.localDecls.length := List_get_eq_some_length_storage hdst
    have hlt_af_dst : dstIdx < s.frame.locals.length := by
      rw [hfr.af_locals_len]; exact hlt_body_dst
    have hlt_mf_dst : dstIdx < topFrame.locals.size := by
      rw [hfr.mf_locals_size]; exact hlt_body_dst
    have ⟨slot_dst, hslot_dst⟩ := List_get_eq_some_of_lt_storage hlt_af_dst
    have ⟨mls_dst, hmls_dst⟩ := Array_get_eq_some_of_lt_storage hlt_mf_dst
    
    cases h_slot_src_eq : slot_src with
    | init v => sorry
    | uninit => sorry
    | dead => sorry

theorem LocalRel_cacheLayout {mach decl layouts slot value} {lay : Miri.Interpreter.LocalLayout} :
  lay = translateTy decl.ty layouts →
  LocalRel mach decl layouts slot value →
  LocalRel mach decl layouts slot { value with layout := some lay } := by
  intro hl hrel
  cases hrel
  · apply LocalRel.dead
    intro l hl_some
    cases hl_some
    exact hl
  · apply LocalRel.immediate
    · intro l hl_some
      cases hl_some
      exact hl
    · assumption
  · apply LocalRel.indirect
    · intro l hl_some
      cases hl_some
      exact hl
    · assumption
    · assumption

theorem FrameRel_cacheLayout {body mach af mf} {idx : Nat} {lay : Miri.Interpreter.LocalLayout}
  (hrel : FrameRel body mach af mf)
  {decl_cached : LocalDecl}
  (hdecl : get? body.localDecls idx = some decl_cached)
  (hlay : lay = translateTy decl_cached.ty body.layouts)
  (hlt : idx < mf.locals.size) :
  FrameRel body mach af (cacheFrameLocalLayout mf idx hlt lay) := by
  cases hrel with | mk body_eq loc_eq af_locals_len mf_locals_len h_locs =>
  apply FrameRel.mk
  · exact body_eq
  · exact loc_eq
  · exact af_locals_len
  · unfold cacheFrameLocalLayout; dsimp; rw [Array.size_set]; exact mf_locals_len
  · intro i decl_i slot mls_i h_decl_i h_slot_i h_mls_i
    unfold cacheFrameLocalLayout at h_mls_i; dsimp at h_mls_i
    rw [Array.getElem?_set] at h_mls_i
    split at h_mls_i
    next heq =>
      subst i
      rw [hdecl] at h_decl_i
      cases h_decl_i
      have h_mls_idx : mf.locals[idx]? = some (mf.locals[idx]'hlt) := by
        apply Array.getElem?_eq_getElem
      have h_loc := h_locs idx decl_cached slot (mf.locals[idx]'hlt) hdecl h_slot_i h_mls_idx
      injection h_mls_i with heq_mls
      subst mls_i
      apply LocalRel_cacheLayout hlay h_loc
    next hneq =>
      exact h_locs i decl_i slot mls_i h_decl_i h_slot_i h_mls_i



theorem StateRel_allocateStack {body s m layout allocated m'}
  (hstate : StateRel body s m)
  (h_alloc : (annealPlaceHooks body.localDecls body.layouts).allocateStack () layout m = EStateM.Result.ok allocated m') :
  StateRel body s m' ∧ m'.stack.frames = m.stack.frames ∧ True := by
  sorry

theorem StateRel_setFrame {body s m f m'}
  (hstate : StateRel body s m)
  (hset : (annealPlaceHooks body.localDecls body.layouts).setFrame f m = EStateM.Result.ok () m') :
  StateRel body s m' := by
  sorry

theorem StateRel_writeMemoryNoValidate {body s m val allocated m'}
  (hstate : StateRel body s m)
  (hwrite : (annealPlaceHooks body.localDecls body.layouts).writeMemoryNoValidate () val allocated m = EStateM.Result.ok () m') :
  StateRel body s m' := by
  sorry

theorem StateRel_memoryOffset {body s m whole offset mplace m'}
  (hstate : StateRel body s m)
  (hoffset : (annealPlaceHooks body.localDecls body.layouts).memoryOffset () whole offset Miri.Interpreter.OffsetMode.wrapping Miri.Interpreter.MemPlaceMeta.none m = EStateM.Result.ok mplace m') :
  StateRel body s m' := by
  sorry

theorem forceAllocation_preserves_StateRel
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRel body s m)
    (topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    (hframes : m.stack.frames = #[topFrame])
    (loc : Local)
    (place : Miri.Interpreter.RuntimePlace AnnealProv)
    (m' : AnnealStepState)
    (mplace : Miri.Interpreter.MPlaceTy AnnealProv)
    (hforce : Miri.Interpreter.forceAllocation (annealPlaceHooks body.localDecls body.layouts) () place m = .ok mplace m') :
    StateRel body s m' := by
  unfold Miri.Interpreter.forceAllocation at hforce
  cases hpref : place.ref with
  | «local» frameIndex localId offset identity =>
    rw [hpref] at hforce
    dsimp only at hforce
    rw [Miri.Interpreter.requireCurrent_eq] at hforce
    rw [Miri.Interpreter.checkLocalIdentity_debugOff (off := rfl)] at hforce
    have ⟨res_req, m1, h_require, hforce1⟩ := split_bind hforce
    have ⟨a_req, s_req, h_fidx, h_req2⟩ := split_bind h_require
    dsimp [annealPlaceHooks, Miri.Interpreter.PlaceHooks.frameIndex, get, EStateM.get, StateT.get] at h_fidx
    injection h_fidx with _ hs_req; subst s_req
    split at h_req2 <;> try contradiction
    dsimp [pure, EStateM.pure] at h_req2
    injection h_req2 with _ hm1; subst m1
    have ⟨res_check, m2, h_check, hforce2⟩ := split_bind hforce1
    dsimp [pure, EStateM.pure] at h_check
    injection h_check with _ hm2; subst m2
    
    have ⟨res_frame, m3, h_frame, hforce3⟩ := split_bind hforce2
    unfold Miri.Interpreter.PlaceHooks.getFrame at h_frame
    have ⟨a_frame_state, s_frame_state, h_frame_get, h_frame_match⟩ := split_bind h_frame
    dsimp [get, EStateM.get, StateT.get] at h_frame_get
    injection h_frame_get with h_a hs_frame
    subst a_frame_state s_frame_state
    
    unfold Miri.Interpreter.Stack.currentFrame? at h_frame_match
    rw [hframes] at h_frame_match
    dsimp [Array.back?] at h_frame_match
    dsimp [pure, EStateM.pure] at h_frame_match
    injection h_frame_match with h_res_frame hm3; subst m3
    
    have ⟨old, m4, h_lift, hforce4⟩ := split_bind hforce3
    
    cases h_op : res_frame.getLocalOperand localId
    · rw [h_op] at h_lift
      -- if error, stackLift evaluates to error, which contradicts ok
      revert h_lift
      intro h_lift
      contradiction
    · rw [h_op] at h_lift
      dsimp [pure, EStateM.pure] at h_lift
      injection h_lift with h_old hm4; subst m4
      cases h_old_match : old with
      | indirect mplace_old =>
        rw [h_old_match] at hforce4
        dsimp only at hforce4
        have ⟨whole, m5, h_pure, hforce5⟩ := split_bind hforce4
        dsimp [pure, EStateM.pure] at h_pure
        injection h_pure with _ hm5; subst m5
        cases h_off : offset <;> rw [h_off] at hforce5 <;> dsimp only at hforce5
        · dsimp [bind, StateT.bind, EStateM.bind, pure, EStateM.pure] at hforce5
          injection hforce5 with _ hm_eq
          subst hm_eq
          exact hstate
        · have ⟨whole2, m6, h_mem_off, hforce6⟩ := split_bind hforce5
          dsimp [annealPlaceHooks, Miri.Interpreter.PlaceHooks.memoryOffset] at h_mem_off
          dsimp [throw, EStateM.throw] at h_mem_off
          contradiction
      | immediate val =>
        rw [h_old_match] at hforce4
        dsimp only at hforce4
        unfold Miri.Interpreter.placeLayoutOfLocal at hforce4
        have ⟨layout, m5, h_layout, hforce5⟩ := split_bind hforce4
        
        -- Now h_layout is the execution of placeLayoutOfLocal
        have hstate5 : StateRel body s m5 := by
          sorry
        
        split at hforce5
        · dsimp [throw, EStateM.throw] at hforce5
          contradiction
        · dsimp [pure, EStateM.pure] at hforce5
          have ⟨allocated, m6, h_alloc, hforce6⟩ := split_bind hforce5
          
          cases hval : val with
          | uninit =>
            sorry

          | scalar sc =>
            rw [hval] at hforce6
            dsimp only at hforce6
            trace_state; sorry
          | scalarPair sc1 sc2 =>
            rw [hval] at hforce6
            dsimp only at hforce6
            trace_state; sorry
  | memory mplace_mem =>
    sorry

end LeanMiriSpec.Correspondence

