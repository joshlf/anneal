/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import LeanMiriSpec.Correspondence.WitLM2_4PaddedZst

/-!
# Two-Sided General Step Simulation Theorems (`R-a`) and Never-Written Union Boundary (`R-b`)

Extracted from `WitLM2_4.lean` (Section 12 second half) so every `LM-2.4`
witness module stays strictly `< 3,500` LOC.
-/

namespace LeanMiriSpec.Correspondence.Witness

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open LeanMiriSpec.Correspondence

/-! ### Two-Sided General Step Simulation Theorems (`R-a`) and Never-Written Union Boundary (`R-b`)

The helpers below derive Anneal's `readProjectedValueUnionAware` and `stepMirFn`
outcomes directly from `Trusted.Rustc.V2026_06_01.MirSemantics` (without
importing `Anneal.*`), upgrading the padded-ZST union step theorems so Anneal's
step/fault is **proved** rather than assumed (`R-a`). -/

private theorem resolveTyWithLocalDecls_kind_lm24
    (localDecls : List LocalDecl) (layouts : LayoutTable) (ty : Ty) :
    (resolveTyWithLocalDecls localDecls layouts ty).kind = ty.kind := by
  unfold resolveTyWithLocalDecls
  cases isUnresolvedLayoutIdx layouts ty.layoutIdx <;> dsimp only
  all_goals (try rfl)
  cases findDeclOrContainerElemTyWithKind? localDecls layouts ty.kind <;> dsimp only
  all_goals (try rfl)
  cases Nat.beq ty.layoutIdx 0 <;> cases localDecls <;> dsimp only
  all_goals (try (cases isPrimitiveScalarKind ty.kind <;> rfl))
  all_goals rfl

/-- Resolved field type `rFieldTy` computed by `readProjectedValueUnionAware`. -/
def unionFieldReadTyLM2_4 (localDecls : List LocalDecl) (layouts : LayoutTable) (l : TypeLayout)
    (idx : Nat) (fieldTy : Ty) : Ty :=
  match isUnresolvedLayoutIdx layouts fieldTy.layoutIdx with
  | false => fieldTy
  | true =>
    match get? l.fieldLayouts idx with
    | some flIdx => { fieldTy with layoutIdx := flIdx }
    | none => resolveTyWithLocalDecls localDecls layouts fieldTy

private theorem unionFieldReadTyLM2_4_kind (localDecls : List LocalDecl) (layouts : LayoutTable)
    (l : TypeLayout) (idx : Nat) (fieldTy : Ty) :
    (unionFieldReadTyLM2_4 localDecls layouts l idx fieldTy).kind = fieldTy.kind := by
  unfold unionFieldReadTyLM2_4
  cases isUnresolvedLayoutIdx layouts fieldTy.layoutIdx <;> dsimp only
  all_goals (try rfl)
  cases get? l.fieldLayouts idx <;> dsimp only
  all_goals (try rfl)
  exact resolveTyWithLocalDecls_kind_lm24 localDecls layouts fieldTy

/-- Canonical 0-byte value decoded by `readProjectedValueUnionAware`. -/
def zeroByteValueLM2_4 (layouts : LayoutTable) (ty : Ty) : Value :=
  match decodeTypedValueFromBytes defaultCodecFuel layouts ty .nil with
  | some v => v
  | none => .unit

/-- Inactive union slot condition (`directFvOpt = none`). -/
def UnionSlotInactiveLM2_4 (fields : List Value) (idx : Nat) (k : RigidTy) : Prop :=
  get? fields idx = none ∨
    (get? fields idx = some .unit ∧ k ≠ .tuple [] ∧ ∀ p a, k ≠ .fnDef p a)

/-- Well-formedness gate (`unionImageOk`) in `readProjectedValueUnionAware`. -/
def UnionImageOkLM2_4 (layouts : LayoutTable) (uIdx count : Nat) (fields : List Value) : Prop :=
  unionNeedsConsistencyCheck count fields = false ∨
    ∃ img, encodeByLayoutIdxAux 8 layouts uIdx (.aggregate 0 fields) = some img

private theorem kani5159_uninhabited_field_root_ub_lm24
    (locals : List LocalSlot) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (baseTy fieldTy : Ty) (fields : List Value) (idx count : Nat) (l : TypeLayout)
    (d : DefPath) (args : List RigidTy)
    (hKind : (resolveTyWithLocalDecls localDecls layouts baseTy).kind = .adt d args)
    (hLookup : LayoutTable.lookup layouts (resolveTyWithLocalDecls localDecls layouts baseTy).layoutIdx =
      some l)
    (hFields : l.fields = .union count)
    (hIdx : idx < count)
    (hImg : UnionImageOkLM2_4 layouts (resolveTyWithLocalDecls localDecls layouts baseTy).layoutIdx count fields)
    (hSlot : UnionSlotInactiveLM2_4 fields idx fieldTy.kind)
    (hUninh : tyIsUninhabited layouts (unionFieldReadTyLM2_4 localDecls layouts l idx fieldTy) = true)
    (hSz : tyByteSize localDecls layouts (unionFieldReadTyLM2_4 localDecls layouts l idx fieldTy) = some 0 ∨
      tyByteSize localDecls layouts (unionFieldReadTyLM2_4 localDecls layouts l idx fieldTy) = none) :
    readProjectedValueUnionAware locals localDecls layouts (.aggregate 0 fields) baseTy
        [.field idx fieldTy] = .ub := by
  have hBle : Nat.ble (idx + 1) count = true := Nat.ble_eq.mpr hIdx
  unfold readProjectedValueUnionAware
  dsimp only
  rw [hKind, hLookup]
  dsimp only
  rw [hFields]
  dsimp only
  rw [hBle]
  simp only []
  have hTk := unionFieldReadTyLM2_4_kind localDecls layouts l idx fieldTy
  unfold unionFieldReadTyLM2_4 at hSz hTk hUninh
  cases hg : get? l.fieldLayouts idx <;>
    cases hu : isUnresolvedLayoutIdx layouts fieldTy.layoutIdx <;>
    simp only [hu, hg] at hSz hTk hUninh ⊢
  all_goals
    cases hC : unionNeedsConsistencyCheck count fields <;>
    rcases hSlot with hS | ⟨hS, hNU, hNF⟩ <;> rw [hS] <;> (try rw [hTk])
  all_goals
    first
    | (rcases hSz with hSz | hSz <;> simp only [] <;> rw [hSz] <;> simp only [hUninh]; done)
    | (rcases hImg with h | ⟨img, hEnc⟩
       · rw [hC] at h; nomatch h
       · rw [hEnc]; simp only []
         cases l.fieldLayouts <;> simp only [] <;>
           (rcases hSz with hSz | hSz <;> rw [hSz] <;> simp only [hUninh]))

private theorem readUnion_zeroByte_fieldRoot_lm24
    (locals : List LocalSlot) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (baseTy fieldTy : Ty) (fields : List Value) (idx count : Nat) (l : TypeLayout)
    (d : DefPath) (args : List RigidTy)
    (hKind : (resolveTyWithLocalDecls localDecls layouts baseTy).kind = .adt d args)
    (hLookup : LayoutTable.lookup layouts (resolveTyWithLocalDecls localDecls layouts baseTy).layoutIdx =
      some l)
    (hFields : l.fields = .union count)
    (hIdx : idx < count)
    (hImg : UnionImageOkLM2_4 layouts (resolveTyWithLocalDecls localDecls layouts baseTy).layoutIdx count fields)
    (hSlot : UnionSlotInactiveLM2_4 fields idx fieldTy.kind)
    (hSz : tyByteSize localDecls layouts (unionFieldReadTyLM2_4 localDecls layouts l idx fieldTy) = some 0)
    (hInh : tyIsUninhabited layouts (unionFieldReadTyLM2_4 localDecls layouts l idx fieldTy) = false)
    (p : ProjectionElem) (ps idxResolved : List ProjectionElem)
    (hRes : resolveUnionSubProjIndices locals (p :: ps) = some idxResolved)
    (hBounds : checkStaticSubProjBounds localDecls layouts (unionFieldReadTyLM2_4 localDecls layouts l idx fieldTy)
      (normalizeSubsliceProjections (stripTransparentProjections idxResolved)) = false) :
    readProjectedValueUnionAware locals localDecls layouts (.aggregate 0 fields) baseTy
        (.field idx fieldTy :: p :: ps) =
      readProjectedValueUnionAware locals localDecls layouts
        (zeroByteValueLM2_4 layouts (unionFieldReadTyLM2_4 localDecls layouts l idx fieldTy))
        (unionFieldReadTyLM2_4 localDecls layouts l idx fieldTy) (p :: ps) := by
  have hBle : Nat.ble (idx + 1) count = true := Nat.ble_eq.mpr hIdx
  conv => lhs; unfold readProjectedValueUnionAware
  dsimp only
  rw [hKind, hLookup]
  dsimp only
  rw [hFields]
  dsimp only
  rw [hBle]
  simp only []
  have hTk := unionFieldReadTyLM2_4_kind localDecls layouts l idx fieldTy
  unfold unionFieldReadTyLM2_4 at hTk hSz hInh hBounds ⊢
  cases hg : get? l.fieldLayouts idx <;>
    cases hu : isUnresolvedLayoutIdx layouts fieldTy.layoutIdx <;>
    simp only [hu, hg] at hTk hSz hInh hBounds ⊢
  all_goals
    cases hC : unionNeedsConsistencyCheck count fields <;>
    rcases hSlot with hS | ⟨hS, hNU, hNF⟩ <;> rw [hS] <;> (try rw [hTk])
  all_goals
    first
    | (simp only []; rw [hRes]; simp only []; rw [hBounds]; simp only []; rw [hSz]; simp only [hInh]; rfl)
    | (rcases hImg with h | ⟨img, hEnc⟩
       · rw [hC] at h; nomatch h
       · rw [hEnc]; simp only []
         cases l.fieldLayouts <;> simp only [] <;> rw [hRes] <;> simp only [] <;> rw [hBounds] <;>
           simp only [] <;> rw [hSz] <;> simp only [hInh] <;> rfl)

private theorem replicateUninitBytes_eq_replicate_lm24 :
    ∀ n : Nat, replicateUninitBytes n = List.replicate n AbstractByte.uninit
  | 0 => rfl
  | k + 1 => by simp [replicateUninitBytes, List.replicate_succ, replicateUninitBytes_eq_replicate_lm24 k]

private theorem takeAbstractBytes_eq_take_lm24 :
    ∀ (n : Nat) (bs : List AbstractByte), takeAbstractBytes n bs = bs.take n
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | k + 1, b :: bs => by simp [takeAbstractBytes, takeAbstractBytes_eq_take_lm24 k bs]

private theorem length_eq_list_length_lm24 {α : Type} :
    ∀ xs : List α, Trusted.Sequence.length xs = xs.length
  | [] => rfl
  | _ :: xs => congrArg Nat.succ (length_eq_list_length_lm24 xs)

private theorem sliceAbstractBytes_zero_take_lm24 (bs : List AbstractByte) (n : Nat)
    (h : n ≤ bs.length) :
    sliceAbstractBytes bs 0 n = some (bs.take n) := by
  unfold sliceAbstractBytes
  have hBle : Nat.ble (Nat.add 0 n) (Trusted.Sequence.length bs) = true := by
    rw [length_eq_list_length_lm24]
    change Nat.ble (0 + n) bs.length = true
    rw [Nat.zero_add]
    exact Nat.ble_eq.mpr h
  rw [hBle]
  dsimp only [dropAbstractBytes]
  rw [takeAbstractBytes_eq_take_lm24]

private theorem tyByteSize_succ_kind_lm24 (localDecls : List LocalDecl) (layouts : LayoutTable)
    (ty : Ty) (n : Nat) (h : tyByteSize localDecls layouts ty = some (n + 1)) :
    ty.kind ≠ .tuple [] ∧ ∀ p a, ty.kind ≠ .fnDef p a := by
  have hk := resolveTyWithLocalDecls_kind_lm24 localDecls layouts ty
  unfold tyByteSize tyByteSizeAndAlignAux at h
  dsimp only at h
  rw [hk] at h
  refine ⟨fun hT => ?_, fun p a hF => ?_⟩
  · rw [hT] at h; simp at h
  · rw [hF] at h; simp at h

private theorem readUnion_posField_offset0_none_lm24
    (locals : List LocalSlot) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (baseTy fieldTy : Ty) (fields : List Value) (idx count : Nat) (l : TypeLayout)
    (d : DefPath) (args : List RigidTy)
    (hKind : (resolveTyWithLocalDecls localDecls layouts baseTy).kind = .adt d args)
    (hLookup : LayoutTable.lookup layouts (resolveTyWithLocalDecls localDecls layouts baseTy).layoutIdx =
      some l)
    (hFields : l.fields = .union count)
    (hIdx : idx < count)
    (hSlot : UnionSlotInactiveLM2_4 fields idx fieldTy.kind)
    (img : List AbstractByte)
    (hEnc : encodeByLayoutIdxAux 8 layouts (resolveTyWithLocalDecls localDecls layouts baseTy).layoutIdx
      (.aggregate 0 fields) = some img)
    (n : Nat)
    (hSz : tyByteSize localDecls layouts (unionFieldReadTyLM2_4 localDecls layouts l idx fieldTy) = some (n + 1))
    (hInt : (∃ wk, fieldTy.kind = .uint wk) ∨ (∃ wk, fieldTy.kind = .int wk))
    (hLe : n + 1 ≤ img.length)
    (hDecNone : decodeTypedValueFromBytes defaultCodecFuel layouts
        (unionFieldReadTyLM2_4 localDecls layouts l idx fieldTy) (img.take (n + 1)) = none) :
    readProjectedValueUnionAware locals localDecls layouts (.aggregate 0 fields) baseTy
        [.field idx fieldTy] = .ub := by
  have hBle : Nat.ble (idx + 1) count = true := Nat.ble_eq.mpr hIdx
  have hSlice := sliceAbstractBytes_zero_take_lm24 img (n + 1) hLe
  unfold readProjectedValueUnionAware
  dsimp only
  rw [hKind, hLookup]
  dsimp only
  rw [hFields]
  dsimp only
  rw [hBle]
  simp only []
  have hTk := unionFieldReadTyLM2_4_kind localDecls layouts l idx fieldTy
  unfold unionFieldReadTyLM2_4 at hSz hTk hDecNone
  cases hg : get? l.fieldLayouts idx <;>
    cases hu : isUnresolvedLayoutIdx layouts fieldTy.layoutIdx <;>
    simp only [hu, hg] at hSz hTk hDecNone ⊢
  all_goals
    cases hC : unionNeedsConsistencyCheck count fields <;>
    rcases hSlot with hS | ⟨hS, hNU, hNF⟩ <;> rw [hS] <;> (try rw [hTk]) <;> rw [hEnc] <;>
    simp only []
  all_goals (try (cases l.fieldLayouts <;> simp only []))
  all_goals
    rw [hSz]; simp only []
    rcases hInt with ⟨wk, hwk⟩ | ⟨wk, hwk⟩ <;>
    (simp only [hwk] at hDecNone ⊢; simp only [hSlice, hDecNone])

private theorem abstractBytesHaveProv_replicate_uninit_lm24 :
    ∀ n : Nat, abstractBytesHaveProv (List.replicate n AbstractByte.uninit) = false
  | 0 => rfl
  | k + 1 => abstractBytesHaveProv_replicate_uninit_lm24 k

private theorem decodeTypedValueFromBytes_int_uninit_lm24 (layouts : LayoutTable) (ty : Ty) (n : Nat)
    (hInt : (∃ w, ty.kind = .uint w) ∨ (∃ w, ty.kind = .int w)) :
    decodeTypedValueFromBytes defaultCodecFuel layouts ty (List.replicate (n + 1) .uninit) = none := by
  have hP := abstractBytesHaveProv_replicate_uninit_lm24 (n + 1)
  have hD : ∀ s, decodeScalarBytes (List.replicate (n + 1) AbstractByte.uninit) s = none := by
    intro s
    unfold decodeScalarBytes
    rw [List.replicate_succ]
    cases Nat.beq (Trusted.Sequence.length (AbstractByte.uninit :: List.replicate n AbstractByte.uninit)) 0 <;> rfl
  rw [show defaultCodecFuel = 15 + 1 from rfl]
  rcases hInt with ⟨w, hw⟩ | ⟨w, hw⟩
  · unfold decodeTypedValueFromBytes
    simp only [normalizeCodecTy, hw]
    rw [hP]
    simp only []
    unfold decodeValueFromBytes
    simp only [hw, hD]
    cases intCastTargetBytes (RigidTy.uint w) with
    | none => simp only []
    | some eb =>
      cases h2 : Nat.beq (Trusted.Sequence.length (List.replicate (n + 1) AbstractByte.uninit)) eb <;>
        simp only [h2]
  · unfold decodeTypedValueFromBytes
    simp only [normalizeCodecTy, hw]
    rw [hP]
    simp only []
    unfold decodeValueFromBytes
    simp only [hw, hD]
    cases intCastTargetBytes (RigidTy.int w) with
    | none => simp only []
    | some eb =>
      cases h2 : Nat.beq (Trusted.Sequence.length (List.replicate (n + 1) AbstractByte.uninit)) eb <;>
        simp only [h2]

private theorem get?_replicate_unit_lm24 :
    ∀ (count i : Nat), i < count → get? (List.replicate count Value.unit) i = some .unit
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | _ + 1, 0, _ => rfl
  | k + 1, i + 1, h => get?_replicate_unit_lm24 k i (Nat.lt_of_succ_lt_succ h)

private theorem get?_eq_none_of_le_lm24 {α : Type} :
    ∀ (xs : List α) (i : Nat), xs.length ≤ i → get? xs i = none
  | [], 0, _ => rfl
  | [], _ + 1, _ => rfl
  | _ :: xs, i + 1, h => get?_eq_none_of_le_lm24 xs i (Nat.le_of_succ_le_succ h)

private theorem placeTouchesUnion_field_of_union_lm24
    (localDecls : List LocalDecl) (layouts : LayoutTable) (u j count : Nat)
    (uDecl : LocalDecl) (fieldTy : Ty) (rest : List ProjectionElem)
    (l : TypeLayout) (d : DefPath) (args : List RigidTy)
    (hdecl_u : get? localDecls u = some uDecl)
    (hKind : (resolveTyWithLocalDecls localDecls layouts uDecl.ty).kind = .adt d args)
    (hLookup : LayoutTable.lookup layouts
      (resolveTyWithLocalDecls localDecls layouts uDecl.ty).layoutIdx = some l)
    (hFields : l.fields = .union count) :
    placeTouchesUnion localDecls layouts ⟨u, .field j fieldTy :: rest⟩ = true := by
  obtain ⟨hd, tl, hds⟩ : ∃ hd tl, localDecls = hd :: tl := by
    cases h : localDecls with
    | nil => rw [h] at hdecl_u; cases u <;> cases hdecl_u
    | cons hd tl => exact ⟨hd, tl, rfl⟩
  obtain ⟨le, les, hls⟩ : ∃ le les, layouts.entries = le :: les := by
    cases h : layouts.entries with
    | nil =>
      unfold LayoutTable.lookup at hLookup
      rw [h] at hLookup
      cases (resolveTyWithLocalDecls localDecls layouts uDecl.ty).layoutIdx <;> cases hLookup
    | cons le les => exact ⟨le, les, rfl⟩
  unfold placeTouchesUnion
  dsimp only
  rw [hds, hls]
  dsimp only
  rw [← hds, hdecl_u]
  dsimp only [tyProjTouchesUnion]
  unfold MirSemantics.isUnionLayout
  rw [hKind, hLookup]
  cases l
  dsimp only at hFields ⊢
  rw [hFields]

/-- **Two-sided general uninhabited zero-variant union field read UB (`R-a`, `kani#5159`)**:
Derives **both** `stepMirFn body s = MirStepNode.fail .ub` in Anneal (via
`kani5159_uninhabited_field_root_ub_lm24`, without assuming `hstep_a`) **and**
`Step.step (annealStepHooksLM2_4PaddedZst ..) () m = (m', .error (.undefinedBehavior "validation: zero-variant enum value"))`
in `lean-miri` via vendored `Miri.Interpreter.projectField` + vendored
`Miri.Interpreter.ValidityVisitor.validatePlace`, establishing `StepRelLM2_4PaddedZst.ub`. -/
theorem step_padded_zst_union_uninhabited_field_read_ub_two_sided
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_4PaddedZst body s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {r u j count n : Nat} {voidTy : Ty} {voidTl : TypeLayout} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨r, .nil⟩ (.use (.copy ⟨u, [.field j voidTy]⟩)), span⟩)
    {rDecl uDecl : LocalDecl}
    (hdecl_r : get? body.localDecls r = some rDecl)
    (hdecl_u : get? body.localDecls u = some uDecl)
    (hru : r ≠ u)
    (hun_u : isUnionLocal body.localDecls body.layouts u = true)
    (hfields : (translateTy uDecl.ty body.layouts).layout.fields = .Union n)
    (hj_lt : j < n)
    (hvoid_lo : 100 ≤ encodeTyId voidTy)
    (hvoid_hi : encodeTyId voidTy < 1000)
    (hvoid_lookup : body.layouts.lookup (encodeTyId voidTy - 100) = some voidTl)
    (hvoid_var : voidTl.variants = .empty)
    (hvoid_fields : voidTl.fields = .arbitrary .nil .nil)
    {fields : List Value} {l : TypeLayout} {d : DefPath} {args : List RigidTy}
    (hu_slot : get? s.frame.locals u = some (.init (.aggregate 0 fields)))
    (hKind : (resolveTyWithLocalDecls body.localDecls body.layouts uDecl.ty).kind = .adt d args)
    (hLookup : LayoutTable.lookup body.layouts
      (resolveTyWithLocalDecls body.localDecls body.layouts uDecl.ty).layoutIdx = some l)
    (hFields : l.fields = .union count)
    (hIdx : j < count)
    (hImg : UnionImageOkLM2_4 body.layouts
      (resolveTyWithLocalDecls body.localDecls body.layouts uDecl.ty).layoutIdx count fields)
    (hSlot : UnionSlotInactiveLM2_4 fields j voidTy.kind)
    (hUninh : tyIsUninhabited body.layouts
      (unionFieldReadTyLM2_4 body.localDecls body.layouts l j voidTy) = true)
    (hSz : tyByteSize body.localDecls body.layouts
        (unionFieldReadTyLM2_4 body.localDecls body.layouts l j voidTy) = some 0 ∨
      tyByteSize body.localDecls body.layouts
        (unionFieldReadTyLM2_4 body.localDecls body.layouts l j voidTy) = none)
    {mp_u : Miri.Interpreter.MemPlace AnnealProv}
    (hmeta : mp_u.metadata = .none)
    (hu_ind : ∀ tf, m.stack.frames = #[tf] → ∃ c, tf.locals[u]? = some ⟨.live (.indirect mp_u), c⟩) :
    stepMirFn body s = MirStepNode.fail .ub ∧
    StepRelLM2_4PaddedZst body m (stepMirFn body s)
      (Miri.Interpreter.Step.step
        (annealStepHooksLM2_4PaddedZst body.localDecls body.layouts) () m) := by
  have hstep_a : stepMirFn body s = MirStepNode.fail .ub := by
    rcases hstate with ⟨_, _, _, _, _, hcal, _, _, _, _, _⟩
    rw [stepMirFn_eq_of_not_other body s hcal hphase]
    simp only [hbb, hstmt]
    have hread := kani5159_uninhabited_field_root_ub_lm24 s.frame.locals body.localDecls
      body.layouts uDecl.ty voidTy fields j count l d args hKind hLookup hFields hIdx hImg hSlot
      hUninh hSz
    have htch := placeTouchesUnion_field_of_union_lm24 body.localDecls body.layouts u j count
      uDecl voidTy [] l d args hdecl_u hKind hLookup hFields
    unfold evalStmt evalRvalue evalOperand readProjectedForLocal
    dsimp only
    rw [hu_slot, htch, hdecl_u]
    dsimp only
    rw [hread]
  exact ⟨hstep_a,
    step_padded_zst_union_uninhabited_field_read_ub hstate hbb hstmt hdecl_r hdecl_u hru hun_u
      hfields hj_lt hvoid_lo hvoid_hi hvoid_lookup hvoid_var hvoid_fields hmeta hu_ind hstep_a⟩

private theorem lm24PUMiriAt_stateRel (b k : Nat) (s1 s4 s7 : LocalSlot)
    (h1 : PaddedZstUnionLocalRel lm24PUMachine (lm24Decl lm24PUTy) lm24PULayouts s1
      { value := .live (.indirect lm24BaseMemPlace),
        layout := some (translateTy lm24PUTy lm24PULayouts) })
    (h4 : PaddedZstUnionLocalRel lm24PUMachine (lm24Decl lm24PUTy) lm24PULayouts s4
      { value := .live (.indirect lm24Arr2MemPlace),
        layout := some (translateTy lm24PUTy lm24PULayouts) })
    (h7 : UnionLocalRel lm24PUMachine (lm24Decl lm24UnitTy) lm24PULayouts s7
      { value := .live (.immediate .uninit),
        layout := some (translateTy lm24UnitTy lm24PULayouts) }) :
    StateRelLM2_4PaddedZst lm24PUBody
      (lm24PUAnnealState b k
        [.uninit, s1, .uninit, .uninit, s4,
         .init (zstArrayVal 4), .init (zstArrayVal 4), s7, .uninit])
      (lm24PUMiriAt b k) := by
  refine .mk { lm24PUInitMiriFrame b with location := .mir ⟨b, k⟩ } rfl rfl ⟨_, rfl⟩
    { body_eq := rfl
      location_eq := rfl
      af_locals_len := rfl
      mf_locals_size := rfl
      locals_rel := ?_ }
    rfl rfl rfl rfl rfl ?_
  · intro i decl slot mls hdecl hslot hmls
    match i with
    | 0 | 2 | 3 | 8 =>
      injection hdecl with hdecl; subst hdecl
      injection hslot with hslot; subst hslot
      injection hmls with hmls; subst hmls
      exact .ofUnionLocalRel _ _ (.base _ _
        (.immediate .uninit .uninit _ (fun l hl => (Option.some.inj hl).symm) (.inl ⟨rfl, rfl⟩)))
    | 1 =>
      injection hdecl with hdecl; subst hdecl
      injection hslot with hslot; subst hslot
      injection hmls with hmls; subst hmls
      exact h1
    | 4 =>
      injection hdecl with hdecl; subst hdecl
      injection hslot with hslot; subst hslot
      injection hmls with hmls; subst hmls
      exact h4
    | 5 =>
      injection hdecl with hdecl; subst hdecl
      injection hslot with hslot; subst hslot
      injection hmls with hmls; subst hmls
      exact .zstArrayIndirect 4 lm24ThirdMemPlace _
        (fun l hl => (Option.some.inj hl).symm) rfl rfl lm24PU_zstMem5
    | 6 =>
      injection hdecl with hdecl; subst hdecl
      injection hslot with hslot; subst hslot
      injection hmls with hmls; subst hmls
      exact .zstArrayIndirect 4 lm24FourthMemPlace _
        (fun l hl => (Option.some.inj hl).symm) rfl rfl lm24PU_zstMem6
    | 7 =>
      injection hdecl with hdecl; subst hdecl
      injection hslot with hslot; subst hslot
      injection hmls with hmls; subst hmls
      exact .ofUnionLocalRel _ _ h7
    | n + 9 =>
      change (none : Option LocalDecl) = some decl at hdecl
      cases hdecl
  · intro i j mp_i mp_j lay_i lay_j hij hi hj
    match i, j with
    | 1, 1 | 4, 4 | 5, 5 | 6, 6 => exact absurd rfl hij
    | 1, 4 | 1, 5 | 1, 6 | 4, 1 | 4, 5 | 4, 6 | 5, 1 | 5, 4 | 5, 6 | 6, 1 | 6, 4 | 6, 5 =>
      injection hi with hi; injection hi with hvi _; injection hvi with hvi; injection hvi with hvi
      injection hj with hj; injection hj with hvj _; injection hvj with hvj; injection hvj with hvj
      subst hvi hvj
      decide
    | 0, _ | 2, _ | 3, _ | 7, _ | 8, _ => cases hi
    | _, 0 | _, 2 | _, 3 | _, 7 | _, 8 => cases hj
    | n + 9, _ =>
      have hsz : (lm24PUInitMiriFrame b).locals.size = 9 := rfl
      have hlt := (Array.getElem?_eq_some_iff.mp hi).1
      rw [hsz] at hlt; omega
    | _, n + 9 =>
      have hsz : (lm24PUInitMiriFrame b).locals.size = 9 := rfl
      have hlt := (Array.getElem?_eq_some_iff.mp hj).1
      rw [hsz] at hlt; omega

private theorem lm24PU_nodup : LiveAllocsNodup lm24PUMachine := by
  change List.Nodup [witnessAllocId, lm24SecondAllocId, lm24ThirdAllocId, lm24FourthAllocId]
  decide

/-- Concrete instantiation of `step_padded_zst_union_uninhabited_field_read_ub_two_sided`
on `bb4` step 1 of `lm24PUBody` (`_8 = copy (_1.3: VoidZst)`), with all 4 bytes of
`_1` initialized to `0x01020304_u32` (`m4₁` after `_1 = PU { b: 0x01020304_u32 }` in
`lean-miri`, paired via `PaddedZstUnionLocalRel.zstOverlay`). -/
theorem lm24_bb4_uninhabited_two_sided_inst :
    let u32ZstSlot : LocalSlot :=
      .init (.aggregate 0
        ([.unit, .unit, .unit, .unit] ++
          [.aggregate 0
            (encodeRawAbstractByteVals
              (encodeLittleEndianBytes 0x01020304 4 none ++ replicateUninitBytes 0))]))
    let s4₁ := lm24PUAnnealState 4 1
      [.uninit, u32ZstSlot, .uninit, .uninit, .uninit,
       .init (zstArrayVal 4), .init (zstArrayVal 4), .uninit, .uninit]
    let m4₁ := (Miri.Interpreter.Step.step
      (annealStepHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts) ()
      (lm24PUInitMiri 4)).1
    stepMirFn lm24PUBody s4₁ = MirStepNode.fail .ub ∧
    StepRelLM2_4PaddedZst lm24PUBody m4₁ (stepMirFn lm24PUBody s4₁)
      (Miri.Interpreter.Step.step
        (annealStepHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts) () m4₁) := by
  let u32ZstSlot : LocalSlot :=
    .init (.aggregate 0
      ([.unit, .unit, .unit, .unit] ++
        [.aggregate 0
          (encodeRawAbstractByteVals
            (encodeLittleEndianBytes 0x01020304 4 none ++ replicateUninitBytes 0))]))
  let s4₁ := lm24PUAnnealState 4 1
    [.uninit, u32ZstSlot, .uninit, .uninit, .uninit,
     .init (zstArrayVal 4), .init (zstArrayVal 4), .uninit, .uninit]
  let m4₁ := (Miri.Interpreter.Step.step
    (annealStepHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts) ()
    (lm24PUInitMiri 4)).1
  let top4₁ : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
    { lm24PUInitMiriFrame 4 with location := .mir ⟨4, 1⟩ }
  let la4₁ :
      Miri.Memory.LocalAllocation
        AnnealProv (Option Miri.TreeBorrows.BorrowTree) Miri.Memory.MiriMemoryKind :=
    match m4₁.machine.memory.live[0]? with
    | some (_, la) => la
    | none => { kind := .stack, allocation := lm24PUUninitAlloc4 }
  let msc4 := extractExceptOk (translateScalarInt ⟨0x01020304, 4⟩) (by with_unfolding_all rfl)
  have hsc4 : ScalarRel ⟨0x01020304, 4⟩ msc4 :=
    ⟨Or.inr (Or.inr (Or.inl rfl)), by decide, by decide, by with_unfolding_all rfl⟩
  have hframes4₁ : m4₁.stack.frames = #[top4₁] := by with_unfolding_all rfl
  have hst4₁ : StateRelLM2_4PaddedZst lm24PUBody s4₁ m4₁ := by
    refine .mk top4₁ hframes4₁ rfl ⟨_, rfl⟩
      { body_eq := rfl
        location_eq := rfl
        af_locals_len := rfl
        mf_locals_size := rfl
        locals_rel := ?_ }
      rfl rfl rfl rfl rfl ?_
    · intro i decl slot mls hdecl hslot hmls
      match i with
      | 0 | 2 | 3 | 7 | 8 =>
        injection hdecl with hdecl; subst hdecl
        injection hslot with hslot; subst hslot
        injection hmls with hmls; subst hmls
        exact .ofUnionLocalRel _ _ (.base _ _
          (.immediate .uninit .uninit _ (fun l hl => (Option.some.inj hl).symm) (.inl ⟨rfl, rfl⟩)))
      | 1 =>
        injection hdecl with hdecl; subst hdecl
        injection hslot with hslot; subst hslot
        injection hmls with hmls; subst hmls
        exact .zstOverlay 4 4 4 0 2 lm24U32Ty ⟨0x01020304, 4⟩ lm24BaseMemPlace _
          (fun l hl => (Option.some.inj hl).symm) lm24_wt_PU rfl
          (.mk witnessAllocId witnessTag witnessBaseAddr la4₁ msc4
            rfl rfl rfl (by with_unfolding_all exact List.Mem.head _)
            (by with_unfolding_all rfl) rfl (by decide)
            (by with_unfolding_all rfl) (by with_unfolding_all rfl) (by with_unfolding_all rfl)
            (by with_unfolding_all rfl) (by with_unfolding_all rfl) (by with_unfolding_all rfl)
            (by with_unfolding_all rfl) (by decide) (Or.inl (by with_unfolding_all rfl))
            hsc4 (.inr (.inr (.inr ⟨.u32, rfl⟩)))
            (.scalar ⟨0x01020304, 4⟩ msc4 hsc4 rfl nofun nofun)
            (by with_unfolding_all rfl))
      | 4 =>
        injection hdecl with hdecl; subst hdecl
        injection hslot with hslot; subst hslot
        injection hmls with hmls; subst hmls
        exact .uninitIndirect 4 4 4 0 2 lm24Arr2MemPlace _
          (fun l hl => (Option.some.inj hl).symm) lm24_wt_PU rfl
          (.mk lm24SecondAllocId witnessTag lm24SecondBaseAddr
            { kind := .stack, allocation := lm24PUUninitAlloc4 }
            rfl rfl rfl (by with_unfolding_all exact List.Mem.tail _ (List.Mem.head _))
            (by with_unfolding_all rfl) rfl
            (by decide) (by with_unfolding_all rfl) (by with_unfolding_all rfl)
            (by with_unfolding_all rfl) (by with_unfolding_all rfl) (by with_unfolding_all rfl)
            (by with_unfolding_all rfl) (by with_unfolding_all rfl) (by with_unfolding_all rfl))
      | 5 =>
        injection hdecl with hdecl; subst hdecl
        injection hslot with hslot; subst hslot
        injection hmls with hmls; subst hmls
        exact .zstArrayIndirect 4 lm24ThirdMemPlace _
          (fun l hl => (Option.some.inj hl).symm) rfl rfl
          (.mk lm24ThirdAllocId witnessTag lm24ThirdBaseAddr
            { kind := .stack, allocation := lm24ZstArr4Alloc }
            rfl rfl rfl
            (by with_unfolding_all exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
            (by with_unfolding_all rfl) rfl (by with_unfolding_all rfl)
            (by with_unfolding_all rfl) (by with_unfolding_all rfl))
      | 6 =>
        injection hdecl with hdecl; subst hdecl
        injection hslot with hslot; subst hslot
        injection hmls with hmls; subst hmls
        exact .zstArrayIndirect 4 lm24FourthMemPlace _
          (fun l hl => (Option.some.inj hl).symm) rfl rfl
          (.mk lm24FourthAllocId witnessTag lm24FourthBaseAddr
            { kind := .stack, allocation := lm24ZstArr4Alloc }
            rfl rfl rfl
            (by with_unfolding_all
              exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
            (by with_unfolding_all rfl) rfl (by with_unfolding_all rfl)
            (by with_unfolding_all rfl) (by with_unfolding_all rfl))
      | k + 9 => change (none : Option LocalDecl) = some decl at hdecl; cases hdecl
    · intro i j mp_i mp_j lay_i lay_j hij hi hj
      match i, j with
      | 1, 1 | 4, 4 | 5, 5 | 6, 6 => exact absurd rfl hij
      | 1, 4 | 1, 5 | 1, 6 | 4, 1 | 4, 5 | 4, 6 | 5, 1 | 5, 4 | 5, 6 | 6, 1 | 6, 4 | 6, 5 =>
        injection hi with hi; injection hi with hvi _; injection hvi with hvi; injection hvi with hvi
        injection hj with hj; injection hj with hvj _; injection hvj with hvj; injection hvj with hvj
        subst hvi hvj; decide
      | 0, _ | 2, _ | 3, _ | 7, _ | 8, _ => cases hi
      | _, 0 | _, 2 | _, 3 | _, 7 | _, 8 => cases hj
      | k + 9, _ =>
        have hlt := (Array.getElem?_eq_some_iff.mp hi).1
        have hsz : (lm24PUInitMiriFrame 4).locals.size = 9 := rfl
        rw [hsz] at hlt; omega
      | _, k + 9 =>
        have hlt := (Array.getElem?_eq_some_iff.mp hj).1
        have hsz : (lm24PUInitMiriFrame 4).locals.size = 9 := rfl
        rw [hsz] at hlt; omega
  exact step_padded_zst_union_uninhabited_field_read_ub_two_sided hst4₁ nofun rfl rfl rfl rfl
    (by decide) rfl rfl (by decide) (by decide) (by decide) rfl rfl rfl
    rfl rfl rfl rfl (by decide) (.inr ⟨_, rfl⟩) (.inr ⟨rfl, nofun, nofun⟩) rfl
    (.inl rfl) (mp_u := lm24BaseMemPlace) rfl (fun tf htf => by
      rw [hframes4₁] at htf
      cases Array.singleton_inj.mp htf
      exact ⟨some (translateTy lm24PUTy lm24PULayouts), rfl⟩)

/-- **Two-sided general uninitialized scalar payload read UB (`R-a`, `kani#5176`)**:
For any `StateRelLM2_4PaddedZst body s m` where `_u` is a `[(); N]`-initialized
all-uninit padded union (`PaddedZstUnionLocalRel.zstUninit`) and field `j < n`
is a primitive integer scalar `scTy` of width `w` (`ValidScalarBytes w`, `w ≤ S`),
derives **both** `stepMirFn body s = MirStepNode.fail .ub` in Anneal **and**
`Step.step (annealStepHooksLM2_4PaddedZst ..) () m = (m', .error (.undefinedBehavior "read of uninitialized memory field"))`
in `lean-miri` (via vendored `ValidityVisitor.validatePlace` calling
`annealReadImmediateLM2_2`), establishing `StepRelLM2_4PaddedZst.ub`. -/
theorem step_padded_zst_union_uninit_payload_read_ub_two_sided
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_4PaddedZst body s m)
    (hnodup : LiveAllocsNodup m.machine)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {r u j S n N f_z zstFlIdx w : Nat}
    {scTy : Ty} {signed : Bool} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨r, .nil⟩ (.use (.copy ⟨u, [.field j scTy]⟩)), span⟩)
    {rDecl uDecl : LocalDecl}
    (hdecl_r : get? body.localDecls r = some rDecl)
    (hdecl_u : get? body.localDecls u = some uDecl)
    (hru : r ≠ u)
    (hwt : WellTypedPaddedZstUnionTy body.layouts uDecl.ty S N f_z zstFlIdx)
    (hfields : (translateTy uDecl.ty body.layouts).layout.fields = .Union n)
    (hj_lt : j < n)
    (hw : ValidScalarBytes w) (hwS : w ≤ S)
    (hInt : (∃ wk, scTy.kind = .uint wk) ∨ (∃ wk, scTy.kind = .int wk))
    (hflay : translateTy scTy body.layouts =
      { ty := encodeTyId scTy, layout := scalarLayoutData w signed })
    (hSz_a : ∀ l, LayoutTable.lookup body.layouts
        (resolveTyWithLocalDecls body.localDecls body.layouts uDecl.ty).layoutIdx = some l →
      tyByteSize body.localDecls body.layouts
        (unionFieldReadTyLM2_4 body.localDecls body.layouts l j scTy) = some w)
    (hres_u : resolveTyWithLocalDecls body.localDecls body.layouts uDecl.ty = uDecl.ty)
    {mp_u : Miri.Interpreter.MemPlace AnnealProv}
    (hu_slot : get? s.frame.locals u = some (.init (.aggregate 0 (List.replicate n .unit))))
    (hu_ind : ∀ tf, m.stack.frames = #[tf] → ∃ c, tf.locals[u]? = some ⟨.live (.indirect mp_u), c⟩)
    (hmem : PaddedZstUnionUninitMemRel m.machine uDecl.ty body.layouts S mp_u) :
    stepMirFn body s = MirStepNode.fail .ub ∧
    StepRelLM2_4PaddedZst body m (stepMirFn body s)
      (Miri.Interpreter.Step.step
        (annealStepHooksLM2_4PaddedZst body.localDecls body.layouts) () m) := by
  rcases hstate with ⟨topFrame, hframes, _, _, hframe, hcal, _, _, _, _, _⟩
  obtain ⟨defPath, args, tl, n', _, hk, _, _, hlookup, hfu, _, huninh, htl_sz, _, _, _,
    _, _, _, _, _, _, _, _⟩ := hwt.adt_spec
  have hn_eq : n' = n := by
    unfold translateTy at hfields; dsimp only at hfields
    rw [hk, hlookup] at hfields
    dsimp only [translateTypeLayout, translateFieldsShape] at hfields
    rw [hfu] at hfields; cases hfields; rfl
  subst hn_eq
  have hw_pos : ∃ w0, w = w0 + 1 := by
    rcases hw with rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩
  obtain ⟨w0, hw_eq⟩ := hw_pos
  have hstep_a : stepMirFn body s = MirStepNode.fail .ub := by
    rw [stepMirFn_eq_of_not_other body s hcal hphase]
    simp only [hbb, hstmt]
    have hKind : (resolveTyWithLocalDecls body.localDecls body.layouts uDecl.ty).kind =
        .adt defPath args := by rw [hres_u]; exact hk
    have hLookup' : LayoutTable.lookup body.layouts
        (resolveTyWithLocalDecls body.localDecls body.layouts uDecl.ty).layoutIdx = some tl := by
      rw [hres_u]; exact hlookup
    have hEnc : encodeByLayoutIdxAux 8 body.layouts
        (resolveTyWithLocalDecls body.localDecls body.layouts uDecl.ty).layoutIdx
        (.aggregate 0 (List.replicate n' .unit)) = some (replicateUninitBytes S) := by
      rw [hres_u]; exact encodeByLayoutIdxAux_union_allUnits hwt hfields 7
    have hSz' : tyByteSize body.localDecls body.layouts
        (unionFieldReadTyLM2_4 body.localDecls body.layouts tl j scTy) = some (w0 + 1) := by
      rw [← hw_eq]; exact hSz_a tl hLookup'
    have hK := tyByteSize_succ_kind_lm24 body.localDecls body.layouts _ w0 hSz'
    rw [unionFieldReadTyLM2_4_kind] at hK
    have hLe' : w0 + 1 ≤ (replicateUninitBytes S).length := by
      rw [replicateUninitBytes_eq_replicate_lm24, List.length_replicate, ← hw_eq]; exact hwS
    have hTake : (replicateUninitBytes S).take (w0 + 1) = List.replicate (w0 + 1) .uninit := by
      rw [replicateUninitBytes_eq_replicate_lm24, List.take_replicate,
        Nat.min_eq_left (by omega)]
    have hIntR : (∃ wk, (unionFieldReadTyLM2_4 body.localDecls body.layouts tl j scTy).kind = .uint wk) ∨
        (∃ wk, (unionFieldReadTyLM2_4 body.localDecls body.layouts tl j scTy).kind = .int wk) := by
      rw [unionFieldReadTyLM2_4_kind]; exact hInt
    have hDecNone : decodeTypedValueFromBytes defaultCodecFuel body.layouts
        (unionFieldReadTyLM2_4 body.localDecls body.layouts tl j scTy)
        ((replicateUninitBytes S).take (w0 + 1)) = none := by
      rw [hTake]; exact decodeTypedValueFromBytes_int_uninit_lm24 body.layouts _ w0 hIntR
    have hread := readUnion_posField_offset0_none_lm24 s.frame.locals body.localDecls body.layouts
      uDecl.ty scTy (List.replicate n' .unit) j n' tl defPath args hKind hLookup' hfu hj_lt
      (.inr ⟨get?_replicate_unit_lm24 n' j hj_lt, hK.1, hK.2⟩) (replicateUninitBytes S) hEnc w0
      hSz' hInt hLe' hDecNone
    have htch := placeTouchesUnion_field_of_union_lm24 body.localDecls body.layouts u j n'
      uDecl scTy [] tl defPath args hdecl_u hKind hLookup' hfu
    unfold evalStmt evalRvalue evalOperand readProjectedForLocal
    dsimp only
    rw [hu_slot, htch, hdecl_u]
    dsimp only
    rw [hread]
  -- `lean-miri` side:
  have hun_u : isUnionLocal body.localDecls body.layouts u = true :=
    isUnionLocal_of_wellTypedPaddedZst hdecl_u hwt
  obtain ⟨_, mls_r, _, hlt_r, _, _, hmls_r_eq, hloc_r⟩ := hframe.lookup_local hdecl_r
  obtain ⟨_, mls_u, _, hlt_u, _, hmls_u', _, hloc_u⟩ := hframe.lookup_local hdecl_u
  obtain ⟨uC, hmls_u⟩ := hu_ind topFrame hframes
  rw [hmls_u] at hmls_u'; injection hmls_u' with hmls_u'; subst hmls_u'
  let layR := translateTy rDecl.ty body.layouts
  let layU := translateTy uDecl.ty body.layouts
  let topFrame₀ := cacheFrameLocalLayout topFrame r hlt_r layR
  let m₀ : AnnealStepState := { m with stack := ⟨#[topFrame₀]⟩ }
  let destPlace : Miri.Interpreter.RuntimePlace AnnealProv :=
    ⟨.local 0 r none topFrame.localsIdentity, layR⟩
  have hevalPlace : (annealRvalueHooksLM2_4PaddedZst body.localDecls body.layouts).evalPlace ()
      ⟨r, #[]⟩ true m = .ok destPlace m₀ :=
    annealEvalPlace_unprojected hframes hlt_r hdecl_r (by rw [hmls_r_eq]; exact hloc_r.layout_eq)
  have hframes₀ : m₀.stack.frames = #[topFrame₀] := rfl
  have hlt_u₀ : u < topFrame₀.locals.size := by
    dsimp only [topFrame₀]; rw [cacheFrameLocalLayout_size]; exact hlt_u
  have hmls_u₀ : topFrame₀.locals[u]'hlt_u₀ = ⟨.live (.indirect mp_u), uC⟩ := by
    have h := Array.getElem?_eq_getElem hlt_u₀
    dsimp only [topFrame₀, cacheFrameLocalLayout] at h ⊢
    rw [Array.getElem?_set_ne _ hru, hmls_u] at h
    exact (Option.some.inj h).symm
  let topFrame₁ := cacheFrameLocalLayout topFrame₀ u hlt_u₀ layU
  let m₀' : AnnealStepState := { m₀ with stack := ⟨#[topFrame₁]⟩ }
  have hprim : IsPrimScalarTy scTy := by
    rcases hInt with ⟨ut, h⟩ | ⟨it, h⟩
    · exact .inr (.inr (.inr ⟨ut, h⟩))
    · exact .inr (.inr (.inl ⟨it, h⟩))
  have hnotArr : (annealEvalOperandLM2_4PaddedZst.unionZstArrayElemCount?
      body.layouts (encodeTyId scTy)).isSome = false := by
    unfold annealEvalOperandLM2_4PaddedZst.unionZstArrayElemCount? encodeTyId
    rcases hInt with ⟨ut, h⟩ | ⟨it, h⟩
    · rw [h]; cases ut <;> rfl
    · rw [h]; cases it <;> rfl
  have hclassInt : annealUnionValidityClassify body.layouts (encodeTyId scTy) m₀' =
      .ok .integer m₀' := by
    unfold annealUnionValidityClassify encodeTyId
    rcases hInt with ⟨ut, h⟩ | ⟨it, h⟩
    · rw [h]; cases ut <;> rfl
    · rw [h]; cases it <;> rfl
  have hmeta : mp_u.metadata = .none := by
    cases hmem with
    | mk _ _ _ _ _ _ hm _ _ _ _ _ _ _ _ _ _ _ => exact hm
  have hfield : annealEvalUnionField body.localDecls body.layouts u j (encodeTyId scTy) m₀ =
      .ok ⟨.indirect mp_u, translateTy scTy body.layouts⟩ m₀' :=
    annealEvalUnionField_indirect (body := body) (m := m₀) hframes₀ hlt_u₀ hdecl_u
      (by rw [hmls_u₀]; exact hloc_u.layout_eq) (by rw [hmls_u₀]) hmeta hfields hj_lt hprim
  have hop : (annealRvalueHooksLM2_4PaddedZst body.localDecls body.layouts).evalOperandAt ()
      (Miri.Interpreter.OperandPath.rvalue "operand")
      (translateOperand (.copy ⟨u, [.field j scTy]⟩))
      (some ((annealRvalueHooksLM2_4PaddedZst body.localDecls body.layouts).placeLayout destPlace)) m₀ =
      .ok ⟨.indirect mp_u, translateTy scTy body.layouts⟩ m₀' := by
    dsimp only [annealRvalueHooksLM2_4PaddedZst, translateOperand]
    rw [(annealEvalOperandLM2_4PaddedZst_eq_of_non_zstArray_field body.localDecls body.layouts
      (translatePlace ⟨u, [.field j scTy]⟩) j (encodeTyId scTy) _ rfl hnotArr).1]
    simp only [translatePlace, List.map, translateProjectionElem, List.toArray,
      annealEvalOperandLM2_4, hun_u, ↓reduceIte]
    exact hfield
  have hread_err : annealReadImmediateLM2_2 ⟨.indirect mp_u, translateTy scTy body.layouts⟩ m₀' =
      .error (.undefinedBehavior "read of uninitialized memory field") m₀' := by
    rw [hflay]
    exact (step_padded_zst_union_uninit_payload_read_ub (body := body) (m := m₀')
      hnodup hwt hfields hw hwS hmem (tyId := encodeTyId scTy)).2
  have hval_err : annealValidateOpLM2_4PaddedZst body.layouts
      ⟨.indirect mp_u, translateTy scTy body.layouts⟩ m₀' =
      .error (.undefinedBehavior "read of uninitialized memory field") m₀' := by
    have hvis :
        Miri.Interpreter.ValidityVisitor.visit (annealUnionValidityHooks body.layouts)
          ⟨.indirect mp_u, translateTy scTy body.layouts⟩ 4
          { path := { originalType := "" }, flags := {}, ctfeMode := none,
            refTracking := none, dataBytes := none }
          ⟨.memory mp_u, translateTy scTy body.layouts⟩ m₀' =
        .error (.undefinedBehavior "read of uninitialized memory field") m₀' := by
      unfold Miri.Interpreter.ValidityVisitor.visit
      rw [EStateM.bind_eq_ok (by
        dsimp only [annealUnionValidityHooks]
        rw [show (translateTy scTy body.layouts).ty = encodeTyId scTy by rw [hflay]]
        exact hclassInt)]
      refine EStateM.bind_eq_error ?_
      with_unfolding_all
        exact EStateM.bind_eq_error hread_err
    unfold annealValidateOpLM2_4PaddedZst Miri.Interpreter.ValidityVisitor.validatePlace
    have htn : (annealUnionValidityHooks body.layouts).typeName
        ⟨.indirect mp_u, translateTy scTy body.layouts⟩ (translateTy scTy body.layouts).ty m₀' =
        .ok "" m₀' := rfl
    have hgw : ∀ {A} (act : EStateM Miri.Interpreter.StepError AnnealStepState A),
        (annealUnionValidityHooks body.layouts).withGhostValidation act = act := fun _ => rfl
    simp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure, htn, hgw,
      Bool.false_eq_true, ↓reduceIte, hvis]
  have hlm24 : lm24Assign body.localDecls body.layouts ⟨r, #[]⟩
      (translateRvalue (.use (.copy ⟨u, [.field j scTy]⟩))) = true := by
    simp [lm24Assign, lm24Rvalue, lm24Operand, lm24Place, translateRvalue, translateOperand,
      translatePlace, hun_u]
  have hm_stmt : Miri.Interpreter.Step.evalStatement
      (annealStepHooksLM2_4PaddedZst body.localDecls body.layouts) ()
      (translateStmt ⟨.assign ⟨r, .nil⟩ (.use (.copy ⟨u, [.field j scTy]⟩)), span⟩) m =
      (m₀', .error (.undefinedBehavior "read of uninitialized memory field")) := by
    unfold Miri.Interpreter.Step.evalStatement translateStmt
    dsimp only [translateStmtKind, translatePlace, List.map, List.toArray]
    simp only [annealStepHooksLM2_4PaddedZst, hlm24, ↓reduceIte]
    unfold Miri.Interpreter.runRvalue Miri.Interpreter.evalRvalueIntoPlace
    rw [EStateM.bind_eq_ok hevalPlace]
    dsimp only [translateRvalue]
    rw [EStateM.bind_eq_ok hop]
    dsimp only [annealRvalueHooksLM2_4PaddedZst, annealRvalueHooksLM2_4, annealRvalueHooksLM2_2,
      annealRvalueHooks]
    rw [EStateM.bind_eq_error hval_err]
  have hstep_m := miri_step_at_statement_error
    (annealStepHooksLM2_4PaddedZst body.localDecls body.layouts)
    hframes hframe.body_eq hframe.location_eq hbb hstmt hm_stmt
  refine ⟨hstep_a, ?_⟩
  rw [hstep_a, hstep_m]
  exact .ub m₀' "read of uninitialized memory field"

/-- Concrete instantiation of `step_padded_zst_union_uninit_payload_read_ub_two_sided`
on `bb0` step 3 of `lm24PUBody` (`_2 = copy (_4.1: u8)`). -/
theorem lm24_bb0_uninit_payload_two_sided_inst :
    let s0₃ := lm24PUAnnealState 0 3
      [.uninit, lm24PUZstSlot, .uninit, .uninit, lm24PUZstSlot,
       .init (zstArrayVal 4), .init (zstArrayVal 4), .uninit, .uninit]
    stepMirFn lm24PUBody s0₃ = MirStepNode.fail .ub ∧
    StepRelLM2_4PaddedZst lm24PUBody (lm24PUMiriAt 0 3) (stepMirFn lm24PUBody s0₃)
      (Miri.Interpreter.Step.step
        (annealStepHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts) ()
        (lm24PUMiriAt 0 3)) := by
  have hst0₃ := lm24PUMiriAt_stateRel 0 3 lm24PUZstSlot lm24PUZstSlot .uninit
    (.zstUninit 4 4 4 0 2 lm24BaseMemPlace _ (fun l hl => (Option.some.inj hl).symm)
      lm24_wt_PU rfl lm24PU_uninitMem1)
    (.zstUninit 4 4 4 0 2 lm24Arr2MemPlace _ (fun l hl => (Option.some.inj hl).symm)
      lm24_wt_PU rfl lm24PU_uninitMem4)
    (.base _ _ (.immediate .uninit .uninit _ (fun l hl => (Option.some.inj hl).symm)
      (.inl ⟨rfl, rfl⟩)))
  exact step_padded_zst_union_uninit_payload_read_ub_two_sided hst0₃
    lm24PU_nodup nofun rfl rfl rfl rfl (by decide)
    lm24_wt_PU rfl (by decide) (Or.inl rfl) (by decide) (Or.inl ⟨.u8, rfl⟩)
    (w := 1) (signed := false) rfl
    (fun l hl => by injection hl with hl; subst hl; rfl) rfl rfl
    (mp_u := lm24Arr2MemPlace)
    (fun tf htf => by cases Array.singleton_inj.mp htf; exact ⟨_, rfl⟩)
    lm24PU_uninitMem4

/-- **Two-sided general well-formed out-of-bounds `[(); N]` union element read UB (`R-a`)**:
When `offset < minLen` and `N < minLen` (`N, minLen < 2^64`), derives **both**
`stepMirFn body s = MirStepNode.fail .ub` in Anneal (via
`readUnion_zeroByte_fieldRoot_lm24`, without assuming `hstep_a`) **and**
`Step.step (annealStepHooksLM2_4PaddedZst ..) () m = (m', .error (.undefinedBehavior s!"bounds check failed: index {UInt64.ofNat N} >= len {UInt64.ofNat minLen}"))`
in `lean-miri` via vendored `Miri.Interpreter.projectField` +
`Miri.Interpreter.projectConstantIndex`, establishing `StepRelLM2_4PaddedZst.ub`. -/
theorem step_padded_zst_union_elem_index_oob_ub_two_sided
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_4PaddedZst body s m)
    (hnodup : LiveAllocsNodup m.machine)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {r u S n N f_z zstFlIdx offset minLen : Nat}
    {zstArrTy : Ty} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨r, .nil⟩
        (.use (.copy ⟨u, [.field f_z zstArrTy, .constantIndex offset minLen false]⟩)), span⟩)
    {rDecl uDecl : LocalDecl}
    (hdecl_r : get? body.localDecls r = some rDecl)
    (hdecl_u : get? body.localDecls u = some uDecl)
    (hru : r ≠ u)
    (hwt : WellTypedPaddedZstUnionTy body.layouts uDecl.ty S N f_z zstFlIdx)
    (hfields : (translateTy uDecl.ty body.layouts).layout.fields = .Union n)
    (hfz_lt : f_z < n)
    (hcnt : annealEvalOperandLM2_4PaddedZst.unionZstArrayElemCount?
      body.layouts (encodeTyId zstArrTy) = some N)
    (hfKind : zstArrTy.kind = .array (.tuple []) N)
    (hWf : offset < minLen)
    (hoob : N < minLen)
    (hN64 : N < 2 ^ 64)
    (hMin64 : minLen < 2 ^ 64)
    (hres_u : resolveTyWithLocalDecls body.localDecls body.layouts uDecl.ty = uDecl.ty)
    {fields : List Value}
    (hu_slot : get? s.frame.locals u = some (.init (.aggregate 0 fields)))
    (hImg : UnionImageOkLM2_4 body.layouts
      (resolveTyWithLocalDecls body.localDecls body.layouts uDecl.ty).layoutIdx n fields)
    (hSlot : UnionSlotInactiveLM2_4 fields f_z zstArrTy.kind)
    (hSz0 : ∀ l, LayoutTable.lookup body.layouts
        (resolveTyWithLocalDecls body.localDecls body.layouts uDecl.ty).layoutIdx = some l →
      tyByteSize body.localDecls body.layouts
        (unionFieldReadTyLM2_4 body.localDecls body.layouts l f_z zstArrTy) = some 0)
    (hInhF : ∀ l, LayoutTable.lookup body.layouts
        (resolveTyWithLocalDecls body.localDecls body.layouts uDecl.ty).layoutIdx = some l →
      tyIsUninhabited body.layouts
        (unionFieldReadTyLM2_4 body.localDecls body.layouts l f_z zstArrTy) = false)
    (hZeroV : ∀ l, LayoutTable.lookup body.layouts
        (resolveTyWithLocalDecls body.localDecls body.layouts uDecl.ty).layoutIdx = some l →
      ∃ elems, zeroByteValueLM2_4 body.layouts
          (unionFieldReadTyLM2_4 body.localDecls body.layouts l f_z zstArrTy) =
        .aggregate 0 elems ∧ elems.length = N)
    {mp_u : Miri.Interpreter.MemPlace AnnealProv}
    {allocId : Miri.Memory.AllocId} {tag : Miri.Memory.BorTag} {baseAddr : UInt64}
    {la : Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
      Miri.Memory.MiriMemoryKind}
    (hmeta : mp_u.metadata = .none)
    (hprov : mp_u.ptr.provenance = some (.concrete allocId tag))
    (hlive : (allocId, la) ∈ m.machine.memory.live.toList)
    (hbase : m.machine.lookupBaseAddr allocId = some baseAddr)
    (hu_ind : ∀ tf, m.stack.frames = #[tf] → ∃ c, tf.locals[u]? = some ⟨.live (.indirect mp_u), c⟩) :
    stepMirFn body s = MirStepNode.fail .ub ∧
    StepRelLM2_4PaddedZst body m (stepMirFn body s)
      (Miri.Interpreter.Step.step
        (annealStepHooksLM2_4PaddedZst body.localDecls body.layouts) () m) := by
  have hstep_a : stepMirFn body s = MirStepNode.fail .ub := by
    rcases hstate with ⟨_, _, _, _, _, hcal, _, _, _, _, _⟩
    obtain ⟨defPath, args, tl, n', _, hk, _, _, hlookup, hfu, _, _, _, _, _, _,
      _, _, _, _, _, _, _, _⟩ := hwt.adt_spec
    have hn_eq : n' = n := by
      unfold translateTy at hfields; dsimp only at hfields
      rw [hk, hlookup] at hfields
      dsimp only [translateTypeLayout, translateFieldsShape] at hfields
      rw [hfu] at hfields; cases hfields; rfl
    subst hn_eq
    rw [stepMirFn_eq_of_not_other body s hcal hphase]
    simp only [hbb, hstmt]
    have hKind : (resolveTyWithLocalDecls body.localDecls body.layouts uDecl.ty).kind =
        .adt defPath args := by rw [hres_u]; exact hk
    have hLookup' : LayoutTable.lookup body.layouts
        (resolveTyWithLocalDecls body.localDecls body.layouts uDecl.ty).layoutIdx = some tl := by
      rw [hres_u]; exact hlookup
    let fTy := unionFieldReadTyLM2_4 body.localDecls body.layouts tl f_z zstArrTy
    have hfResKind : (resolveTyWithLocalDecls body.localDecls body.layouts fTy).kind =
        .array (.tuple []) N := by
      rw [resolveTyWithLocalDecls_kind_lm24, unionFieldReadTyLM2_4_kind, hfKind]
    have hble : Nat.ble minLen N = false :=
      Bool.eq_false_iff.mpr (fun h => by have := Nat.ble_eq.mp h; omega)
    have hBounds : checkStaticSubProjBounds body.localDecls body.layouts fTy
        [.constantIndex offset minLen false] = false := by
      unfold checkStaticSubProjBounds
      dsimp only
      rw [hfResKind]
      dsimp only
      rw [hble]
      rfl
    have hroot := readUnion_zeroByte_fieldRoot_lm24 s.frame.locals body.localDecls body.layouts
      uDecl.ty zstArrTy fields f_z n' tl defPath args hKind hLookup' hfu hfz_lt hImg hSlot
      (hSz0 tl hLookup') (hInhF tl hLookup') (.constantIndex offset minLen false) []
      [.constantIndex offset minLen false] rfl hBounds
    obtain ⟨elems, hzv, helen⟩ := hZeroV tl hLookup'
    rw [hzv] at hroot
    have hleaf : readProjectedValueUnionAware s.frame.locals body.localDecls body.layouts
        (.aggregate 0 elems) fTy [.constantIndex offset minLen false] = .ub := by
      unfold readProjectedValueUnionAware
      simp only []
      rw [length_eq_list_length_lm24 elems, helen, hble]
      rfl
    rw [hleaf] at hroot
    have htch := placeTouchesUnion_field_of_union_lm24 body.localDecls body.layouts u f_z n'
      uDecl zstArrTy [.constantIndex offset minLen false] tl defPath args
      hdecl_u hKind hLookup' hfu
    unfold evalStmt evalRvalue evalOperand readProjectedForLocal
    dsimp only
    rw [hu_slot, htch, hdecl_u]
    dsimp only
    rw [hroot]
  exact ⟨hstep_a,
    (step_padded_zst_union_elem_index_read_simulation hstate hnodup hbb hstmt hdecl_r hdecl_u hru
      hwt hfields hfz_lt hcnt hWf hN64 hMin64 hmeta hprov hlive hbase hu_ind).1 hoob hstep_a⟩

/-- Concrete instantiation of `step_padded_zst_union_elem_index_oob_ub_two_sided`
on `bb3` step 2 of `lm24PUBody` (`_7 = copy (_1.0[4 of 5]: ())`). -/
theorem lm24_bb3_elem_index_oob_two_sided_inst :
    let s3₂ := lm24PUAnnealState 3 2
      [.uninit, lm24PUZstSlot, .uninit, .uninit, .uninit,
       .init (zstArrayVal 4), .init (zstArrayVal 4), .init zstUnitVal, .uninit]
    stepMirFn lm24PUBody s3₂ = MirStepNode.fail .ub ∧
    StepRelLM2_4PaddedZst lm24PUBody (lm24PUMiriAt 3 2) (stepMirFn lm24PUBody s3₂)
      (Miri.Interpreter.Step.step
        (annealStepHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts) ()
        (lm24PUMiriAt 3 2)) := by
  have hst3₂ := lm24PUMiriAt_stateRel 3 2 lm24PUZstSlot .uninit (.init zstUnitVal)
    (.zstUninit 4 4 4 0 2 lm24BaseMemPlace _ (fun l hl => (Option.some.inj hl).symm)
      lm24_wt_PU rfl lm24PU_uninitMem1)
    (.uninitIndirect 4 4 4 0 2 lm24Arr2MemPlace _ (fun l hl => (Option.some.inj hl).symm)
      lm24_wt_PU rfl lm24PU_uninitMem4)
    (.base _ _ (.immediate (.init zstUnitVal) .uninit _
      (fun l hl => (Option.some.inj hl).symm) (.inr ⟨.unit, rfl, .unit rfl⟩)))
  exact step_padded_zst_union_elem_index_oob_ub_two_sided hst3₂
    lm24PU_nodup nofun rfl rfl rfl rfl (by decide)
    lm24_wt_PU rfl (by decide) rfl rfl (by decide) (by decide) (by decide) (by decide) rfl rfl
    (.inr ⟨replicateUninitBytes 4, rfl⟩)
    (.inr ⟨rfl, nofun, nofun⟩)
    (fun l hl => by injection hl with hl; subst hl; rfl)
    (fun l hl => by injection hl with hl; subst hl; rfl)
    (fun l hl => by
      injection hl with hl; subst hl
      exact ⟨List.replicate 4 zstUnitVal, rfl, rfl⟩)
    rfl rfl (List.Mem.head _) (by with_unfolding_all rfl)
    (fun tf htf => by cases Array.singleton_inj.mp htf; exact ⟨_, rfl⟩)

set_option maxRecDepth 200000 in
/-- **Kernel-checked never-written (`.uninit`) union 0-byte field read boundary (`R-b`)**:
At `bb5` statement `3` of `lm24PUBody` (`_6 = copy (_1.0: [(); 4])`), where union
`_1 : PU` holds `LocalSlot.uninit` in Anneal (`s5₃`):
1. After `StorageDead(_1); StorageLive(_1)` in `lean-miri` (`m5₃_imm`), `_1` holds
   `.live (.immediate .uninit)` (related to `s5₃` by `StateRelLM2_4PaddedZst` via
   `UnionLocalRel.base`), and **both** Anneal (`stepMirFn = .fail .ub`) and
   `lean-miri` (`"field read of uninitialized union"`, under both
   `annealStepHooksLM2_4PaddedZst` and `annealStepHooksLM2_4`) fault
   (`StepRelLM2_4PaddedZst.ub`);
2. When `_1` instead already points to 4-byte uninitialized stack storage
   (`m5₃_ind := lm24PUMiriAt 5 3`, matching real Miri's eager `StorageLive`
   allocation and MiniRust's `evalValue_load_union_zstArray_field`, and also
   related to `s5₃` by `StateRelLM2_4PaddedZst` via
   `PaddedZstUnionLocalRel.uninitIndirect`), `lean-miri` **accepts** the 0-byte
   `[(); 4]` field read (`.ok true` under both `annealStepHooksLM2_4PaddedZst`
   and `annealStepHooksLM2_4`), whereas Anneal faults (`stepMirFn = .fail .ub`)
   because `MirSemantics.evalOperand` rejects every projection on `LocalSlot.uninit`. -/
theorem lm24_never_written_union_zst_read_boundary :
    let s5₃ := lm24PUAnnealState 5 3
      [.uninit, .uninit, .uninit, .uninit, .uninit,
       .init (zstArrayVal 4), .init (zstArrayVal 4), .uninit, .uninit]
    let m5₃_imm : AnnealStepState :=
      { stack := ⟨#[{ lm24PUInitMiriFrame 5 with
          locals := (lm24PUInitMiriFrame 5).locals.set! 1
            { value := .live (.immediate .uninit),
              layout := some (translateTy lm24PUTy lm24PULayouts) },
          location := .mir ⟨5, 3⟩ }]⟩
        machine := { lm24PUMachine with
          memory := deallocLocalMemory lm24PUMachine.memory
            (.live (.indirect lm24BaseMemPlace)) } }
    let m5₃_ind := lm24PUMiriAt 5 3
    let hooks := annealStepHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts
    let hooks_base := annealStepHooksLM2_4 lm24PUBody.localDecls lm24PUBody.layouts
    -- (1) Post-`StorageLive` immediate `.uninit` state: related and both fault (`StepRelLM2_4PaddedZst.ub`)
    StateRelLM2_4PaddedZst lm24PUBody s5₃ m5₃_imm ∧
    stepMirFn lm24PUBody s5₃ = MirStepNode.fail .ub ∧
    (Miri.Interpreter.Step.step hooks () m5₃_imm).2 =
      .error (.undefinedBehavior "field read of uninitialized union") ∧
    (Miri.Interpreter.Step.step hooks_base () m5₃_imm).2 =
      .error (.undefinedBehavior "field read of uninitialized union") ∧
    StepRelLM2_4PaddedZst lm24PUBody m5₃_imm (stepMirFn lm24PUBody s5₃)
      (Miri.Interpreter.Step.step hooks () m5₃_imm) ∧
    -- (2) Eagerly storage-allocated uninitialized union state (`uninitIndirect`):
    -- related by `StateRelLM2_4PaddedZst`, `lean-miri` accepts `.ok true` while Anneal faults
    StateRelLM2_4PaddedZst lm24PUBody s5₃ m5₃_ind ∧
    (Miri.Interpreter.Step.step hooks () m5₃_ind).2 = .ok true ∧
    (Miri.Interpreter.Step.step hooks_base () m5₃_ind).2 = .ok true := by
  let s5₃ := lm24PUAnnealState 5 3
    [.uninit, .uninit, .uninit, .uninit, .uninit,
     .init (zstArrayVal 4), .init (zstArrayVal 4), .uninit, .uninit]
  let m5₃_imm : AnnealStepState :=
    { stack := ⟨#[{ lm24PUInitMiriFrame 5 with
        locals := (lm24PUInitMiriFrame 5).locals.set! 1
          { value := .live (.immediate .uninit),
            layout := some (translateTy lm24PUTy lm24PULayouts) },
        location := .mir ⟨5, 3⟩ }]⟩
      machine := { lm24PUMachine with
        memory := deallocLocalMemory lm24PUMachine.memory
          (.live (.indirect lm24BaseMemPlace)) } }
  let hooks := annealStepHooksLM2_4PaddedZst lm24PUBody.localDecls lm24PUBody.layouts
  have hst_imm : StateRelLM2_4PaddedZst lm24PUBody s5₃ m5₃_imm := by
    refine .mk m5₃_imm.stack.frames[0] rfl rfl ⟨_, rfl⟩
      { body_eq := rfl
        location_eq := rfl
        af_locals_len := rfl
        mf_locals_size := rfl
        locals_rel := ?_ }
      rfl rfl rfl rfl rfl ?_
    · intro i decl slot mls hdecl hslot hmls
      match i with
      | 0 | 1 | 2 | 3 | 7 | 8 =>
        injection hdecl with hdecl; subst hdecl
        injection hslot with hslot; subst hslot
        injection hmls with hmls; subst hmls
        exact .ofUnionLocalRel _ _ (.base _ _
          (.immediate .uninit .uninit _ (fun l hl => (Option.some.inj hl).symm) (.inl ⟨rfl, rfl⟩)))
      | 4 =>
        injection hdecl with hdecl; subst hdecl
        injection hslot with hslot; subst hslot
        injection hmls with hmls; subst hmls
        exact .uninitIndirect 4 4 4 0 2 lm24Arr2MemPlace _
          (fun l hl => (Option.some.inj hl).symm) lm24_wt_PU rfl
          (.mk lm24SecondAllocId witnessTag lm24SecondBaseAddr
            { kind := .stack, allocation := lm24PUUninitAlloc4 }
            rfl rfl rfl (by with_unfolding_all exact List.Mem.head _)
            (by with_unfolding_all rfl) rfl (by decide)
            (by with_unfolding_all rfl) (by with_unfolding_all rfl)
            (by with_unfolding_all rfl) (by with_unfolding_all rfl)
            (by with_unfolding_all rfl) (by with_unfolding_all rfl)
            (by with_unfolding_all rfl) (by with_unfolding_all rfl))
      | 5 =>
        injection hdecl with hdecl; subst hdecl
        injection hslot with hslot; subst hslot
        injection hmls with hmls; subst hmls
        exact .zstArrayIndirect 4 lm24ThirdMemPlace _
          (fun l hl => (Option.some.inj hl).symm) rfl rfl
          (.mk lm24ThirdAllocId witnessTag lm24ThirdBaseAddr
            { kind := .stack, allocation := lm24ZstArr4Alloc }
            rfl rfl rfl (by with_unfolding_all exact List.Mem.tail _ (List.Mem.head _))
            (by with_unfolding_all rfl) rfl
            (by with_unfolding_all rfl) (by with_unfolding_all rfl)
            (by with_unfolding_all rfl))
      | 6 =>
        injection hdecl with hdecl; subst hdecl
        injection hslot with hslot; subst hslot
        injection hmls with hmls; subst hmls
        exact .zstArrayIndirect 4 lm24FourthMemPlace _
          (fun l hl => (Option.some.inj hl).symm) rfl rfl
          (.mk lm24FourthAllocId witnessTag lm24FourthBaseAddr
            { kind := .stack, allocation := lm24ZstArr4Alloc }
            rfl rfl rfl
            (by with_unfolding_all exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
            (by with_unfolding_all rfl) rfl
            (by with_unfolding_all rfl) (by with_unfolding_all rfl)
            (by with_unfolding_all rfl))
      | n + 9 =>
        change (none : Option LocalDecl) = some decl at hdecl
        cases hdecl
    · intro i j mp_i mp_j lay_i lay_j hij hi hj
      match i, j with
      | 4, 4 | 5, 5 | 6, 6 => exact absurd rfl hij
      | 4, 5 | 4, 6 | 5, 4 | 5, 6 | 6, 4 | 6, 5 =>
        injection hi with hi; injection hi with hvi _; injection hvi with hvi; injection hvi with hvi
        injection hj with hj; injection hj with hvj _; injection hvj with hvj; injection hvj with hvj
        subst hvi hvj; decide
      | 0, _ | 1, _ | 2, _ | 3, _ | 7, _ | 8, _ => cases hi
      | _, 0 | _, 1 | _, 2 | _, 3 | _, 7 | _, 8 => cases hj
      | n + 9, _ =>
        have hlt := (Array.getElem?_eq_some_iff.mp hi).1
        have hsz : m5₃_imm.stack.frames[0].locals.size = 9 := rfl
        rw [hsz] at hlt; omega
      | _, n + 9 =>
        have hlt := (Array.getElem?_eq_some_iff.mp hj).1
        have hsz : m5₃_imm.stack.frames[0].locals.size = 9 := rfl
        rw [hsz] at hlt; omega
  have hst_ind := lm24PUMiriAt_stateRel 5 3 .uninit .uninit .uninit
    (.uninitIndirect 4 4 4 0 2 lm24BaseMemPlace _ (fun l hl => (Option.some.inj hl).symm)
      lm24_wt_PU rfl lm24PU_uninitMem1)
    (.uninitIndirect 4 4 4 0 2 lm24Arr2MemPlace _ (fun l hl => (Option.some.inj hl).symm)
      lm24_wt_PU rfl lm24PU_uninitMem4)
    (.base _ _ (.immediate .uninit .uninit _ (fun l hl => (Option.some.inj hl).symm)
      (.inl ⟨rfl, rfl⟩)))
  have hm_imm : Miri.Interpreter.Step.step hooks () m5₃_imm =
      ((Miri.Interpreter.Step.step hooks () m5₃_imm).1,
        .error (.undefinedBehavior "field read of uninitialized union")) :=
    miri_step_eq hooks m5₃_imm _ (by with_unfolding_all rfl)
  have hstep_rel_imm :
      StepRelLM2_4PaddedZst lm24PUBody m5₃_imm (stepMirFn lm24PUBody s5₃)
        (Miri.Interpreter.Step.step hooks () m5₃_imm) := by
    rw [show stepMirFn lm24PUBody s5₃ = MirStepNode.fail .ub from rfl, hm_imm]
    exact .ub _ "field read of uninitialized union"
  exact ⟨hst_imm, rfl,
    by with_unfolding_all rfl,
    by with_unfolding_all rfl,
    hstep_rel_imm,
    hst_ind,
    by with_unfolding_all rfl,
    by with_unfolding_all rfl⟩

end LeanMiriSpec.Correspondence.Witness
