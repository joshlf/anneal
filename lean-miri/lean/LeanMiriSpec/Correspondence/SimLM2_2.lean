/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import LeanMiriSpec.Correspondence.Simulation
import LeanMiriSpec.Correspondence.SimLM1_2
import LeanMiriSpec.Correspondence.SimLM1_4
import LeanMiriSpec.Correspondence.LayoutLM2_2
import LeanMiriSpec.Correspondence.ProjLM2_2

/-!
# `LM-2.2`: Padded Tuples & Structs, `.ScalarPair` vs. `.Memory` Dispatch & Nested `Field` Projections

Formal correspondence between Anneal (`Trusted.Rustc.V2026_06_01.MirSemantics`)
and `lean-miri` (`Miri/Interpreter/{Aggregate,Projection,Place,Rvalue}.lean`
and `Miri/ABI/Layout.lean`) under `StateRelLM2_2` and `StepRelLM2_2`:

1. `ValidStructLayout` and `writeField_preserves_other_fields_and_padding`
   (re-exported from `LayoutLM2_2.lean`);
2. `evalRvalue_aggregate_tuple_struct_simulation`: non-empty tuple and
   single-variant ADT aggregate construction (`AggregateKind.Tuple` and
   `AggregateKind.Adt`) of arbitrary positive arity across `AbiRepr.Scalar`,
   `AbiRepr.ScalarPair`, and `AbiRepr.Memory` (both unpadded and padded,
   including nested `.Scalar` and `.ScalarPair` sub-structs with
   `ValidStructLayout` at every nesting level), matching upstream Miri's
   `forceAllocation` on field writes and keeping every alignment padding byte
   `.uninit` in `Allocation.initializationMask`;
3. `evalProjection_nested_field_read_simulation` (re-exported from
   `ProjLM2_2.lean`): single and arbitrarily nested `ProjectionElem.field`
   reads across `AbiRepr.Scalar`, `AbiRepr.ScalarPair`, and `AbiRepr.Memory`;
4. `step_assign_nested_field_write_simulation`, `step_stmt_lm2_2_simulation`,
   `step_two_stmts_lm2_2_simulation`, and `step_stmts_lm2_2_simulation`: 100%
   state-independent statement typing (`WellTypedLM2_2Stmt`) and composition over
   any run of consecutive statements across `StorageLive`, `StorageDead`, scalar
   & immediate-aggregate `Use` assignments, `Aggregate` construction, and
   single/nested partial-field writes;
5. `step_assign_use_struct_lm2_2_simulation`: whole-value reassignment
   `_dst = Use(op)` of a `.Scalar`/`.ScalarPair` struct whose destination is
   dead, immediate, or already held in a stack allocation (written through
   memory exactly as upstream `writePlaceImmediateNoValidate` does).
-/

namespace LeanMiriSpec.Correspondence

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

/-! ## 1. Syntactic Helpers, `writeAggregate` Unfolding & Projected `evalPlace` -/

/-- Single-variant aggregate kinds supported by `LM-2.2`: tuples
(`AggregateKind.tuple`) and single-variant structs
(`AggregateKind.adt defId 0 .none`). -/
def IsTupleOrSingleAdtKind (kind : MirAst.AggregateKind) : Prop :=
  kind = .tuple ∨ ∃ defId, kind = .adt defId 0 .none

theorem translateRvalue_aggregate_of_isTupleOrSingleAdtKind
    {kind : MirAst.AggregateKind} (hk : IsTupleOrSingleAdtKind kind)
    (ops : List MirAst.Operand) :
    ∃ mkind,
      translateRvalue (.aggregate kind ops) =
        .Aggregate mkind (ops.map translateOperand).toArray ∧
      (mkind = .Tuple ∨ mkind = .Adt 0 0 #[] none none) := by
  rcases hk with rfl | ⟨defId, rfl⟩
  · exact ⟨.Tuple, rfl, Or.inl rfl⟩
  · exact ⟨.Adt 0 0 #[] none none, rfl, Or.inr rfl⟩

/-- Parametric field-writing loop matching `Miri.Interpreter.writeAggregate`
over an arbitrary list of translated MIR operands starting at index `start`. -/
def writeAggregateFieldsAux
    (h : Miri.Interpreter.AggregateHooks AnnealProv AnnealStepState Unit
      (Miri.Interpreter.RuntimePlace AnnealProv))
    (dest : Miri.Interpreter.RuntimePlace AnnealProv)
    (start : Nat) : List Miri.MIR.Operand → Miri.Interpreter.RvalueM AnnealStepState Unit
  | [] => pure ()
  | op :: rest => do
      let field ← h.projectField () dest start
      let v ← h.evalOperandAt () (Miri.Interpreter.OperandPath.aggregate start) op
        (some (h.placeLayout field))
      h.copyOpNoValidate () v field false
      writeAggregateFieldsAux h dest (start + 1) rest

private theorem forIn_range'_writeAggregate_eq
    (h : Miri.Interpreter.AggregateHooks AnnealProv AnnealStepState Unit
      (Miri.Interpreter.RuntimePlace AnnealProv))
    (operands : Array Miri.MIR.Operand)
    (dest : Miri.Interpreter.RuntimePlace AnnealProv) :
    ∀ (rest : List Miri.MIR.Operand) (start : Nat),
      (∀ k (hk : k < rest.length), operands[start + k]? = some (rest[k]'hk)) →
      (do
        for index in List.range' start rest.length 1 do
          let some operand := operands[index]? | throw (.invalidProgram "aggregate operand index")
          let field ← h.projectField () dest index
          let operand ← h.evalOperandAt () (Miri.Interpreter.OperandPath.aggregate index) operand
            (some (h.placeLayout field))
          h.copyOpNoValidate () operand field false) =
        writeAggregateFieldsAux h dest start rest
  | [], _, _ => rfl
  | op :: tl, start, hget => by
    have h0 : operands[start]? = some op := by
      have := hget 0 (Nat.zero_lt_succ _)
      simpa using this
    have htl : ∀ k (hk : k < tl.length), operands[(start + 1) + k]? = some (tl[k]'hk) := by
      intro k hk
      have := hget (k + 1) (Nat.succ_lt_succ hk)
      have hadd : start + (k + 1) = (start + 1) + k := by omega
      rw [← hadd]
      exact this
    have ih := forIn_range'_writeAggregate_eq h operands dest tl (start + 1) htl
    funext s
    simp only [List.length_cons, List.range', forIn, List.forIn'_cons,
      writeAggregateFieldsAux, h0,
      Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]
    cases h.projectField () dest start s with
    | error e s1 => rfl
    | ok field s1 =>
      dsimp only
      cases h.evalOperandAt () (Miri.Interpreter.OperandPath.aggregate start) op
          (some (h.placeLayout field)) s1 with
      | error e s2 => rfl
      | ok v s2 =>
        dsimp only
        cases h.copyOpNoValidate () v field false s2 with
        | error e s3 => rfl
        | ok _ s3 => exact congrFun ih s3

/-- Parametric unfolding of `Miri.Interpreter.writeAggregate` for any arity
`ops.length` over `AggregateKind.Tuple` or single-variant `AggregateKind.Adt`. -/
theorem writeAggregate_list_eq
    (h : Miri.Interpreter.AggregateHooks AnnealProv AnnealStepState Unit
      (Miri.Interpreter.RuntimePlace AnnealProv))
    {mkind : Miri.MIR.AggregateKind}
    (hmk : mkind = .Tuple ∨ mkind = .Adt 0 0 #[] none none)
    (ops : List Miri.MIR.Operand)
    (dest : Miri.Interpreter.RuntimePlace AnnealProv)
    (hdown : h.projectDowncast () dest 0 = pure dest)
    (hdisc : h.writeDiscriminant () 0 dest = pure ())
    (henf : h.enforceValidity () (h.placeLayout dest) = pure true)
    (hval : h.validate () dest = pure ()) :
    Miri.Interpreter.writeAggregate h () mkind ops.toArray dest =
      writeAggregateFieldsAux h dest 0 ops := by
  have hloop := forIn_range'_writeAggregate_eq h ops.toArray dest ops 0 (by
    intro k hk; simp [hk])
  simp at hloop
  rcases hmk with rfl | rfl
  · funext s
    have hstep :
        Miri.Interpreter.writeAggregate h () .Tuple ops.toArray dest =
        (do
          writeAggregateFieldsAux h dest 0 ops
          h.writeDiscriminant () 0 dest
          if ← h.enforceValidity () (h.placeLayout dest) then
            h.validate () dest) := by
      simp [Miri.Interpreter.writeAggregate]
      exact congrArg (· >>= _) hloop
    rw [hstep]
    dsimp only [Bind.bind, EStateM.bind]
    cases writeAggregateFieldsAux h dest 0 ops s with
    | error _ _ => rfl
    | ok u s1 =>
      cases u
      simp [Pure.pure, EStateM.pure, hdisc, henf, hval]
  · funext s
    have hstep :
        Miri.Interpreter.writeAggregate h () (.Adt 0 0 #[] none none) ops.toArray dest =
        (do
          writeAggregateFieldsAux h dest 0 ops
          h.writeDiscriminant () 0 dest
          if ← h.enforceValidity () (h.placeLayout dest) then
            h.validate () dest) := by
      simp [Miri.Interpreter.writeAggregate, hdown]
      exact congrArg (· >>= _) hloop
    rw [hstep]
    dsimp only [Bind.bind, EStateM.bind]
    cases writeAggregateFieldsAux h dest 0 ops s with
    | error _ _ => rfl
    | ok u s1 =>
      cases u
      simp [Pure.pure, EStateM.pure, hdisc, henf, hval]

/-- Syntactic check that operand `op` does not destructively move `dstIdx`. -/
def OperandDoesNotMoveLocal (dstIdx : Local) : MirAst.Operand → Prop
  | .move ⟨idx, []⟩ => idx ≠ dstIdx
  | _ => True

/-- Syntactic check that operand `op` does not reference `dstIdx` (used for
`Aggregate` rvalue operands so an in-place destination field write never aliases
a later operand read). -/
def OperandDoesNotAccessLocal (dstIdx : Local) : MirAst.Operand → Prop
  | .constant _ => True
  | .copy ⟨idx, _⟩ | .move ⟨idx, _⟩ => idx ≠ dstIdx

theorem OperandDoesNotAccessLocal.not_move {dstIdx : Local} {op : MirAst.Operand}
    (h : OperandDoesNotAccessLocal dstIdx op) : OperandDoesNotMoveLocal dstIdx op := by
  cases op with
  | constant _ => trivial
  | copy _ => trivial
  | move pl =>
    rcases pl with ⟨idx, projs⟩
    cases projs with
    | nil => exact h
    | cons _ _ => trivial

/-- Static abstract local-environment transformer for evaluating `op`: an
unprojected `.move ⟨idx, []⟩` deinitializes `idx` to `.uninit` /
`.live (.immediate .uninit)` (removing `idx` from `initLocals` and adding `idx`
to `immLocals`), while all other operands leave local initialization and
immediacy unchanged. -/
def operandPostStaticEnv (stEnv : LM2_2StaticEnv) : MirAst.Operand → LM2_2StaticEnv
  | .move ⟨idx, []⟩ =>
      { initLocals := stEnv.initLocals.filter (· != idx)
        immLocals := idx :: stEnv.immLocals }
  | _ => stEnv

/-- Fold `operandPostStaticEnv` left-to-right across an operand list. -/
def opsPostStaticEnv (stEnv : LM2_2StaticEnv) : List MirAst.Operand → LM2_2StaticEnv
  | [] => stEnv
  | op :: rest => opsPostStaticEnv (operandPostStaticEnv stEnv op) rest

/-- Pure syntactic shape of `LM-2.2` operands ensuring Anneal's `evalOperand`
never returns `.unsupported` and preserves `locals.length`. -/
def SyntacticFieldOperand (numLocals : Nat) : MirAst.Operand → Prop
  | .constant c => ∃ sc, c.val = .scalar (.int sc)
  | .copy ⟨idx, projs⟩ | .move ⟨idx, projs⟩ =>
      idx < numLocals ∧ ∀ p ∈ projs, ∃ fIdx fTy, p = .field fIdx fTy

theorem ValidFieldProjChain.only_fields
    {layouts : LayoutTable} {baseLay : Miri.Interpreter.LocalLayout}
    {projs : List ProjectionElem} {leafTy : Ty} {totalOff : Miri.ABI.Size}
    (h : ValidFieldProjChain layouts baseLay projs leafTy totalOff) :
    ∀ p ∈ projs, ∃ fIdx fTy, p = .field fIdx fTy := by
  induction h with
  | single _ idx fty _ _ _ _ _ =>
    intro p hp
    simp only [List.mem_singleton] at hp
    exact ⟨idx, fty, hp⟩
  | cons _ idx midTy _ _ _ _ _ _ _ _ _ ih =>
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hmem
    · exact ⟨idx, midTy, rfl⟩
    · exact ih p hmem

private theorem readProjectedValue_ne_unsupported_of_fields
    (locals : List LocalSlot) :
    ∀ (projs : List ProjectionElem) (val : Value),
      (∀ p ∈ projs, ∃ fIdx fTy, p = .field fIdx fTy) →
      readProjectedValue locals val projs ≠ .unsupported
  | [], _, _ => nofun
  | p :: ps, val, hall => by
    obtain ⟨fIdx, fTy, rfl⟩ := hall p List.mem_cons_self
    have hall' : ∀ q ∈ ps, ∃ i t, q = .field i t :=
      fun q hq => hall q (List.mem_cons_of_mem _ hq)
    cases val with
    | aggregate _ fvals =>
      dsimp [readProjectedValue]
      cases get? fvals fIdx with
      | none => nofun
      | some fv => exact readProjectedValue_ne_unsupported_of_fields locals ps fv hall'
    | scalar sc =>
      cases fIdx with
      | zero => exact readProjectedValue_ne_unsupported_of_fields locals ps (.scalar sc) hall'
      | succ _ => nofun
    | ptr pv sz =>
      cases fIdx with
      | zero => exact readProjectedValue_ne_unsupported_of_fields locals ps (.ptr pv sz) hall'
      | succ _ => nofun
    | unit =>
      cases fIdx with
      | zero => exact readProjectedValue_ne_unsupported_of_fields locals ps .unit hall'
      | succ _ => nofun

theorem SyntacticFieldOperand.evalOperand_shape
    {locals : List LocalSlot} {op : MirAst.Operand}
    (h : SyntacticFieldOperand locals.length op)
    (globals : List CapturedAllocation) (layouts : LayoutTable) :
    evalOperand locals op .nil globals layouts .nil ≠ .unsupported ∧
    ∀ v locals',
      evalOperand locals op .nil globals layouts .nil = .ok v locals' →
      locals'.length = locals.length ∧
      ∀ k, OperandDoesNotMoveLocal k op → get? locals' k = get? locals k := by
  cases op with
  | constant c =>
    obtain ⟨sc, hval⟩ := h
    have heq : evalOperand locals (.constant c) .nil globals layouts .nil =
        .ok (.scalar sc) locals := by
      unfold evalOperand; dsimp only; rw [hval]; rfl
    rw [heq]
    refine ⟨nofun, ?_⟩
    intro _ locals' hok
    injection hok with _ hloc; subst hloc
    exact ⟨rfl, fun _ _ => rfl⟩
  | copy pl =>
    rcases pl with ⟨idx, projs⟩
    obtain ⟨hlt, hfields⟩ := h
    have hget : get? locals idx = some (locals[idx]'hlt) := by
      rw [get?_eq_getElem?, List.getElem?_eq_getElem hlt]
    cases projs with
    | nil =>
      unfold evalOperand; dsimp only; rw [hget]
      cases locals[idx]'hlt with
      | dead => exact ⟨nofun, fun _ _ hok => nomatch hok⟩
      | uninit => exact ⟨nofun, fun _ _ hok => nomatch hok⟩
      | init rootVal =>
        dsimp only [readProjectedValue]
        refine ⟨nofun, fun _ locals' hok => ?_⟩
        injection hok with _ hloc; subst hloc
        exact ⟨rfl, fun _ _ => rfl⟩
    | cons p0 ps =>
      obtain ⟨fIdx, fTy, rfl⟩ := hfields p0 List.mem_cons_self
      unfold evalOperand; dsimp only; rw [hget]
      cases locals[idx]'hlt with
      | dead => exact ⟨nofun, fun _ _ hok => nomatch hok⟩
      | uninit => exact ⟨nofun, fun _ _ hok => nomatch hok⟩
      | init rootVal =>
        dsimp only
        have hne := readProjectedValue_ne_unsupported_of_fields locals
          (.field fIdx fTy :: ps) rootVal hfields
        cases hr : readProjectedValue locals rootVal (.field fIdx fTy :: ps) with
        | unsupported => exact False.elim (hne hr)
        | ub => exact ⟨nofun, fun _ _ hok => nomatch hok⟩
        | ok pv =>
          refine ⟨nofun, fun _ locals' hok => ?_⟩
          injection hok with _ hloc; subst hloc
          exact ⟨rfl, fun _ _ => rfl⟩
  | move pl =>
    rcases pl with ⟨idx, projs⟩
    obtain ⟨hlt, hfields⟩ := h
    have hget : get? locals idx = some (locals[idx]'hlt) := by
      rw [get?_eq_getElem?, List.getElem?_eq_getElem hlt]
    cases projs with
    | nil =>
      unfold evalOperand; dsimp only; rw [hget]
      cases locals[idx]'hlt with
      | dead => exact ⟨nofun, fun _ _ hok => nomatch hok⟩
      | uninit => exact ⟨nofun, fun _ _ hok => nomatch hok⟩
      | init rootVal =>
        dsimp only; rw [set?_eq_some_set hlt]
        refine ⟨nofun, fun _ locals' hok => ?_⟩
        injection hok with _ hloc; subst hloc
        exact ⟨List.length_set, fun k hk => by
          have hne : idx ≠ k := hk
          simp [get?, List.getElem?_set_ne hne]⟩
    | cons p0 ps =>
      obtain ⟨fIdx, fTy, rfl⟩ := hfields p0 List.mem_cons_self
      unfold evalOperand; dsimp only; rw [hget]
      cases locals[idx]'hlt with
      | dead => exact ⟨nofun, fun _ _ hok => nomatch hok⟩
      | uninit => exact ⟨nofun, fun _ _ hok => nomatch hok⟩
      | init rootVal =>
        dsimp only
        have hne := readProjectedValue_ne_unsupported_of_fields locals
          (.field fIdx fTy :: ps) rootVal hfields
        cases hr : readProjectedValue locals rootVal (.field fIdx fTy :: ps) with
        | unsupported => exact False.elim (hne hr)
        | ub => exact ⟨nofun, fun _ _ hok => nomatch hok⟩
        | ok pv =>
          refine ⟨nofun, fun _ locals' hok => ?_⟩
          injection hok with _ hloc; subst hloc
          exact ⟨rfl, fun _ _ => rfl⟩

theorem evalOperands_shape_of_syntactic
    (globals : List CapturedAllocation) (layouts : LayoutTable) (dstIdx : Local) :
    ∀ (ops : List MirAst.Operand) (locals : List LocalSlot),
      (∀ op ∈ ops, SyntacticFieldOperand locals.length op ∧ OperandDoesNotMoveLocal dstIdx op) →
      evalOperands locals ops .nil globals layouts .nil ≠ .unsupported ∧
      ∀ vals locals',
        evalOperands locals ops .nil globals layouts .nil = .ok vals locals' →
        locals'.length = locals.length ∧
        get? locals' dstIdx = get? locals dstIdx
  | [], _, _ => by
    refine ⟨nofun, fun _ locals' hok => ?_⟩
    dsimp [evalOperands] at hok
    injection hok with _ hloc; subst hloc
    exact ⟨rfl, rfl⟩
  | op :: rest, locals, hall => by
    obtain ⟨hsyn0, hnm0⟩ := hall op List.mem_cons_self
    obtain ⟨hne0, hok0⟩ := hsyn0.evalOperand_shape globals layouts
    unfold evalOperands
    cases hr0 : evalOperand locals op .nil globals layouts .nil with
    | unsupported => exact False.elim (hne0 hr0)
    | ub => exact ⟨nofun, fun _ _ hok => nomatch hok⟩
    | ok v0 locals1 =>
      dsimp only
      obtain ⟨hlen1, hkeep1⟩ := hok0 v0 locals1 hr0
      have hall_rest : ∀ q ∈ rest,
          SyntacticFieldOperand locals1.length q ∧ OperandDoesNotMoveLocal dstIdx q := by
        intro q hq; rw [hlen1]; exact hall q (List.mem_cons_of_mem _ hq)
      obtain ⟨hne_rest, hok_rest⟩ :=
        evalOperands_shape_of_syntactic globals layouts dstIdx rest locals1 hall_rest
      cases hr_rest : evalOperands locals1 rest .nil globals layouts .nil with
      | unsupported => exact False.elim (hne_rest hr_rest)
      | ub => exact ⟨nofun, fun _ _ hok => nomatch hok⟩
      | ok vs locals2 =>
        dsimp only
        obtain ⟨hlen2, hkeep2⟩ := hok_rest vs locals2 hr_rest
        refine ⟨nofun, fun _ locals' hok => ?_⟩
        injection hok with _ hloc; subst hloc
        exact ⟨hlen2.trans hlen1, hkeep2.trans (hkeep1 dstIdx hnm0)⟩

/-- Resolve a projected local `Place` along `ValidFieldProjChain` via
`annealEvalPlace`, caching the base local's layout and accumulating `totalOff`. -/
theorem annealEvalPlace_projected
    {body : CapturedMir} {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {idx : Local} {decl : LocalDecl}
    {projs : List ProjectionElem} {leafTy : Ty} {totalOff : Miri.ABI.Size}
    (hframes : m.stack.frames = #[topFrame])
    (hlt : idx < topFrame.locals.size)
    (hdecl : get? body.localDecls idx = some decl)
    (hcache : ∀ l, (topFrame.locals[idx]'hlt).layout = some l →
      l = translateTy decl.ty body.layouts)
    (hchain : ValidFieldProjChain body.layouts (translateTy decl.ty body.layouts)
      projs leafTy totalOff) :
    annealEvalPlace body.localDecls body.layouts (translatePlace ⟨idx, projs⟩) m =
      .ok ⟨.local 0 idx (some totalOff) topFrame.localsIdentity,
            translateTy leafTy body.layouts⟩
        { m with
          stack := ⟨#[cacheFrameLocalLayout topFrame idx hlt
            (translateTy decl.ty body.layouts)]⟩ } := by
  have hres := annealResolveAndCacheLocalLayout_eq (known := none) hframes hlt hdecl hcache
  have hlt_u64 := (translateTy decl.ty body.layouts).layout.size.bytes.toNat_lt
  have hproj := annealProjectPlaceList_of_validFieldProjChain hchain
    (frameIdx := 0) (localId := idx) (baseOffOpt := none) (id0 := topFrame.localsIdentity)
    (by dsimp [Miri.ABI.Size.ZERO]; omega)
  dsimp [Miri.ABI.Size.ZERO] at hproj
  rw [UInt64.zero_add] at hproj
  have hsz_eq : Miri.ABI.Size.ofBytes totalOff.bytes = totalOff := by cases totalOff; rfl
  rw [hsz_eq] at hproj
  cases projs with
  | nil => exact False.elim (hchain.ne_nil rfl)
  | cons p ps =>
    obtain ⟨fidx0, fty0, rfl⟩ := hchain.head_field
    have hcur : m.stack.currentFrame?.isNone = false := by
      rw [stack_currentFrame?_singleton m.stack topFrame hframes]; rfl
    have hsz_frames : m.stack.frames.size - 1 = 0 := by rw [hframes]; rfl
    have hid_c : (cacheFrameLocalLayout topFrame idx hlt
        (translateTy decl.ty body.layouts)).localsIdentity = topFrame.localsIdentity := rfl
    change annealEvalProjectedPlace body.localDecls body.layouts
      ⟨idx, (List.map translateProjectionElem (.field fidx0 fty0 :: ps)).toArray⟩ m = _
    with_unfolding_all
      unfold annealEvalProjectedPlace
      simp only [get, getThe, MonadStateOf.get, Bind.bind, Pure.pure,
        EStateM.get, EStateM.bind, EStateM.pure,
        hcur, Bool.false_eq_true, ↓reduceIte,
        hsz_frames, hres, hid_c, hproj]


/-! ## 2. `NoZeroByteLeaves` Inversion & Immediate-ABI Struct Recovery -/

private theorem valueLeafBytes_pos_of_noZeroByteLeaves :
    ∀ {v : Value}, NoZeroByteLeaves v → 0 < valueLeafBytes v
  | .scalar _, h => h
  | .aggregate 0 (hd :: _), ⟨hhd, _⟩ => by
    have hpos := valueLeafBytes_pos_of_noZeroByteLeaves hhd
    dsimp [valueLeafBytes, valueLeafBytes.valueLeafBytesList]
    omega

private theorem valueLeafBytesList_ge_of_get? :
    ∀ {vs : List Value} {idx : Nat} {sub : Value},
      get? vs idx = some sub →
      valueLeafBytes sub ≤ valueLeafBytes.valueLeafBytesList vs
  | [], _, _, hget => by rw [get?_eq_getElem?] at hget; cases hget
  | hd :: tl, 0, sub, hget => by
    rw [get?_eq_getElem?] at hget
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
    subst hget
    dsimp [valueLeafBytes.valueLeafBytesList]; omega
  | hd :: tl, n + 1, sub, hget => by
    rw [get?_eq_getElem?, List.getElem?_cons_succ, ← get?_eq_getElem?] at hget
    have ih := valueLeafBytesList_ge_of_get? hget
    dsimp [valueLeafBytes.valueLeafBytesList]; omega

private theorem valueLeafBytes_ge_of_validPath
    {layouts : LayoutTable} {v : Value} {projs : List ProjectionElem} {sc : MirAst.ScalarInt}
    (hp : ValidAggregateFieldPath layouts v projs)
    (hr : readProjectedValue [] v projs = .ok (.scalar sc)) :
    sc.sizeBytes ≤ valueLeafBytes v := by
  induction hp with
  | single fields idx fty oldVal hget =>
    dsimp [readProjectedValue] at hr
    rw [hget] at hr
    injection hr with heq; subst heq
    exact valueLeafBytesList_ge_of_get? hget
  | cons fields idx fty rest subVal hget _ _ ih =>
    dsimp [readProjectedValue] at hr
    rw [hget] at hr
    exact Nat.le_trans (ih hr) (valueLeafBytesList_ge_of_get? hget)

theorem zeroScalarWrappedVal_of_noZeroByteLeaves
    {layouts : LayoutTable} {sc : MirAst.ScalarInt} :
    ∀ {projs : List ProjectionElem} {v : Value},
      NoZeroByteLeaves v →
      (projs ≠ [] → ValidAggregateFieldPath layouts v projs) →
      (∀ p ∈ projs, ∃ fty, p = .field 0 fty) →
      readProjectedValue [] v projs = .ok (.scalar sc) →
      valueLeafBytes v = sc.sizeBytes →
      ZeroScalarWrappedVal sc v projs
  | [], v, _, _, _, hr, _ => by
    dsimp [readProjectedValue] at hr
    injection hr with heq; subst heq
    exact .bare
  | p0 :: rest, v, hnz, hvpath, hall, hr, hbytes => by
    obtain ⟨fty, rfl⟩ := hall p0 List.mem_cons_self
    have hall_rest : ∀ q ∈ rest, ∃ t, q = .field 0 t :=
      fun q hq => hall q (List.mem_cons_of_mem _ hq)
    cases hvpath (by nofun) with
    | single fields _ _ oldVal hget =>
      cases fields with
      | nil => rw [get?_eq_getElem?] at hget; cases hget
      | cons subVal tl =>
        rw [get?_eq_getElem?, List.getElem?_cons_zero, Option.some.injEq] at hget
        subst hget
        dsimp [readProjectedValue, get?] at hr
        injection hr with hsc; subst hsc
        rcases hnz with ⟨_, htl⟩
        cases tl with
        | nil => exact .wrap_cons fty [] (.scalar sc) .bare
        | cons x xs =>
          have hx := valueLeafBytes_pos_of_noZeroByteLeaves htl.1
          dsimp [valueLeafBytes, valueLeafBytes.valueLeafBytesList] at hbytes
          omega
    | cons fields _ _ _ subVal hget _ hsub =>
      cases fields with
      | nil => rw [get?_eq_getElem?] at hget; cases hget
      | cons hd tl =>
        rw [get?_eq_getElem?, List.getElem?_cons_zero, Option.some.injEq] at hget
        subst hget
        dsimp [readProjectedValue, get?] at hr
        rcases hnz with ⟨hnz_sub, htl⟩
        have hge_sub := valueLeafBytes_ge_of_validPath hsub hr
        cases tl with
        | nil =>
          dsimp [valueLeafBytes, valueLeafBytes.valueLeafBytesList] at hbytes
          have hsub_bytes : valueLeafBytes hd = sc.sizeBytes := by omega
          exact .wrap_cons fty rest hd
            (zeroScalarWrappedVal_of_noZeroByteLeaves hnz_sub (fun _ => hsub)
              hall_rest hr hsub_bytes)
        | cons x xs =>
          have hx := valueLeafBytes_pos_of_noZeroByteLeaves htl.1
          dsimp [valueLeafBytes, valueLeafBytes.valueLeafBytesList] at hbytes
          omega

private theorem validPath_cons_inv {layouts : LayoutTable}
    {rootVal : Value} {idx : Nat} {fty : Ty}
    {rest : List ProjectionElem} {sc : MirAst.ScalarInt}
    (hp : ValidAggregateFieldPath layouts rootVal (.field idx fty :: rest))
    (hr : readProjectedValue [] rootVal (.field idx fty :: rest) = .ok (.scalar sc)) :
    ∃ fields subVal,
      rootVal = .aggregate 0 fields ∧
      get? fields idx = some subVal ∧
      readProjectedValue [] subVal rest = .ok (.scalar sc) ∧
      (rest ≠ [] → ValidAggregateFieldPath layouts subVal rest) ∧
      sc.sizeBytes ≤ valueLeafBytes subVal := by
  cases hp with
  | single fields _ _ oldVal hget =>
    dsimp [readProjectedValue] at hr
    rw [hget] at hr
    injection hr with heq; subst heq
    exact ⟨fields, .scalar sc, rfl, hget, rfl, fun hne => False.elim (hne rfl), Nat.le_refl _⟩
  | cons fields _ _ _ subVal hget _ hsub =>
    dsimp [readProjectedValue] at hr
    rw [hget] at hr
    exact ⟨fields, subVal, rfl, hget, hr, fun _ => hsub, valueLeafBytes_ge_of_validPath hsub hr⟩

/-- Pure syntactic specification of an immediate-ABI aggregate type (`AbiRepr.Scalar`
1-field wrapper or `AbiRepr.ScalarPair` 2-scalar tuple/struct) in `StructTypeEnv`. -/
inductive IsImmediateStructTy (env : StructTypeEnv) (layouts : LayoutTable) (ty : Ty) :
    List StructFieldDesc → List (List ProjectionElem) → Prop where
  | scalarWrapper (f₀ : StructFieldDesc) (p₀ : List ProjectionElem) (a : Miri.ABI.Scalar) :
      env ty = some ([f₀], [p₀]) →
      ValidStructLayout (translateTy ty layouts).layout [f₀] →
      (translateTy ty layouts).layout.backendRepr = .Scalar a →
      (translateTy ty layouts).layout.size = f₀.fieldLayout.size →
      p₀ ≠ [] →
      ValidZeroScalarChain layouts (translateTy ty layouts) p₀ f₀.ty →
      f₀.offset = Miri.ABI.Size.ZERO →
      f₀.fieldLayout = (translateTy f₀.ty layouts).layout →
      IsPrimScalarTy f₀.ty →
      IsImmediateStructTy env layouts ty [f₀] [p₀]
  | scalarPair (f₀ f₁ : StructFieldDesc) (mid₀ mid₁ : Ty)
      (z₀ z₁ : List ProjectionElem)
      (a b : Miri.ABI.Scalar) (bOff : Miri.ABI.Size) :
      env ty = some ([f₀, f₁], [.field 0 mid₀ :: z₀, .field 1 mid₁ :: z₁]) →
      ValidStructLayout (translateTy ty layouts).layout [f₀, f₁] →
      (translateTy ty layouts).layout.size.bytes.toNat < 2 ^ 32 →
      ((∃ ts, ty.kind = .tuple ts) ∨ (∃ p adtArgs, ty.kind = .adt p adtArgs)) →
      (∀ t₁, ty.kind = .tuple [t₁, .bool] → f₁.ty.kind = .bool) →
      (translateTy ty layouts).layout.backendRepr =
        .ScalarPair (a := a) (b := b) (bOffset := bOff) →
      a.size annealRuntimeDataLayout = .ok f₀.fieldLayout.size →
      b.size annealRuntimeDataLayout = .ok f₁.fieldLayout.size →
      (translateTy ty layouts).layout.fields.offset 0 = .ok Miri.ABI.Size.ZERO →
      (translateTy ty layouts).layout.fields.offset 1 = .ok bOff →
      f₀.offset = Miri.ABI.Size.ZERO →
      f₁.offset = bOff →
      f₀.fieldLayout = (translateTy f₀.ty layouts).layout →
      f₁.fieldLayout = (translateTy f₁.ty layouts).layout →
      IsRoundtripTy mid₀ →
      IsRoundtripTy mid₁ →
      IsPrimScalarTy f₀.ty →
      IsPrimScalarTy f₁.ty →
      ValidOptZeroScalarChain layouts mid₀ z₀ f₀.ty →
      ValidOptZeroScalarChain layouts mid₁ z₁ f₁.ty →
      IsImmediateStructTy env layouts ty [f₀, f₁]
        [.field 0 mid₀ :: z₀, .field 1 mid₁ :: z₁]

theorem StructMemPlaceRel.toImmediateStructRel
    {env : StructTypeEnv} {mach : AnnealMachine} {ty : Ty} {layouts : LayoutTable}
    {fields : List StructFieldDesc} {paths : List (List ProjectionElem)}
    {rootVal : Value} {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hspec : IsImmediateStructTy env layouts ty fields paths)
    (hmp : StructMemPlaceRel mach ty layouts fields paths rootVal mp) :
    ∃ imm,
      ImmediateStructRel ty layouts fields paths rootVal imm ∧
      ∀ m : AnnealStepState,
        m.machine = mach →
        annealReadIndirectImmediate mp (translateTy ty layouts) m =
          .ok ⟨imm, translateTy ty layouts⟩ m := by
  rcases hmp with ⟨allocId, _, baseAddr, localAlloc, _, _, _, ⟨_, hnz_root⟩,
    hleaf_bytes, hprov, _, _, hlive, hbase, hptr, _, _, _, _, _, _, _, _, hfields, _⟩
  have hptr_z : mp.ptr.offset = Miri.ABI.Size.ofBytes (baseAddr + Miri.ABI.Size.ZERO.bytes) := by
    rw [hptr]; dsimp [Miri.ABI.Size.ZERO]; rw [UInt64.add_zero]
  cases hspec with
  | scalarWrapper f₀ p₀ a _ hvalid hrepr hsz_eq hp₀_ne hzero hf₀_off hfl₀ hprim₀ =>
    obtain ⟨_, _, _, hvpath₀, sc, msc, hrpv₀, hrel, hsz₀, hbool₀, hchar₀, _, hread₀⟩ :=
      hfields 0 (by simp)
    dsimp at hvpath₀ hrpv₀ hsz₀ hbool₀ hchar₀ hread₀
    have hsc_bytes : valueLeafBytes rootVal = sc.sizeBytes := by
      rw [hleaf_bytes]; dsimp [structSumFieldBytes]; rw [hsz₀]
      rcases hrel.validBytes with h1 | h1 | h1 | h1 | h1 <;> (rw [h1]; rfl)
    have hwrap := zeroScalarWrappedVal_of_noZeroByteLeaves hnz_root
      (fun _ => hvpath₀) hzero.all_field_zero hrpv₀ hsc_bytes
    have hnz_lay : (translateTy ty layouts).layout.size ≠ Miri.ABI.Size.ZERO := by
      rw [hsz_eq, hfl₀]; exact hprim₀.size_ne_zero (layouts := layouts)
    refine ⟨.scalar (.fromScalarInt msc),
      .scalarWrapper f₀ p₀ a sc msc rootVal hvalid hrepr hp₀_ne hzero hf₀_off hfl₀
        hprim₀ hwrap hrel hsz₀ hbool₀ hchar₀, ?_⟩
    intro m hm
    rw [hf₀_off, ← hsz_eq] at hread₀
    exact annealReadIndirectImmediate_scalarRepr_ok hnz_lay (by intro s c heq; rcases hvalid.fields_shape_valid with ⟨_, hprim, _⟩ | ⟨_, _, harb, _⟩ <;> simp_all) hrepr hprov
      (by rw [hm]; exact hbase) hptr_z (by rw [hm]; exact hlive.1) hread₀
  | scalarPair f₀ f₁ mid₀ mid₁ z₀ z₁ a b bOff _ hvalid hsz4g hagg htup_bool hrepr
      ha_sz hb_sz hoff0 hoff1 hf₀_off hf₁_off hfl₀ hfl₁ hrt₀ hrt₁ hprim₀ hprim₁ hz₀ hz₁ =>
    obtain ⟨_, _, _, hvpath₀, sc₀, msc₀, hrpv₀, hrel₀, hsz₀, hbool₀, hchar₀, _, hread₀⟩ :=
      hfields 0 (by simp)
    obtain ⟨_, _, _, hvpath₁, sc₁, msc₁, hrpv₁, hrel₁, hsz₁, hbool₁, hchar₁, _, hread₁⟩ :=
      hfields 1 (by simp)
    dsimp at hvpath₀ hvpath₁ hrpv₀ hrpv₁ hsz₀ hsz₁ hbool₀ hchar₀ hbool₁ hchar₁ hread₀ hread₁
    obtain ⟨vs0, v₀, hrv0, hget0, hr0, hvp0, hge0⟩ := validPath_cons_inv hvpath₀ hrpv₀
    obtain ⟨vs1, v₁, hrv1, hget1, hr1, hvp1, hge1⟩ := validPath_cons_inv hvpath₁ hrpv₁
    subst hrv0
    injection hrv1 with _ hvs_eq; subst hvs_eq
    cases vs0 with
    | nil => rw [get?_eq_getElem?] at hget0; cases hget0
    | cons u0 tl0 =>
      rw [get?_eq_getElem?, List.getElem?_cons_zero, Option.some.injEq] at hget0; subst hget0
      cases tl0 with
      | nil => rw [get?_eq_getElem?] at hget1; cases hget1
      | cons u1 tl1 =>
        rw [get?_eq_getElem?, List.getElem?_cons_succ, List.getElem?_cons_zero,
          Option.some.injEq] at hget1; subst hget1
        rcases hnz_root with ⟨hnz₀, hnz₁, htl1⟩
        have hsum_sc : valueLeafBytes (.aggregate 0 (u0 :: u1 :: tl1)) =
            sc₀.sizeBytes + sc₁.sizeBytes := by
          rw [hleaf_bytes]; dsimp [structSumFieldBytes]; rw [hsz₀, hsz₁]
          have hb0 : (translateSizeBytes sc₀.sizeBytes).bytes.toNat = sc₀.sizeBytes := by
            rcases hrel₀.validBytes with h1 | h1 | h1 | h1 | h1 <;> (rw [h1]; rfl)
          have hb1 : (translateSizeBytes sc₁.sizeBytes).bytes.toNat = sc₁.sizeBytes := by
            rcases hrel₁.validBytes with h1 | h1 | h1 | h1 | h1 <;> (rw [h1]; rfl)
          omega
        cases tl1 with
        | cons x xs =>
          have hx := valueLeafBytes_pos_of_noZeroByteLeaves htl1.1
          dsimp [valueLeafBytes, valueLeafBytes.valueLeafBytesList] at hsum_sc
          omega
        | nil =>
          dsimp [valueLeafBytes, valueLeafBytes.valueLeafBytesList] at hsum_sc
          have hw₀ := zeroScalarWrappedVal_of_noZeroByteLeaves hnz₀ hvp0 hz₀.all_field_zero
            hr0 (by omega)
          have hw₁ := zeroScalarWrappedVal_of_noZeroByteLeaves hnz₁ hvp1 hz₁.all_field_zero
            hr1 (by omega)
          have hnz_lay : (translateTy ty layouts).layout.size ≠ Miri.ABI.Size.ZERO := by
            have hbnd := hvalid.fields_in_bounds 0 (by simp)
            have hpos : 0 < f₀.fieldLayout.size.bytes.toNat := by
              rw [hfl₀]
              have hne := hprim₀.size_ne_zero (layouts := layouts)
              cases hsz_f : (translateTy f₀.ty layouts).layout.size with
              | mk bs =>
                cases hbs : bs.toNat with
                | zero =>
                  have hbs0 : bs = 0 := UInt64.toNat_inj.mp (by simpa using hbs)
                  subst hbs0; exact absurd hsz_f hne
                | succ n => omega
            intro hz
            rw [hz] at hbnd; dsimp [Miri.ABI.Size.ZERO] at hbnd; omega
          refine ⟨.scalarPair (.fromScalarInt msc₀) (.fromScalarInt msc₁),
            .scalarPair f₀ f₁ mid₀ mid₁ z₀ z₁ a b bOff sc₀ sc₁ msc₀ msc₁ u0 u1
              hvalid hsz4g hagg htup_bool hrepr ha_sz hb_sz hoff0 hoff1 hf₀_off hf₁_off
              hfl₀ hfl₁ hrt₀ hrt₁ hprim₀ hprim₁ hz₀ hz₁ hw₀ hw₁ hrel₀ hrel₁
              hsz₀ hsz₁ hbool₀ hchar₀ hbool₁ hchar₁, ?_⟩
          intro m hm
          rw [hf₀_off] at hread₀
          have hbOff_z : Miri.ABI.Size.ofBytes (Miri.ABI.Size.ZERO.bytes + bOff.bytes) = bOff := by
            dsimp [Miri.ABI.Size.ZERO]; rw [UInt64.zero_add]; cases bOff; rfl
          rw [hf₁_off, ← hbOff_z] at hread₁
          exact annealReadIndirectImmediate_scalarPair_ok hnz_lay (by intro s c heq; rcases hvalid.fields_shape_valid with ⟨_, hprim, _⟩ | ⟨_, _, harb, _⟩ <;> simp_all) hrepr ha_sz hb_sz hprov
            (by rw [hm]; exact hbase) hptr_z (by rw [hm]; exact hlive.1) hread₀ hread₁

theorem UninitStructMemPlaceRel.readIndirect_ub_of_isImmediateStructTy
    {env : StructTypeEnv} {m : AnnealStepState} {ty : Ty} {layouts : LayoutTable}
    {fields : List StructFieldDesc} {paths : List (List ProjectionElem)}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hspec : IsImmediateStructTy env layouts ty fields paths)
    (hmp : UninitStructMemPlaceRel m.machine ty layouts fields mp) :
    ∃ msg,
      annealReadIndirectImmediate mp (translateTy ty layouts) m =
        .error (.undefinedBehavior msg) m := by
  rcases hmp with ⟨allocId, _, baseAddr, localAlloc, hvalid, hprov, _, _, hlive,
    hbase, hptr, _, _, _, _, _, _, hmask_uninit⟩
  have hptr_z : mp.ptr.offset = Miri.ABI.Size.ofBytes (baseAddr + Miri.ABI.Size.ZERO.bytes) := by
    rw [hptr]; dsimp [Miri.ABI.Size.ZERO]; rw [UInt64.add_zero]
  have hlt_u64 := (translateTy ty layouts).layout.size.bytes.toNat_lt
  cases hspec with
  | scalarWrapper f₀ p₀ a _ _ hrepr hsz_eq _ _ _ hfl₀ hprim₀ =>
    have hnz_lay : (translateTy ty layouts).layout.size ≠ Miri.ABI.Size.ZERO := by
      rw [hsz_eq, hfl₀]; exact hprim₀.size_ne_zero (layouts := layouts)
    have hend := lm22_allocRange_end (start := Miri.ABI.Size.ZERO)
      (sz := (translateTy ty layouts).layout.size)
      (by dsimp [Miri.ABI.Size.ZERO]; omega)
    have hfin : Miri.ABI.Size.ofBytes (Miri.ABI.Size.ZERO.bytes +
        (translateTy ty layouts).layout.size.bytes) =
        (translateTy ty layouts).layout.size := by
      dsimp [Miri.ABI.Size.ZERO]; rw [UInt64.zero_add]
      cases (translateTy ty layouts).layout.size; rfl
    rw [hfin] at hend
    have huninit_q : localAlloc.allocation.initializationMask.isRangeInitialized
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateTy ty layouts).layout.size) =
        .ok (.error (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateTy ty layouts).layout.size)) := by
      rw [hmask_uninit]
      exact Miri.Memory.InitMask.lazy_uninitialized_query _ _ _ hend (UInt64.le_refl _)
    exact ⟨_, annealReadIndirectImmediate_scalarRepr_uninit_ub hnz_lay (by intro s c heq; rcases hvalid.fields_shape_valid with ⟨_, hprim, _⟩ | ⟨_, _, harb, _⟩ <;> simp_all) hrepr
      hprov hbase hptr_z hlive.1 huninit_q⟩
  | scalarPair f₀ f₁ mid₀ mid₁ z₀ z₁ a b bOff _ _ _ _ _ hrepr ha_sz _ _ _ hf₀_off _ hfl₀ _ _ _ hprim₀ _ _ _ =>
    have hbnd := hvalid.fields_in_bounds 0 (by simp)
    dsimp at hbnd
    rw [hf₀_off] at hbnd
    dsimp [Miri.ABI.Size.ZERO] at hbnd
    have hpos : 0 < f₀.fieldLayout.size.bytes.toNat := by
      rw [hfl₀]
      have hne := hprim₀.size_ne_zero (layouts := layouts)
      cases hsz_f : (translateTy f₀.ty layouts).layout.size with
      | mk bs =>
        cases hbs : bs.toNat with
        | zero =>
          have hbs0 : bs = 0 := UInt64.toNat_inj.mp (by simpa using hbs)
          subst hbs0; exact absurd hsz_f hne
        | succ n => omega
    have hnz_lay : (translateTy ty layouts).layout.size ≠ Miri.ABI.Size.ZERO := by
      intro hz; rw [hz] at hbnd; dsimp [Miri.ABI.Size.ZERO] at hbnd; omega
    have hend := lm22_allocRange_end (start := Miri.ABI.Size.ZERO)
      (sz := f₀.fieldLayout.size) (by dsimp [Miri.ABI.Size.ZERO]; omega)
    have hfin : Miri.ABI.Size.ofBytes (Miri.ABI.Size.ZERO.bytes + f₀.fieldLayout.size.bytes) =
        f₀.fieldLayout.size := by
      dsimp [Miri.ABI.Size.ZERO]; rw [UInt64.zero_add]; cases f₀.fieldLayout.size; rfl
    rw [hfin] at hend
    have hle_end : f₀.fieldLayout.size.bytes ≤ (translateTy ty layouts).layout.size.bytes := by
      rw [UInt64.le_iff_toNat_le]; omega
    have huninit_q : localAlloc.allocation.initializationMask.isRangeInitialized
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO f₀.fieldLayout.size) =
        .ok (.error (Miri.Memory.allocRange Miri.ABI.Size.ZERO f₀.fieldLayout.size)) := by
      rw [hmask_uninit]
      exact Miri.Memory.InitMask.lazy_uninitialized_query _ _ _ hend hle_end
    exact ⟨_, annealReadIndirectImmediate_scalarPair_uninit_ub hnz_lay (by intro s c heq; rcases hvalid.fields_shape_valid with ⟨_, hprim, _⟩ | ⟨_, _, harb, _⟩ <;> simp_all) hrepr ha_sz
      hprov hbase hptr_z hlive.1 huninit_q⟩


/-! ## 3. `FrameRelLM2_2Except` & Syntactic `WellTypedLM2_2Operand` -/

/-- Stack-frame correspondence under `StructTypeEnv` allowing one optional local
`excl` (the destination local mid-`writeAggregate`) to be excluded while
evaluating remaining aggregate operands that do not access `excl`. -/
structure FrameRelLM2_2Except
    (body : CapturedMir)
    (env : StructTypeEnv)
    (excl : Option Local)
    (mach : AnnealMachine)
    (af : StackFrame)
    (mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit) : Prop where
  body_eq : mf.body = translateBody body
  location_eq : mf.location = .mir ⟨af.blockIdx, af.stmtIdx⟩
  af_locals_len : af.locals.length = body.localDecls.length
  mf_locals_size : mf.locals.size = body.localDecls.length
  locals_rel :
    ∀ (i : Nat) (decl : LocalDecl) (slot : LocalSlot)
      (mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout),
      excl ≠ some i →
      get? body.localDecls i = some decl →
      get? af.locals i = some slot →
      mf.locals[i]? = some mls →
      LocalRelLM2_2 env mach decl body.layouts slot mls

namespace FrameRelLM2_2Except

theorem of_frameRel {body : CapturedMir} {env : StructTypeEnv}
    {mach : AnnealMachine} {af : StackFrame}
    {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (excl : Option Local) (h : FrameRelLM2_2 body env mach af mf) :
    FrameRelLM2_2Except body env excl mach af mf :=
  ⟨h.body_eq, h.location_eq, h.af_locals_len, h.mf_locals_size,
    fun i d sl ml _ hd hs hm => h.locals_rel i d sl ml hd hs hm⟩

theorem toFrameRel {body : CapturedMir} {env : StructTypeEnv}
    {mach : AnnealMachine} {af : StackFrame}
    {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (h : FrameRelLM2_2Except body env none mach af mf) :
    FrameRelLM2_2 body env mach af mf :=
  ⟨h.body_eq, h.location_eq, h.af_locals_len, h.mf_locals_size,
    fun i d sl ml hd hs hm => h.locals_rel i d sl ml nofun hd hs hm⟩

theorem lookup_local {body : CapturedMir} {env : StructTypeEnv} {excl : Option Local}
    {mach : AnnealMachine} {af : StackFrame}
    {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (h : FrameRelLM2_2Except body env excl mach af mf)
    {idx : Nat} {decl : LocalDecl}
    (hne : excl ≠ some idx)
    (hdecl : get? body.localDecls idx = some decl) :
    ∃ (slot : LocalSlot)
      (mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout)
      (hlt_mf : idx < mf.locals.size),
      idx < af.locals.length ∧
      get? af.locals idx = some slot ∧
      mf.locals[idx]? = some mls ∧
      mf.locals[idx]'hlt_mf = mls ∧
      LocalRelLM2_2 env mach decl body.layouts slot mls := by
  rw [get?_eq_getElem?] at hdecl
  obtain ⟨hlt_d, _⟩ := List.getElem?_eq_some_iff.mp hdecl
  have hlt_af : idx < af.locals.length := by rw [h.af_locals_len]; exact hlt_d
  have hlt_mf : idx < mf.locals.size := by rw [h.mf_locals_size]; exact hlt_d
  have hslot : get? af.locals idx = some (af.locals[idx]'hlt_af) := by
    rw [get?_eq_getElem?, List.getElem?_eq_getElem hlt_af]
  have hmls : mf.locals[idx]? = some (mf.locals[idx]'hlt_mf) :=
    Array.getElem?_eq_getElem hlt_mf
  exact ⟨af.locals[idx]'hlt_af, mf.locals[idx]'hlt_mf, hlt_mf, hlt_af, hslot, hmls, rfl,
    h.locals_rel idx decl _ _ hne hdecl hslot hmls⟩

theorem cache_local {body : CapturedMir} {env : StructTypeEnv} {excl : Option Local}
    {mach : AnnealMachine} {af : StackFrame}
    {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (h : FrameRelLM2_2Except body env excl mach af mf)
    {idx : Nat} {decl : LocalDecl}
    (hdecl : get? body.localDecls idx = some decl)
    (hlt_mf : idx < mf.locals.size) :
    FrameRelLM2_2Except body env excl mach af
      (cacheFrameLocalLayout mf idx hlt_mf (translateTy decl.ty body.layouts)) := by
  refine ⟨h.body_eq, h.location_eq, h.af_locals_len, by simp [cacheFrameLocalLayout, h.mf_locals_size], ?_⟩
  intro i d sl ml hne hd hs hm
  dsimp [cacheFrameLocalLayout] at hm
  by_cases hi : i = idx
  · subst hi
    rw [hdecl] at hd; injection hd with hd_eq; subst hd_eq
    rw [Array.getElem?_set_self hlt_mf] at hm
    injection hm with hml; subst hml
    exact (h.locals_rel i decl sl (mf.locals[i]'hlt_mf) hne hdecl hs
      (Array.getElem?_eq_getElem hlt_mf)).cache_layout
  · rw [Array.getElem?_set_ne _ (Ne.symm hi)] at hm
    exact h.locals_rel i d sl ml hne hd hs hm

theorem update_local {body : CapturedMir} {env : StructTypeEnv} {excl : Option Local}
    {mach : AnnealMachine} {af : StackFrame}
    {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (h : FrameRelLM2_2Except body env excl mach af mf)
    {idx : Nat} {decl : LocalDecl}
    (hdecl : get? body.localDecls idx = some decl)
    {hlt_mf : idx < mf.locals.size}
    (newSlot : LocalSlot)
    (newVal : Miri.Interpreter.LocalValue AnnealProv)
    (hnew : excl ≠ some idx →
      LocalRelLM2_2 env mach decl body.layouts newSlot
        { mf.locals[idx]'hlt_mf with value := newVal }) :
    FrameRelLM2_2Except body env excl mach
      { af with locals := af.locals.set idx newSlot }
      { mf with locals := mf.locals.set idx { mf.locals[idx]'hlt_mf with value := newVal } hlt_mf } := by
  refine ⟨h.body_eq, h.location_eq, by simp [h.af_locals_len], by simp [h.mf_locals_size], ?_⟩
  intro i d sl ml hne hd hs hm
  by_cases hi : i = idx
  · subst hi
    rw [hdecl] at hd; injection hd with hd_eq; subst hd_eq
    have hlt_af : i < af.locals.length := by
      rw [h.af_locals_len, ← h.mf_locals_size]; exact hlt_mf
    dsimp [get?] at hs
    rw [List.getElem?_set_self hlt_af] at hs; injection hs with hsl; subst hsl
    rw [Array.getElem?_set_self hlt_mf] at hm; injection hm with hml; subst hml
    exact hnew hne
  · dsimp [get?] at hs
    rw [List.getElem?_set_ne (Ne.symm hi)] at hs
    rw [Array.getElem?_set_ne _ (Ne.symm hi)] at hm
    exact h.locals_rel i d sl ml hne hd hs hm

end FrameRelLM2_2Except

theorem MemoryAllocDisjoint_deinitFrameLocal
    {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hdisj : MemoryAllocDisjoint mf)
    {idx : Nat} (hlt : idx < mf.locals.size) :
    MemoryAllocDisjoint (deinitFrameLocal mf idx hlt) := by
  intro i j mp₁ mp₂ l₁ l₂ hne hi hj
  dsimp [deinitFrameLocal] at hi hj
  by_cases h1 : i = idx
  · subst h1; rw [Array.getElem?_set_self hlt] at hi; cases hi
  · by_cases h2 : j = idx
    · subst h2; rw [Array.getElem?_set_self hlt] at hj; cases hj
    · rw [Array.getElem?_set_ne _ (Ne.symm h1)] at hi
      rw [Array.getElem?_set_ne _ (Ne.symm h2)] at hj
      exact hdisj i j mp₁ mp₂ l₁ l₂ hne hi hj

/-- 100% syntactic (state-independent) typing predicate for `LM-2.2` operands:
1. `constScalar`: primitive scalar constant;
2. `primLocal`: `Copy(_idx)` or `Move(_idx)` of a primitive scalar local with
   `idx ∈ stEnv.immLocals`;
3. `projectedScalar`: single or nested `.field` projection read (`Copy` or `Move`)
   satisfying `WellTypedLM2_2ProjectedRead`;
4. `immStructLocal`: `Copy(_idx)` or `Move(_idx)` of an immediate-ABI aggregate
   (`.Scalar` 1-field wrapper or `.ScalarPair` 2-scalar tuple/struct), valid
   whether `_idx` is currently `.structImm` or `.structInd`;
5. `projectedSubStruct`: single or nested `.field` projection read (`Copy` or
   `Move`) of a 2-scalar `.ScalarPair` sub-struct;
6. `projectedScalarWrap`: single or nested `.field` projection read (`Copy` or
   `Move`) of a 1-field `.Scalar` wrapper sub-struct. -/
inductive WellTypedLM2_2Operand
    (body : CapturedMir)
    (env : StructTypeEnv)
    (stEnv : LM2_2StaticEnv) :
    MirAst.Operand → Ty → Prop where
  | constScalar (c : ConstOperand) (sc : MirAst.ScalarInt) :
      c.val = .scalar (.int sc) →
      env c.ty = none →
      IsPrimScalarTy c.ty →
      ValidScalarBytes sc.sizeBytes →
      sc.bits < scalarModulus sc.sizeBytes →
      (translateTy c.ty body.layouts).layout.size = translateSizeBytes sc.sizeBytes →
      (c.ty.kind = .bool → sc.sizeBytes = 1 ∧ (sc.bits = 0 ∨ sc.bits = 1)) →
      (c.ty.kind = .char → sc.sizeBytes = 4 ∧ isValidCharCode sc.bits = true) →
      WellTypedLM2_2Operand body env stEnv (.constant c) c.ty
  | primLocal (isMove : Bool) (idx : Local) (decl : LocalDecl) :
      get? body.localDecls idx = some decl →
      env decl.ty = none →
      IsPrimScalarTy decl.ty →
      idx ∈ stEnv.immLocals →
      WellTypedLM2_2Operand body env stEnv (mkPlaceOperand isMove ⟨idx, []⟩) decl.ty
  | projectedScalar (isMove : Bool) (idx : Local)
      (projs : List ProjectionElem) (leafTy : Ty) :
      env leafTy = none →
      WellTypedLM2_2ProjectedRead body env idx projs leafTy →
      WellTypedLM2_2Operand body env stEnv (mkPlaceOperand isMove ⟨idx, projs⟩) leafTy
  | immStructLocal (isMove : Bool) (idx : Local) (decl : LocalDecl)
      (fields : List StructFieldDesc) (paths : List (List ProjectionElem)) :
      get? body.localDecls idx = some decl →
      IsImmediateStructTy env body.layouts decl.ty fields paths →
      WellTypedLM2_2Operand body env stEnv (mkPlaceOperand isMove ⟨idx, []⟩) decl.ty
  | projectedSubStruct (isMove : Bool) (idx : Local)
      (projs : List ProjectionElem) (subTy : Ty)
      (sf₀ sf₁ : StructFieldDesc) (mid₀ mid₁ : Ty) :
      IsImmediateStructTy env body.layouts subTy [sf₀, sf₁]
        [[.field 0 mid₀], [.field 1 mid₁]] →
      WellTypedLM2_2ProjectedSubStructRead body env idx projs subTy sf₀ sf₁ mid₀ mid₁ →
      WellTypedLM2_2Operand body env stEnv (mkPlaceOperand isMove ⟨idx, projs⟩) subTy
  | projectedScalarWrap (isMove : Bool) (idx : Local)
      (projs : List ProjectionElem) (subTy : Ty)
      (sf₀ : StructFieldDesc) (mid₀ : Ty) :
      IsImmediateStructTy env body.layouts subTy [sf₀]
        [[.field 0 mid₀]] →
      WellTypedLM2_2ProjectedScalarWrapRead body env idx projs subTy sf₀ mid₀ →
      WellTypedLM2_2Operand body env stEnv (mkPlaceOperand isMove ⟨idx, projs⟩) subTy

private theorem WellTypedLM2_2ProjectedSubStructRead.decl_and_chain
    {body : CapturedMir} {env : StructTypeEnv}
    {idx : Local} {projs : List ProjectionElem}
    {subTy : Ty} {sf₀ sf₁ : StructFieldDesc} {mid₀ mid₁ : Ty}
    (h : WellTypedLM2_2ProjectedSubStructRead body env idx projs subTy sf₀ sf₁ mid₀ mid₁) :
    ∃ decl subOff,
      get? body.localDecls idx = some decl ∧
      ValidFieldProjChain body.layouts (translateTy decl.ty body.layouts) projs subTy subOff := by
  rcases h with ⟨decl, _, _, _, _, _, _, _, _, subOff, _, _, _,
    hdecl, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hchain⟩
  exact ⟨decl, subOff, hdecl, hchain⟩

private theorem WellTypedLM2_2ProjectedScalarWrapRead.decl_and_chain
    {body : CapturedMir} {env : StructTypeEnv}
    {idx : Local} {projs : List ProjectionElem}
    {subTy : Ty} {sf₀ : StructFieldDesc} {mid₀ : Ty}
    (h : WellTypedLM2_2ProjectedScalarWrapRead body env idx projs subTy sf₀ mid₀) :
    ∃ decl subOff,
      get? body.localDecls idx = some decl ∧
      ValidFieldProjChain body.layouts (translateTy decl.ty body.layouts) projs subTy subOff := by
  rcases h with ⟨decl, _, _, _, _, _, subOff, _,
    hdecl, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hchain⟩
  exact ⟨decl, subOff, hdecl, hchain⟩

theorem IsPrimScalarTy.usesStructMemCopyDest_false
    {ty : Ty} {layouts : LayoutTable}
    (h : IsPrimScalarTy ty)
    (ref : Miri.Interpreter.RuntimePlaceRef AnnealProv) :
    usesStructMemCopyDest ⟨ref, translateTy ty layouts⟩ = false := by
  rcases ty with ⟨kind, layoutIdx⟩
  rcases h with hk | hk | ⟨it, hk⟩ | ⟨ut, hk⟩ <;> dsimp only at hk <;> subst hk <;> rfl

theorem IsImmediateStructTy.usesStructMemCopyDest_false
    {env : StructTypeEnv} {layouts : LayoutTable} {ty : Ty}
    {fields : List StructFieldDesc} {paths : List (List ProjectionElem)}
    (h : IsImmediateStructTy env layouts ty fields paths)
    (ref : Miri.Interpreter.RuntimePlaceRef AnnealProv) :
    usesStructMemCopyDest ⟨ref, translateTy ty layouts⟩ = false := by
  cases h with
  | scalarWrapper _ _ _ _ _ hrepr _ _ _ _ _ _ =>
    unfold usesStructMemCopyDest; dsimp only; rw [hrepr]
  | scalarPair _ _ _ _ _ _ _ _ _ _ _ _ _ _ hrepr _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    unfold usesStructMemCopyDest; dsimp only; rw [hrepr]

theorem WellTypedLM2_2Operand.usesStructMemCopyDest_false
    {body : CapturedMir} {env : StructTypeEnv} {stEnv : LM2_2StaticEnv}
    {op : MirAst.Operand} {ty : Ty}
    (h : WellTypedLM2_2Operand body env stEnv op ty)
    (ref : Miri.Interpreter.RuntimePlaceRef AnnealProv) :
    usesStructMemCopyDest ⟨ref, translateTy ty body.layouts⟩ = false := by
  cases h with
  | constScalar _ _ _ _ hprim _ _ _ _ _ => exact hprim.usesStructMemCopyDest_false ref
  | primLocal _ _ _ _ _ hprim _ => exact hprim.usesStructMemCopyDest_false ref
  | projectedScalar _ _ _ _ _ hproj =>
    rcases hproj with ⟨_, _, _, _, _, _, _, _, _, _, hprim, _⟩
    exact hprim.usesStructMemCopyDest_false ref
  | immStructLocal _ _ _ _ _ _ hspec => exact hspec.usesStructMemCopyDest_false ref
  | projectedSubStruct _ _ _ _ _ _ _ _ hspec _ => exact hspec.usesStructMemCopyDest_false ref
  | projectedScalarWrap _ _ _ _ _ _ hspec _ => exact hspec.usesStructMemCopyDest_false ref

theorem WellTypedLM2_2Operand.toSyntacticFieldOperand
    {body : CapturedMir} {env : StructTypeEnv} {stEnv : LM2_2StaticEnv}
    {op : MirAst.Operand} {ty : Ty} {numLocals : Nat}
    (hlen : numLocals = body.localDecls.length)
    (h : WellTypedLM2_2Operand body env stEnv op ty) :
    SyntacticFieldOperand numLocals op := by
  subst hlen
  cases h with
  | constScalar c sc hval _ _ _ _ _ _ _ => exact ⟨sc, hval⟩
  | primLocal isMove idx decl hdecl _ _ _ =>
    rw [get?_eq_getElem?] at hdecl
    have hlt := (List.getElem?_eq_some_iff.mp hdecl).1
    cases isMove <;> exact ⟨hlt, fun _ hp => nomatch hp⟩
  | projectedScalar isMove idx projs leafTy _ hproj =>
    rcases hproj with ⟨decl, _, _, _, _, _, hdecl, _, _, _, _, hchain⟩
    rw [get?_eq_getElem?] at hdecl
    have hlt := (List.getElem?_eq_some_iff.mp hdecl).1
    cases isMove <;> exact ⟨hlt, hchain.only_fields⟩
  | immStructLocal isMove idx decl _ _ hdecl _ =>
    rw [get?_eq_getElem?] at hdecl
    have hlt := (List.getElem?_eq_some_iff.mp hdecl).1
    cases isMove <;> exact ⟨hlt, fun _ hp => nomatch hp⟩
  | projectedSubStruct isMove idx projs _ _ _ _ _ _ hproj =>
    obtain ⟨decl, _, hdecl, hchain⟩ := hproj.decl_and_chain
    rw [get?_eq_getElem?] at hdecl
    have hlt := (List.getElem?_eq_some_iff.mp hdecl).1
    cases isMove <;> exact ⟨hlt, hchain.only_fields⟩
  | projectedScalarWrap isMove idx projs _ _ _ _ hproj =>
    obtain ⟨decl, _, hdecl, hchain⟩ := hproj.decl_and_chain
    rw [get?_eq_getElem?] at hdecl
    have hlt := (List.getElem?_eq_some_iff.mp hdecl).1
    cases isMove <;> exact ⟨hlt, hchain.only_fields⟩

/-- Typed value correspondence produced by `WellTypedLM2_2Operand`: either a
primitive scalar leaf or an immediate-ABI aggregate (`.Scalar` wrapper or
`.ScalarPair` tuple/struct). -/
inductive LM2_2OperandValRel (env : StructTypeEnv) (layouts : LayoutTable) (ty : Ty) :
    Value → Miri.Interpreter.Immediate AnnealProv → Prop where
  | primScalar (sc : MirAst.ScalarInt) (msc : Miri.Memory.ScalarInt) :
      env ty = none →
      IsPrimScalarTy ty →
      ImmediateRel ty layouts (.scalar sc) (.scalar (.fromScalarInt msc)) →
      LM2_2OperandValRel env layouts ty (.scalar sc) (.scalar (.fromScalarInt msc))
  | immStruct (fields : List StructFieldDesc) (paths : List (List ProjectionElem))
      (v : Value) (imm : Miri.Interpreter.Immediate AnnealProv) :
      IsImmediateStructTy env layouts ty fields paths →
      ImmediateStructRel ty layouts fields paths v imm →
      LM2_2OperandValRel env layouts ty v imm

/-- Joint outcome relation for `evalOperand` (Anneal) vs.
`annealEvalOperand >>= annealReadImmediate` (`lean-miri`) under `FrameRelLM2_2Except`. -/
inductive LM2_2OperandSimRel
    (body : CapturedMir)
    (env : StructTypeEnv)
    (stEnv' : LM2_2StaticEnv)
    (excl : Option Local)
    (af : StackFrame)
    (topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    (m : AnnealStepState)
    (op : MirAst.Operand)
    (ty : Ty) :
    OperandEvalResult →
    EStateM.Result Miri.Interpreter.StepError AnnealStepState
      (Miri.Interpreter.RvalueImmTy AnnealProv) →
    Prop where
  | ok (v : Value) (locals' : List LocalSlot)
      (topFrame' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
      (imm : Miri.Interpreter.Immediate AnnealProv)
      (outLay : Miri.Interpreter.LocalLayout) :
      FrameRelLM2_2Except body env excl m.machine { af with locals := locals' } topFrame' →
      LM2_2OperandValRel env body.layouts ty v imm →
      topFrame'.body = topFrame.body →
      topFrame'.location = topFrame.location →
      topFrame'.localsIdentity = topFrame.localsIdentity →
      topFrame'.returnContinuation = topFrame.returnContinuation →
      topFrame'.returnPlace = topFrame.returnPlace →
      topFrame'.locals.size = topFrame.locals.size →
      (∀ d, OperandDoesNotAccessLocal d op → topFrame'.locals[d]? = topFrame.locals[d]?) →
      (∀ d, OperandDoesNotMoveLocal d op →
        get? locals' d = get? af.locals d ∧
        ∀ v0 l0, topFrame.locals[d]? = some ⟨v0, some l0⟩ →
          ∃ l1, topFrame'.locals[d]? = some ⟨v0, some l1⟩) →
      (∀ j ∈ stEnv'.initLocals, excl ≠ some j → get? locals' j ≠ some .uninit) →
      (∀ j ∈ stEnv'.immLocals, excl ≠ some j → ∀ mp lay,
        topFrame'.locals[j]? ≠ some ⟨.live (.indirect mp), lay⟩) →
      (MemoryAllocDisjoint topFrame → MemoryAllocDisjoint topFrame') →
      LM2_2OperandSimRel body env stEnv' excl af topFrame m op ty
        (.ok v locals')
        (.ok ⟨imm, outLay⟩ { m with stack := ⟨#[topFrame']⟩ })
  | ub (m' : AnnealStepState) (msg : String) :
      LM2_2OperandSimRel body env stEnv' excl af topFrame m op ty
        .ub (.error (.undefinedBehavior msg) m')

private theorem unprojected_live_finish
    {body : CapturedMir} {env : StructTypeEnv} {stEnv : LM2_2StaticEnv}
    {excl : Option Local} {af : StackFrame}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {m : AnnealStepState} {isMove : Bool} {idx : Local} {decl : LocalDecl}
    {v : Value} {opVal : Miri.Interpreter.Operand AnnealProv}
    {imm : Miri.Interpreter.Immediate AnnealProv}
    {lay : Option Miri.Interpreter.LocalLayout}
    {globals : List CapturedAllocation}
    {known : Option Miri.Interpreter.LocalLayout}
    {hlt_mf : idx < topFrame.locals.size}
    (hframes : m.stack.frames = #[topFrame])
    (hframe : FrameRelLM2_2Except body env excl m.machine af topFrame)
    (hinit : ∀ j ∈ stEnv.initLocals, excl ≠ some j → get? af.locals j ≠ some .uninit)
    (himm_env : ∀ j ∈ stEnv.immLocals, excl ≠ some j → ∀ mp l,
      topFrame.locals[j]? ≠ some ⟨.live (.indirect mp), l⟩)
    (hdecl : get? body.localDecls idx = some decl)
    (hlt_af : idx < af.locals.length)
    (hslot : get? af.locals idx = some (.init v))
    (hmls_eq : topFrame.locals[idx]'hlt_mf = ⟨.live opVal, lay⟩)
    (hcache : ∀ l, lay = some l → l = translateTy decl.ty body.layouts)
    (hvalRel : LM2_2OperandValRel env body.layouts decl.ty v imm)
    (huninit_rel : ∀ c : Option Miri.Interpreter.LocalLayout,
      (∀ l ∈ c, l = translateTy decl.ty body.layouts) →
      LocalRelLM2_2 env m.machine decl body.layouts .uninit ⟨.live (.immediate .uninit), c⟩)
    (hread : ∀ tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit,
      annealReadImmediate ⟨opVal, translateTy decl.ty body.layouts⟩ { m with stack := ⟨#[tf]⟩ } =
        .ok ⟨imm, translateTy decl.ty body.layouts⟩ { m with stack := ⟨#[tf]⟩ }) :
    LM2_2OperandSimRel body env (operandPostStaticEnv stEnv (mkPlaceOperand isMove ⟨idx, []⟩))
      excl af topFrame m (mkPlaceOperand isMove ⟨idx, []⟩) decl.ty
      (evalOperand af.locals (mkPlaceOperand isMove ⟨idx, []⟩) .nil globals body.layouts .nil)
      ((annealEvalOperand body.localDecls body.layouts
          (translateOperand (mkPlaceOperand isMove ⟨idx, []⟩)) known >>=
        annealReadImmediate) m) := by
  let tf_c := cacheFrameLocalLayout topFrame idx hlt_mf (translateTy decl.ty body.layouts)
  have hfr_c := hframe.cache_local hdecl hlt_mf
  cases isMove with
  | false =>
    have hmk : mkPlaceOperand false ⟨idx, []⟩ = .copy ⟨idx, []⟩ := rfl
    have htr : translateOperand (.copy ⟨idx, []⟩) = .Copy ⟨idx, #[]⟩ := rfl
    have hpost : operandPostStaticEnv stEnv (.copy ⟨idx, []⟩) = stEnv := rfl
    rw [hmk, htr, hpost]
    have ha : evalOperand af.locals (.copy ⟨idx, []⟩) .nil globals body.layouts .nil =
        .ok v af.locals := by simp [evalOperand, readProjectedValue, hslot]
    have hm : (annealEvalOperand body.localDecls body.layouts (.Copy ⟨idx, #[]⟩) known >>=
        annealReadImmediate) m =
        .ok ⟨imm, translateTy decl.ty body.layouts⟩ { m with stack := ⟨#[tf_c]⟩ } := by
      rw [EStateM.bind_eq_ok (annealEvalOperand_copy_live hframes hlt_mf hdecl hmls_eq hcache)]
      exact hread tf_c
    rw [ha, hm]
    refine .ok v af.locals tf_c imm (translateTy decl.ty body.layouts) hfr_c hvalRel rfl rfl rfl rfl rfl
      (cacheFrameLocalLayout_size _ _ _) ?_ ?_ hinit ?_
      (fun hd => MemoryAllocDisjoint_cacheFrameLocalLayout hd hlt_mf _)
    · intro d hd
      have hne : idx ≠ d := hd
      dsimp [tf_c, cacheFrameLocalLayout]
      exact Array.getElem?_set_ne _ hne
    · intro d _
      refine ⟨rfl, fun v0 l0 h0 => ?_⟩
      dsimp [tf_c, cacheFrameLocalLayout]
      by_cases hd_eq : idx = d
      · subst hd_eq
        rw [Array.getElem?_eq_getElem hlt_mf] at h0
        have h0' := Option.some.inj h0
        exact ⟨_, by rw [Array.getElem?_set_self hlt_mf, h0']⟩
      · exact ⟨l0, by rw [Array.getElem?_set_ne _ hd_eq]; exact h0⟩
    · intro j hj hne_j mp l
      have hj_old := himm_env j hj hne_j mp
      dsimp [tf_c, cacheFrameLocalLayout]
      by_cases hij : idx = j
      · subst hij
        rw [Array.getElem?_set_self hlt_mf]
        intro heq; injection heq with hls
        rcases hls0 : topFrame.locals[idx]'hlt_mf with ⟨val0, lay0⟩
        rw [hls0] at hls
        injection hls with hv_eq _
        subst hv_eq
        exact hj_old lay0 (by rw [Array.getElem?_eq_getElem hlt_mf, hls0])
      · rw [Array.getElem?_set_ne _ hij]; exact hj_old l
  | true =>
    have hmk : mkPlaceOperand true ⟨idx, []⟩ = .move ⟨idx, []⟩ := rfl
    have htr : translateOperand (.move ⟨idx, []⟩) = .Move ⟨idx, #[]⟩ := rfl
    rw [hmk, htr]
    have hlt_c : idx < tf_c.locals.size := by rw [cacheFrameLocalLayout_size]; exact hlt_mf
    let tf_d := deinitFrameLocal tf_c idx hlt_c
    have ha : evalOperand af.locals (.move ⟨idx, []⟩) .nil globals body.layouts .nil =
        .ok v (af.locals.set idx .uninit) := by
      unfold evalOperand; dsimp only; rw [hslot]; dsimp only; rw [set?_eq_some_set hlt_af]
    have hm : (annealEvalOperand body.localDecls body.layouts (.Move ⟨idx, #[]⟩) known >>=
        annealReadImmediate) m =
        .ok ⟨imm, translateTy decl.ty body.layouts⟩ { m with stack := ⟨#[tf_d]⟩ } := by
      rw [EStateM.bind_eq_ok (annealEvalOperand_move_live hframes hlt_mf hdecl hmls_eq hcache)]
      exact hread tf_d
    rw [ha, hm]
    have hc_lay? : tf_c.locals[idx]? =
        some { (topFrame.locals[idx]'hlt_mf) with
          layout := some (translateTy decl.ty body.layouts) } := by
      show (cacheFrameLocalLayout topFrame idx hlt_mf _).locals[idx]? = _
      dsimp only [cacheFrameLocalLayout]
      exact Array.getElem?_set_self hlt_mf
    have hc_some : ∀ l ∈ (tf_c.locals[idx]'hlt_c).layout,
        l = translateTy decl.ty body.layouts := by
      intro l hl
      have hget : tf_c.locals[idx]? = some (tf_c.locals[idx]'hlt_c) :=
        Array.getElem?_eq_getElem hlt_c
      rw [hget] at hc_lay?
      injection hc_lay? with heq_ls
      rw [heq_ls] at hl
      exact (Option.some.inj (Option.mem_def.mp hl)).symm
    have hfr_d : FrameRelLM2_2Except body env excl m.machine
        { af with locals := af.locals.set idx .uninit } tf_d :=
      hfr_c.update_local hdecl .uninit (.live (.immediate .uninit))
        (fun _ => huninit_rel _ hc_some)
    have hsz_d : tf_d.locals.size = topFrame.locals.size := by
      show (deinitFrameLocal tf_c idx hlt_c).locals.size = _
      dsimp only [deinitFrameLocal]
      rw [Array.size_set, cacheFrameLocalLayout_size]
    refine .ok v (af.locals.set idx .uninit) tf_d imm (translateTy decl.ty body.layouts) hfr_d hvalRel rfl rfl rfl rfl rfl
      hsz_d ?_ ?_ ?_ ?_
      (fun hd => MemoryAllocDisjoint_deinitFrameLocal
        (MemoryAllocDisjoint_cacheFrameLocalLayout hd hlt_mf _) hlt_c)
    · intro d hd
      have hne : idx ≠ d := hd
      dsimp [tf_d, deinitFrameLocal]
      rw [Array.getElem?_set_ne _ hne]
      dsimp [tf_c, cacheFrameLocalLayout]
      exact Array.getElem?_set_ne _ hne
    · intro d hd
      have hne : idx ≠ d := hd
      refine ⟨by simp [get?, List.getElem?_set_ne hne], fun v0 l0 h0 => ⟨l0, ?_⟩⟩
      dsimp [tf_d, deinitFrameLocal]
      rw [Array.getElem?_set_ne _ hne]
      dsimp [tf_c, cacheFrameLocalLayout]
      rw [Array.getElem?_set_ne _ hne]
      exact h0
    · intro j hj hne_j
      dsimp [operandPostStaticEnv] at hj
      rw [List.mem_filter] at hj
      obtain ⟨hj_mem, hj_ne⟩ := hj
      have hij : idx ≠ j := by
        intro rfl; simp at hj_ne
      dsimp [get?]
      rw [List.getElem?_set_ne hij, ← get?_eq_getElem?]
      exact hinit j hj_mem hne_j
    · intro j hj hne_j mp l
      dsimp [operandPostStaticEnv] at hj
      dsimp [tf_d, deinitFrameLocal]
      by_cases hij : idx = j
      · subst hij; rw [Array.getElem?_set_self hlt_c]; nofun
      · rw [Array.getElem?_set_ne _ hij]
        dsimp [tf_c, cacheFrameLocalLayout]
        rw [Array.getElem?_set_ne _ hij]
        rcases List.mem_cons.mp hj with rfl | hj_old
        · exact False.elim (hij rfl)
        · exact himm_env j hj_old hne_j mp l

private theorem unprojected_dead_or_uninit_ub
    {body : CapturedMir} {env : StructTypeEnv} {stEnv' : LM2_2StaticEnv}
    {excl : Option Local} {af : StackFrame}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {m : AnnealStepState} {isMove : Bool} {idx : Local} {decl : LocalDecl}
    {lay : Option Miri.Interpreter.LocalLayout}
    {globals : List CapturedAllocation}
    {known : Option Miri.Interpreter.LocalLayout}
    {hlt_mf : idx < topFrame.locals.size}
    (hframes : m.stack.frames = #[topFrame])
    (hdecl : get? body.localDecls idx = some decl)
    (hcache : ∀ l, lay = some l → l = translateTy decl.ty body.layouts)
    (hdead_or_uninit :
      (get? af.locals idx = some .dead ∧ topFrame.locals[idx]'hlt_mf = ⟨.dead, lay⟩) ∨
      (get? af.locals idx = some .uninit ∧
        topFrame.locals[idx]'hlt_mf = ⟨.live (.immediate .uninit), lay⟩)) :
    LM2_2OperandSimRel body env stEnv' excl af topFrame m
      (mkPlaceOperand isMove ⟨idx, []⟩) decl.ty
      (evalOperand af.locals (mkPlaceOperand isMove ⟨idx, []⟩) .nil globals body.layouts .nil)
      ((annealEvalOperand body.localDecls body.layouts
          (translateOperand (mkPlaceOperand isMove ⟨idx, []⟩)) known >>=
        annealReadImmediate) m) := by
  have hmk_f : mkPlaceOperand false ⟨idx, []⟩ = .copy ⟨idx, []⟩ := rfl
  have hmk_t : mkPlaceOperand true ⟨idx, []⟩ = .move ⟨idx, []⟩ := rfl
  have htr_f : translateOperand (.copy ⟨idx, []⟩) = .Copy ⟨idx, #[]⟩ := rfl
  have htr_t : translateOperand (.move ⟨idx, []⟩) = .Move ⟨idx, #[]⟩ := rfl
  rcases hdead_or_uninit with ⟨hslot, hmls_eq⟩ | ⟨hslot, hmls_eq⟩
  · cases isMove with
    | false =>
      rw [hmk_f, htr_f]
      have ha : evalOperand af.locals (.copy ⟨idx, []⟩) .nil globals body.layouts .nil = .ub := by
        simp [evalOperand, hslot]
      rw [ha, EStateM.bind_eq_error (annealEvalOperand_copy_dead hframes hlt_mf hdecl hmls_eq hcache)]
      exact .ub _ _
    | true =>
      rw [hmk_t, htr_t]
      have ha : evalOperand af.locals (.move ⟨idx, []⟩) .nil globals body.layouts .nil = .ub := by
        simp [evalOperand, hslot]
      rw [ha, EStateM.bind_eq_error (annealEvalOperand_move_dead hframes hlt_mf hdecl hmls_eq hcache)]
      exact .ub _ _
  · cases isMove with
    | false =>
      rw [hmk_f, htr_f]
      have ha : evalOperand af.locals (.copy ⟨idx, []⟩) .nil globals body.layouts .nil = .ub := by
        simp [evalOperand, hslot]
      rw [ha, EStateM.bind_eq_ok (annealEvalOperand_copy_live hframes hlt_mf hdecl hmls_eq hcache)]
      exact .ub _ _
    | true =>
      rw [hmk_t, htr_t]
      have ha : evalOperand af.locals (.move ⟨idx, []⟩) .nil globals body.layouts .nil = .ub := by
        simp [evalOperand, hslot]
      rw [ha, EStateM.bind_eq_ok (annealEvalOperand_move_live hframes hlt_mf hdecl hmls_eq hcache)]
      exact .ub _ _

theorem IsImmediateStructTy.env_eq
    {env : StructTypeEnv} {layouts : LayoutTable} {ty : Ty}
    {fields : List StructFieldDesc} {paths : List (List ProjectionElem)}
    (h : IsImmediateStructTy env layouts ty fields paths) :
    env ty = some (fields, paths) := by
  cases h with
  | scalarWrapper _ _ _ he _ _ _ _ _ _ _ _ => exact he
  | scalarPair _ _ _ _ _ _ _ _ _ he _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => exact he

theorem evalLM2_2Operand_except
    {body : CapturedMir} {env : StructTypeEnv} {stEnv : LM2_2StaticEnv}
    {excl : Option Local} {af : StackFrame}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {m : AnnealStepState} {op : MirAst.Operand} {ty : Ty}
    (hframes : m.stack.frames = #[topFrame])
    (hframe : FrameRelLM2_2Except body env excl m.machine af topFrame)
    (hinit : ∀ j ∈ stEnv.initLocals, excl ≠ some j → get? af.locals j ≠ some .uninit)
    (himm_env : ∀ j ∈ stEnv.immLocals, excl ≠ some j → ∀ mp l,
      topFrame.locals[j]? ≠ some ⟨.live (.indirect mp), l⟩)
    (hno_excl : ∀ d, excl = some d → OperandDoesNotAccessLocal d op)
    (hop : WellTypedLM2_2Operand body env stEnv op ty)
    (globals : List CapturedAllocation)
    (known : Option Miri.Interpreter.LocalLayout) :
    LM2_2OperandSimRel body env (operandPostStaticEnv stEnv op) excl af topFrame m op ty
      (evalOperand af.locals op .nil globals body.layouts .nil)
      ((annealEvalOperand body.localDecls body.layouts (translateOperand op) known >>=
        annealReadImmediate) m) := by
  have hsame : { m with stack := ⟨#[topFrame]⟩ } = m :=
    stepState_with_same_singleton m topFrame hframes
  cases hop with
  | constScalar c sc hval henv hprim hsz hcan hlaysz hbool hchar =>
    obtain ⟨msc, htry, hrel⟩ := tryFromUInt_of_valid_canonical hsz hcan
    have ha : evalOperand af.locals (.constant c) .nil globals body.layouts .nil =
        .ok (.scalar sc) af.locals := by unfold evalOperand; dsimp only; rw [hval]; rfl
    have hm : annealEvalOperand body.localDecls body.layouts
        (translateOperand (.constant c)) known m =
        .ok ⟨.immediate (.scalar (.fromScalarInt msc)), translateTy c.ty body.layouts⟩ m := by
      with_unfolding_all
        unfold translateOperand translateConstOperand annealEvalOperand evalMirConstImmediate
        dsimp only; rw [hval]
        simp only [translateConstValue, translateConstScalar, get, getThe, MonadStateOf.get,
          EStateM.get, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
          stack_currentFrame?_singleton m.stack topFrame hframes, Option.isNone_some,
          Bool.false_eq_true, ↓reduceIte, htry, hprim.layoutOfEncoded]
    rw [ha, EStateM.bind_eq_ok hm]
    dsimp [operandPostStaticEnv]
    change LM2_2OperandSimRel body env stEnv excl af topFrame m (.constant c) c.ty
      (.ok (.scalar sc) af.locals)
      (.ok ⟨.scalar (.fromScalarInt msc), translateTy c.ty body.layouts⟩ m)
    rw [← hsame]
    exact .ok (.scalar sc) af.locals topFrame (.scalar (.fromScalarInt msc))
      (translateTy c.ty body.layouts)
      hframe (.primScalar sc msc henv hprim (.scalar sc msc hrel hlaysz hbool hchar))
      rfl rfl rfl rfl rfl rfl (fun _ _ => rfl)
      (fun _ _ => ⟨rfl, fun _ l0 h0 => ⟨l0, h0⟩⟩)
      hinit himm_env (fun hd => hd)
  | primLocal isMove idx decl hdecl henv hprim himm_mem =>
    have hne_excl : excl ≠ some idx := by
      intro heq; have hna := hno_excl idx heq; cases isMove <;> exact hna rfl
    obtain ⟨slot, mls, hlt_mf, hlt_af, hslot, hmls, hmls_eq, hloc⟩ :=
      hframe.lookup_local hne_excl hdecl
    cases hloc with
    | structDead _ _ _ he _ | structUninitImm _ _ _ he _ | structUninitInd _ _ _ _ he _ _
    | structImm _ _ _ _ _ he _ _ | structInd _ _ _ _ _ he _ _ =>
      rw [henv] at he; cases he
    | base _ _ _ hb =>
      have hcache := hb.layout_eq
      cases hb with
      | dead c _ =>
        exact unprojected_dead_or_uninit_ub hframes hdecl hcache (Or.inl ⟨hslot, hmls_eq⟩)
      | indirect _ mp c _ _ _ =>
        exact False.elim (himm_env idx himm_mem hne_excl mp c hmls)
      | immediate _ imm c _ hval =>
        rcases hval with ⟨rfl, rfl⟩ | ⟨v, rfl, himmRel⟩
        · exact unprojected_dead_or_uninit_ub hframes hdecl hcache (Or.inr ⟨hslot, hmls_eq⟩)
        · obtain ⟨sc, msc, rfl, rfl, _⟩ := himmRel.of_primitive_scalar hprim
          exact unprojected_live_finish hframes hframe hinit himm_env hdecl hlt_af hslot hmls_eq
            hcache (.primScalar sc msc henv hprim himmRel)
            (fun c' hc' => .base .uninit _ henv (.immediate .uninit .uninit c' hc' (Or.inl ⟨rfl, rfl⟩)))
            (fun _ => rfl)
  | projectedScalar isMove idx projs leafTy henv_leaf hproj =>
    rcases hproj with ⟨decl, fields, paths, k, hk_f, hk_p, hdecl, henv, hpath_k, hty_k, hprim_leaf, hchain⟩
    have hne_excl : excl ≠ some idx := by
      intro heq; have hna := hno_excl idx heq; cases isMove <;> exact hna rfl
    obtain ⟨slot, mls, hlt_mf, _, hslot, _, hmls_eq, hloc⟩ :=
      hframe.lookup_local hne_excl hdecl
    have hp_ne : projs ≠ [] := hchain.ne_nil
    have hpost_eq : operandPostStaticEnv stEnv (mkPlaceOperand isMove ⟨idx, projs⟩) = stEnv := by
      cases projs with
      | nil => exact False.elim (hp_ne rfl)
      | cons _ _ => cases isMove <;> rfl
    rw [hpost_eq]
    rcases evalProjection_nested_field_read_at_local hframes hdecl hlt_mf hslot hmls_eq hloc
        ⟨decl, fields, paths, k, hk_f, hk_p, hdecl, henv, hpath_k, hty_k, hprim_leaf, hchain⟩
        globals known with
      ⟨sc, msc, outLay, ha, hm, himmRel⟩ | ⟨msg, m', ha, hm⟩
    · rw [ha, hm]
      let tf_c := cacheFrameLocalLayout topFrame idx hlt_mf (translateTy decl.ty body.layouts)
      refine .ok (.scalar sc) af.locals tf_c (.scalar (.fromScalarInt msc)) outLay
        (hframe.cache_local hdecl hlt_mf)
        (.primScalar sc msc henv_leaf hprim_leaf himmRel)
        rfl rfl rfl rfl rfl (cacheFrameLocalLayout_size _ _ _) ?_ ?_ hinit ?_
        (fun hd => MemoryAllocDisjoint_cacheFrameLocalLayout hd hlt_mf _)
      · intro d hd
        have hne : idx ≠ d := by cases isMove <;> exact hd
        dsimp [tf_c, cacheFrameLocalLayout]
        exact Array.getElem?_set_ne _ hne
      · intro d _
        refine ⟨rfl, fun v0 l0 h0 => ?_⟩
        dsimp [tf_c, cacheFrameLocalLayout]
        by_cases hd_eq : idx = d
        · subst hd_eq
          rw [Array.getElem?_eq_getElem hlt_mf] at h0
          have h0' := Option.some.inj h0
          exact ⟨_, by rw [Array.getElem?_set_self hlt_mf, h0']⟩
        · exact ⟨l0, by rw [Array.getElem?_set_ne _ hd_eq]; exact h0⟩
      · intro j hj hne_j mp l
        have hj_old := himm_env j hj hne_j mp
        dsimp [tf_c, cacheFrameLocalLayout]
        by_cases hij : idx = j
        · subst hij
          rw [Array.getElem?_set_self hlt_mf]
          intro heq; injection heq with hls
          rcases hls0 : topFrame.locals[idx]'hlt_mf with ⟨val0, lay0⟩
          rw [hls0] at hls
          injection hls with hv_eq _
          subst hv_eq
          exact hj_old lay0 (by rw [Array.getElem?_eq_getElem hlt_mf, hls0])
        · rw [Array.getElem?_set_ne _ hij]; exact hj_old l
    · rw [ha, hm]; exact .ub _ _
  | immStructLocal isMove idx decl fields paths hdecl hspec =>
    have henv := hspec.env_eq
    have hne_excl : excl ≠ some idx := by
      intro heq; have hna := hno_excl idx heq; cases isMove <;> exact hna rfl
    obtain ⟨slot, mls, hlt_mf, hlt_af, hslot, _, hmls_eq, hloc⟩ :=
      hframe.lookup_local hne_excl hdecl
    have hcache := hloc.layout_eq
    cases hloc with
    | base _ _ he_none _ => rw [henv] at he_none; cases he_none
    | structDead _ _ c _ _ =>
      exact unprojected_dead_or_uninit_ub hframes hdecl hcache (Or.inl ⟨hslot, hmls_eq⟩)
    | structUninitImm _ _ c _ _ =>
      exact unprojected_dead_or_uninit_ub hframes hdecl hcache (Or.inr ⟨hslot, hmls_eq⟩)
    | structUninitInd f' p' mp c henv' _ hmp =>
      rw [henv] at henv'
      simp only [Option.some.injEq, Prod.mk.injEq] at henv'
      rcases henv' with ⟨rfl, rfl⟩
      cases isMove with
      | false =>
        have hmk : mkPlaceOperand false ⟨idx, []⟩ = .copy ⟨idx, []⟩ := rfl
        have htr : translateOperand (.copy ⟨idx, []⟩) = .Copy ⟨idx, #[]⟩ := rfl
        rw [hmk, htr]
        have ha : evalOperand af.locals (.copy ⟨idx, []⟩) .nil globals body.layouts .nil = .ub := by
          simp [evalOperand, hslot]
        let tf_c := cacheFrameLocalLayout topFrame idx hlt_mf (translateTy decl.ty body.layouts)
        obtain ⟨msg, hub⟩ := hmp.readIndirect_ub_of_isImmediateStructTy
          (m := { m with stack := ⟨#[tf_c]⟩ }) hspec
        rw [ha, EStateM.bind_eq_ok (annealEvalOperand_copy_live hframes hlt_mf hdecl hmls_eq hcache)]
        dsimp [annealReadImmediate]
        rw [hub]; exact .ub _ _
      | true =>
        have hmk : mkPlaceOperand true ⟨idx, []⟩ = .move ⟨idx, []⟩ := rfl
        have htr : translateOperand (.move ⟨idx, []⟩) = .Move ⟨idx, #[]⟩ := rfl
        rw [hmk, htr]
        have ha : evalOperand af.locals (.move ⟨idx, []⟩) .nil globals body.layouts .nil = .ub := by
          simp [evalOperand, hslot]
        let tf_c := cacheFrameLocalLayout topFrame idx hlt_mf (translateTy decl.ty body.layouts)
        have hlt_c : idx < tf_c.locals.size := by rw [cacheFrameLocalLayout_size]; exact hlt_mf
        let tf_d := deinitFrameLocal tf_c idx hlt_c
        obtain ⟨msg, hub⟩ := hmp.readIndirect_ub_of_isImmediateStructTy
          (m := { m with stack := ⟨#[tf_d]⟩ }) hspec
        rw [ha, EStateM.bind_eq_ok (annealEvalOperand_move_live hframes hlt_mf hdecl hmls_eq hcache)]
        dsimp [annealReadImmediate]
        rw [hub]; exact .ub _ _
    | structImm f' p' v imm c henv' _ himm =>
      rw [henv] at henv'
      simp only [Option.some.injEq, Prod.mk.injEq] at henv'
      rcases henv' with ⟨rfl, rfl⟩
      exact unprojected_live_finish hframes hframe hinit himm_env hdecl hlt_af hslot hmls_eq
        hcache (.immStruct fields paths v imm hspec himm)
        (fun c' hc' => .structUninitImm fields paths c' henv hc')
        (fun _ => by cases himm <;> rfl)
    | structInd f' p' v mp c henv' _ hmp =>
      rw [henv] at henv'
      simp only [Option.some.injEq, Prod.mk.injEq] at henv'
      rcases henv' with ⟨rfl, rfl⟩
      obtain ⟨imm, himm, hread_ind⟩ := hmp.toImmediateStructRel hspec
      exact unprojected_live_finish hframes hframe hinit himm_env hdecl hlt_af hslot hmls_eq
        hcache (.immStruct fields paths v imm hspec himm)
        (fun c' hc' => .structUninitImm fields paths c' henv hc')
        (fun tf => hread_ind { m with stack := ⟨#[tf]⟩ } rfl)
  | projectedSubStruct isMove idx projs _ sf₀ sf₁ mid₀ mid₁ hspec hproj =>
    obtain ⟨decl, _, hdecl, hchain⟩ := hproj.decl_and_chain
    have hne_excl : excl ≠ some idx := by
      intro heq; have hna := hno_excl idx heq; cases isMove <;> exact hna rfl
    obtain ⟨slot, mls, hlt_mf, _, hslot, _, hmls_eq, hloc⟩ :=
      hframe.lookup_local hne_excl hdecl
    have hp_ne : projs ≠ [] := hchain.ne_nil
    have hpost_eq : operandPostStaticEnv stEnv (mkPlaceOperand isMove ⟨idx, projs⟩) = stEnv := by
      cases projs with
      | nil => exact False.elim (hp_ne rfl)
      | cons _ _ => cases isMove <;> rfl
    rw [hpost_eq]
    rcases evalProjection_nested_substruct_read_at_local hframes hdecl hlt_mf hslot hmls_eq hloc
        hproj globals known with
      ⟨sc₀, sc₁, msc₀, msc₁, outLay, ha, hm, himm_sub, _⟩ | ⟨msg, m', ha, hm⟩
    · rw [ha, hm]
      let tf_c := cacheFrameLocalLayout topFrame idx hlt_mf (translateTy decl.ty body.layouts)
      refine .ok (.aggregate 0 [.scalar sc₀, .scalar sc₁]) af.locals tf_c
        (.scalarPair (.fromScalarInt msc₀) (.fromScalarInt msc₁)) outLay
        (hframe.cache_local hdecl hlt_mf)
        (.immStruct [sf₀, sf₁] [[.field 0 mid₀], [.field 1 mid₁]] _ _ hspec himm_sub)
        rfl rfl rfl rfl rfl (cacheFrameLocalLayout_size _ _ _) ?_ ?_ hinit ?_
        (fun hd => MemoryAllocDisjoint_cacheFrameLocalLayout hd hlt_mf _)
      · intro d hd
        have hne : idx ≠ d := by cases isMove <;> exact hd
        dsimp [tf_c, cacheFrameLocalLayout]
        exact Array.getElem?_set_ne _ hne
      · intro d _
        refine ⟨rfl, fun v0 l0 h0 => ?_⟩
        dsimp [tf_c, cacheFrameLocalLayout]
        by_cases hd_eq : idx = d
        · subst hd_eq
          rw [Array.getElem?_eq_getElem hlt_mf] at h0
          have h0' := Option.some.inj h0
          exact ⟨_, by rw [Array.getElem?_set_self hlt_mf, h0']⟩
        · exact ⟨l0, by rw [Array.getElem?_set_ne _ hd_eq]; exact h0⟩
      · intro j hj hne_j mp l
        have hj_old := himm_env j hj hne_j mp
        dsimp [tf_c, cacheFrameLocalLayout]
        by_cases hij : idx = j
        · subst hij
          rw [Array.getElem?_set_self hlt_mf]
          intro heq; injection heq with hls
          rcases hls0 : topFrame.locals[idx]'hlt_mf with ⟨val0, lay0⟩
          rw [hls0] at hls
          injection hls with hv_eq _
          subst hv_eq
          exact hj_old lay0 (by rw [Array.getElem?_eq_getElem hlt_mf, hls0])
        · rw [Array.getElem?_set_ne _ hij]; exact hj_old l
    · rw [ha, hm]; exact .ub _ _
  | projectedScalarWrap isMove idx projs _ sf₀ mid₀ hspec hproj =>
    obtain ⟨decl, _, hdecl, hchain⟩ := hproj.decl_and_chain
    have hne_excl : excl ≠ some idx := by
      intro heq; have hna := hno_excl idx heq; cases isMove <;> exact hna rfl
    obtain ⟨slot, mls, hlt_mf, _, hslot, _, hmls_eq, hloc⟩ :=
      hframe.lookup_local hne_excl hdecl
    have hp_ne : projs ≠ [] := hchain.ne_nil
    have hpost_eq : operandPostStaticEnv stEnv (mkPlaceOperand isMove ⟨idx, projs⟩) = stEnv := by
      cases projs with
      | nil => exact False.elim (hp_ne rfl)
      | cons _ _ => cases isMove <;> rfl
    rw [hpost_eq]
    rcases evalProjection_nested_scalar_wrap_read_at_local hframes hdecl hlt_mf hslot hmls_eq hloc
        hproj globals known with
      ⟨sc₀, msc₀, outLay, ha, hm, himm_sub⟩ | ⟨msg, m', ha, hm⟩
    · rw [ha, hm]
      let tf_c := cacheFrameLocalLayout topFrame idx hlt_mf (translateTy decl.ty body.layouts)
      refine .ok (.aggregate 0 [.scalar sc₀]) af.locals tf_c
        (.scalar (.fromScalarInt msc₀)) outLay
        (hframe.cache_local hdecl hlt_mf)
        (.immStruct [sf₀] [[.field 0 mid₀]] _ _ hspec himm_sub)
        rfl rfl rfl rfl rfl (cacheFrameLocalLayout_size _ _ _) ?_ ?_ hinit ?_
        (fun hd => MemoryAllocDisjoint_cacheFrameLocalLayout hd hlt_mf _)
      · intro d hd
        have hne : idx ≠ d := by cases isMove <;> exact hd
        dsimp [tf_c, cacheFrameLocalLayout]
        exact Array.getElem?_set_ne _ hne
      · intro d _
        refine ⟨rfl, fun v0 l0 h0 => ?_⟩
        dsimp [tf_c, cacheFrameLocalLayout]
        by_cases hd_eq : idx = d
        · subst hd_eq
          rw [Array.getElem?_eq_getElem hlt_mf] at h0
          have h0' := Option.some.inj h0
          exact ⟨_, by rw [Array.getElem?_set_self hlt_mf, h0']⟩
        · exact ⟨l0, by rw [Array.getElem?_set_ne _ hd_eq]; exact h0⟩
      · intro j hj hne_j mp l
        have hj_old := himm_env j hj hne_j mp
        dsimp [tf_c, cacheFrameLocalLayout]
        by_cases hij : idx = j
        · subst hij
          rw [Array.getElem?_set_self hlt_mf]
          intro heq; injection heq with hls
          rcases hls0 : topFrame.locals[idx]'hlt_mf with ⟨val0, lay0⟩
          rw [hls0] at hls
          injection hls with hv_eq _
          subst hv_eq
          exact hj_old lay0 (by rw [Array.getElem?_eq_getElem hlt_mf, hls0])
        · rw [Array.getElem?_set_ne _ hij]; exact hj_old l
    · rw [ha, hm]; exact .ub _ _


/-! ## 5. Partial Struct Allocation State & Syntactic Aggregate Typing -/

private theorem NoZeroByteLeavesList.append_singleton {vs : List Value} {v : Value}
    (hvs : NoZeroByteLeavesList vs) (hv : NoZeroByteLeaves v) :
    NoZeroByteLeavesList (vs ++ [v]) := by
  induction vs with
  | nil => exact ⟨hv, True.intro⟩
  | cons hd tl ih => exact ⟨hvs.1, ih hvs.2⟩

private theorem valueLeafBytesList_append_singleton (vs : List Value) (v : Value) :
    valueLeafBytes.valueLeafBytesList (vs ++ [v]) =
      valueLeafBytes.valueLeafBytesList vs + valueLeafBytes v := by
  induction vs with
  | nil => simp [valueLeafBytes.valueLeafBytesList]
  | cons hd tl ih =>
    dsimp [valueLeafBytes.valueLeafBytesList]
    rw [ih]
    omega

private theorem structSumFieldBytes_append (xs ys : List StructFieldDesc) :
    structSumFieldBytes (xs ++ ys) =
      structSumFieldBytes xs + structSumFieldBytes ys := by
  induction xs with
  | nil => simp [structSumFieldBytes]
  | cons hd tl ih =>
    dsimp [structSumFieldBytes]
    rw [ih]
    omega

private theorem translateSizeBytes_pos_of_valid {n : Nat} (h : ValidScalarBytes n) :
    0 < (translateSizeBytes n).bytes.toNat := by
  rcases h with rfl | rfl | rfl | rfl | rfl <;> decide

private theorem structSumFieldBytes_take_succ {fields : List StructFieldDesc}
    {k : Nat} (hk : k < fields.length) :
    structSumFieldBytes (fields.take (k + 1)) =
      structSumFieldBytes (fields.take k) +
        (fields[k]'hk).fieldLayout.size.bytes.toNat := by
  induction fields generalizing k with
  | nil => cases hk
  | cons hd tl ih =>
    cases k with
    | zero => simp [structSumFieldBytes]
    | succ k' =>
      have hk' : k' < tl.length := Nat.lt_of_succ_lt_succ hk
      dsimp [List.take, structSumFieldBytes]
      rw [ih hk']
      omega

/-- Allocation-level invariant after writing the first `doneVals.length`
constructor fields (covering the first `k ≤ fields.length` scalar leaf
descriptors) into `alloc`. Every padding byte in `fields` remains `.uninit`
throughout construction. -/
structure PartialStructState
    (layouts : LayoutTable) (ty : Ty)
    (fields : List StructFieldDesc) (paths : List (List ProjectionElem))
    (k : Nat) (doneVals : List Value)
    (alloc : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree))
    (words : Array UInt64) : Prop where
  valid_layout : ValidStructLayout (translateTy ty layouts).layout fields
  paths_len : paths.length = fields.length
  hk_le : k ≤ fields.length
  vals_nz : NoZeroByteLeavesList doneVals
  vals_bytes : valueLeafBytes.valueLeafBytesList doneVals = structSumFieldBytes (fields.take k)
  mut_alloc : alloc.mutability = .Mut
  byteSize_eq : alloc.byteSize = (translateTy ty layouts).layout.size
  alloc_len_eq : alloc.len = alloc.byteSize.bytes.toNat
  prov_empty : alloc.provenanceMap = Miri.Memory.ProvenanceMap.new
  mask_rel : InitMaskWordRel alloc.initializationMask alloc.byteSize words
  word_bits_init :
    ∀ i (hi : i < k) b,
      (fields[i]'(Nat.lt_of_lt_of_le hi hk_le)).offset.bytes.toNat ≤ b →
      b < (fields[i]'(Nat.lt_of_lt_of_le hi hk_le)).offset.bytes.toNat +
        (fields[i]'(Nat.lt_of_lt_of_le hi hk_le)).fieldLayout.size.bytes.toNat →
      maskBlocksGetBit words b = true
  fields_rel :
    ∀ i (hi : i < k),
      let hi_f : i < fields.length := Nat.lt_of_lt_of_le hi hk_le
      let f := fields[i]'hi_f
      let path := paths[i]'(by rw [paths_len]; exact hi_f)
      path ≠ [] ∧
      f.fieldLayout = (translateTy f.ty layouts).layout ∧
      IsPrimScalarTy f.ty ∧
      (∀ sfx, ValidAggregateFieldPath layouts (.aggregate 0 (doneVals ++ sfx)) path) ∧
      ∃ sc msc,
        (∀ sfx, readProjectedValue [] (.aggregate 0 (doneVals ++ sfx)) path = .ok (.scalar sc)) ∧
        ScalarRel sc msc ∧
        f.fieldLayout.size = translateSizeBytes sc.sizeBytes ∧
        (f.ty.kind = .bool → sc.sizeBytes = 1 ∧ (sc.bits = 0 ∨ sc.bits = 1)) ∧
        (f.ty.kind = .char → sc.sizeBytes = 4 ∧ isValidCharCode sc.bits = true) ∧
        alloc.initializationMask.isRangeInitialized
          (Miri.Memory.allocRange f.offset f.fieldLayout.size) = .ok (.ok ()) ∧
        alloc.readScalar annealTargetDataLayout
          (Miri.Memory.allocRange f.offset f.fieldLayout.size) false = .ok (.fromScalarInt msc)
  padding_uninit :
    ∀ p, isStructPaddingByte fields (translateTy ty layouts).layout.size p →
      alloc.initializationMask.get (Miri.ABI.Size.ofBytes (UInt64.ofNat p)) = .ok false

namespace PartialStructState

theorem of_zero_word {layouts : LayoutTable} {ty : Ty}
    {fields : List StructFieldDesc} {paths : List (List ProjectionElem)}
    {alloc : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    (hvalid : ValidStructLayout (translateTy ty layouts).layout fields)
    (hplen : paths.length = fields.length)
    (hmut : alloc.mutability = .Mut)
    (hbs : alloc.byteSize = (translateTy ty layouts).layout.size)
    (hlen : alloc.len = alloc.byteSize.bytes.toNat)
    (hprov : alloc.provenanceMap = Miri.Memory.ProvenanceMap.new)
    (hmask : InitMaskWordRel alloc.initializationMask alloc.byteSize
      (initWordsFalse alloc.byteSize)) :
    PartialStructState layouts ty fields paths 0 [] alloc
      (initWordsFalse alloc.byteSize) := by
  refine ⟨hvalid, hplen, Nat.zero_le _, True.intro, rfl, hmut, hbs, hlen, hprov, hmask,
    fun _ hi => absurd hi (Nat.not_lt_zero _),
    fun _ hi => absurd hi (Nat.not_lt_zero _), ?_⟩
  intro p hp
  have hmask' : InitMaskWordRel alloc.initializationMask (translateTy ty layouts).layout.size
      (initWordsFalse (translateTy ty layouts).layout.size) := by
    rwa [← hbs]
  exact (initMaskWordRel_get hmask' hp.1).trans
    (congrArg Except.ok (maskBlocksGetBit_initWordsFalse _ p))

theorem of_structMemPlaceRel {mach : AnnealMachine} {ty : Ty} {layouts : LayoutTable}
    {fields : List StructFieldDesc} {paths : List (List ProjectionElem)}
    {rootVal : Value} {mp : Miri.Interpreter.MemPlace AnnealProv}
    (h : StructMemPlaceRel mach ty layouts fields paths rootVal mp) :
    ∃ (allocId : Miri.Memory.AllocId) (tag : Miri.Memory.BorTag) (baseAddr : UInt64) (localAlloc : AnnealLocalAlloc) (words : Array UInt64),
      mp.ptr.provenance = some (.concrete allocId tag) ∧
      mp.misaligned = none ∧
      mp.metadata = .none ∧
      LiveAllocEntry mach.memory.live allocId localAlloc ∧
      mach.lookupBaseAddr allocId = some baseAddr ∧
      mp.ptr.offset = Miri.ABI.Size.ofBytes baseAddr ∧
      baseAddr.toNat + (translateTy ty layouts).layout.size.bytes.toNat < 2 ^ 64 ∧
      mp.ptr.offset.isAligned (translateTy ty layouts).layout.align.abi = .ok true ∧
      PartialStructState layouts ty fields paths 0 [] localAlloc.allocation words := by
  rcases h with ⟨allocId, _, baseAddr, localAlloc, words, hvalid, hplen, _, _, hprov, hmis, hmeta, hlive, hbase, hptr, hovf, hmut, halign, hbs, hlen, hpmap,
    hmask, _, _, hpad⟩
  refine ⟨allocId, _, baseAddr, localAlloc, words,
    hprov, hmis, hmeta, hlive, hbase, hptr, hovf, halign, ?_⟩
  exact ⟨hvalid, hplen, Nat.zero_le _, True.intro, rfl, hmut, hbs, hlen, hpmap, hmask,
    fun _ hi => absurd hi (Nat.not_lt_zero _),
    fun _ hi => absurd hi (Nat.not_lt_zero _), hpad⟩

theorem step_one_leaf {layouts : LayoutTable} {ty : Ty}
    {fields : List StructFieldDesc} {paths : List (List ProjectionElem)}
    {k : Nat} {doneVals : List Value}
    {alloc : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    {words : Array UInt64}
    (h : PartialStructState layouts ty fields paths k doneVals alloc words)
    (hk : k < fields.length)
    {v_f : Value} {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    (hv_nz : NoZeroByteLeaves v_f)
    (hv_bytes : valueLeafBytes v_f = (fields[k]'hk).fieldLayout.size.bytes.toNat)
    (hp_ne : (paths[k]'(by rw [h.paths_len]; exact hk)) ≠ [])
    (hfl_eq : (fields[k]'hk).fieldLayout = (translateTy (fields[k]'hk).ty layouts).layout)
    (hprim : IsPrimScalarTy (fields[k]'hk).ty)
    (hvpath : ∀ sfx, ValidAggregateFieldPath layouts (.aggregate 0 ((doneVals ++ [v_f]) ++ sfx))
      (paths[k]'(by rw [h.paths_len]; exact hk)))
    (hrpv : ∀ sfx, readProjectedValue [] (.aggregate 0 ((doneVals ++ [v_f]) ++ sfx))
      (paths[k]'(by rw [h.paths_len]; exact hk)) = .ok (.scalar sc))
    (hrel : ScalarRel sc msc)
    (hsz : (fields[k]'hk).fieldLayout.size = translateSizeBytes sc.sizeBytes)
    (hbool : (fields[k]'hk).ty.kind = .bool → sc.sizeBytes = 1 ∧ (sc.bits = 0 ∨ sc.bits = 1))
    (hchar : (fields[k]'hk).ty.kind = .char → sc.sizeBytes = 4 ∧ isValidCharCode sc.bits = true) :
    ∃ alloc' words',
      Miri.Memory.Allocation.writeScalar annealTargetDataLayout
        (Miri.Memory.allocRange (fields[k]'hk).offset msc.size)
        (.fromScalarInt msc) alloc = .ok () alloc' ∧
      PartialStructState layouts ty fields paths (k + 1) (doneVals ++ [v_f]) alloc' words' := by
  obtain ⟨alloc', words', hw, hbs', hlen', hmut', hpmap', hmask', hbits',
      hinit_k, hread_k, hother', hpad'⟩ :=
    writeField_preserves_other_fields_and_padding h.valid_layout hk hrel hsz
      h.byteSize_eq h.alloc_len_eq h.mut_alloc h.prov_empty h.mask_rel
  refine ⟨alloc', words', hw, h.valid_layout, h.paths_len, Nat.succ_le_of_lt hk,
    h.vals_nz.append_singleton hv_nz, ?_, hmut', hbs', hlen', hpmap', hmask', ?_, ?_, ?_⟩
  · rw [valueLeafBytesList_append_singleton, h.vals_bytes, structSumFieldBytes_take_succ hk, hv_bytes]
  · intro i hi b hlo hhi
    have hb_lt : b < (translateTy ty layouts).layout.size.bytes.toNat := by
      have := h.valid_layout.fields_in_bounds i (Nat.lt_of_lt_of_le hi (Nat.succ_le_of_lt hk))
      omega
    rw [hbits' b hb_lt]
    by_cases hik : i = k
    · subst hik
      have hin : (fields[i]'hk).offset.bytes.toNat ≤ b ∧
          b < (fields[i]'hk).offset.bytes.toNat + (fields[i]'hk).fieldLayout.size.bytes.toNat :=
        ⟨hlo, hhi⟩
      simp [hin]
    · have hi_lt : i < k := by omega
      rw [h.word_bits_init i hi_lt b hlo hhi]
      simp
  · intro i hi
    by_cases hik : i = k
    · subst hik
      exact ⟨hp_ne, hfl_eq, hprim, hvpath, sc, msc, hrpv, hrel, hsz, hbool, hchar, hinit_k, hread_k⟩
    · have hi_lt : i < k := by omega
      have hi_f : i < fields.length := Nat.lt_of_lt_of_le hi_lt h.hk_le
      obtain ⟨hp_i, hfl_i, hprim_i, hvpath_i, sc_i, msc_i, hrpv_i, hrel_i, hsz_i,
          hbool_i, hchar_i, _, hread_i⟩ := h.fields_rel i hi_lt
      dsimp at hp_i hfl_i hprim_i hvpath_i hrpv_i hsz_i hbool_i hchar_i hread_i ⊢
      have hpos_i : 0 < (fields[i]'hi_f).fieldLayout.size.bytes.toNat := by
        rw [hsz_i]; exact translateSizeBytes_pos_of_valid hrel_i.validBytes
      obtain ⟨hinit_i', hread_i_eq⟩ := hother' i hi_f hik hpos_i (h.word_bits_init i hi_lt)
      exact ⟨hp_i, hfl_i, hprim_i,
        fun sfx => by rw [List.append_assoc]; exact hvpath_i (v_f :: sfx),
        sc_i, msc_i,
        fun sfx => by rw [List.append_assoc]; exact hrpv_i (v_f :: sfx),
        hrel_i, hsz_i, hbool_i, hchar_i, hinit_i', hread_i_eq.trans hread_i⟩
  · intro p hp
    exact (hpad' p hp).trans (h.padding_uninit p hp)

theorem toStructMemPlaceRel {mach : AnnealMachine} {layouts : LayoutTable} {ty : Ty}
    {fields : List StructFieldDesc} {paths : List (List ProjectionElem)}
    {hd : Value} {tl : List Value}
    {allocId : Miri.Memory.AllocId} {baseAddr : UInt64}
    {localAlloc : AnnealLocalAlloc} {words : Array UInt64}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    (h : PartialStructState layouts ty fields paths fields.length (hd :: tl)
      localAlloc.allocation words)
    {tag : Miri.Memory.BorTag} (hprov : mp.ptr.provenance = some (.concrete allocId tag))
    (hmis : mp.misaligned = none)
    (hmeta : mp.metadata = .none)
    (hlive : LiveAllocEntry mach.memory.live allocId localAlloc)
    (hbase : mach.lookupBaseAddr allocId = some baseAddr)
    (hptr : mp.ptr.offset = Miri.ABI.Size.ofBytes baseAddr)
    (hovf : baseAddr.toNat + (translateTy ty layouts).layout.size.bytes.toNat < 2 ^ 64)
    (halign : mp.ptr.offset.isAligned (translateTy ty layouts).layout.align.abi = .ok true) :
    StructMemPlaceRel mach ty layouts fields paths (.aggregate 0 (hd :: tl)) mp := by
  have hleaf_bytes : valueLeafBytes (.aggregate 0 (hd :: tl)) = structSumFieldBytes fields := by
    dsimp [valueLeafBytes]
    rw [h.vals_bytes, List.take_length]
  refine .mk allocId _ baseAddr localAlloc words h.valid_layout h.paths_len
    ⟨⟨hd, tl, rfl⟩, h.vals_nz⟩ hleaf_bytes hprov hmis hmeta hlive hbase hptr hovf
    h.mut_alloc halign h.byteSize_eq h.alloc_len_eq h.prov_empty h.mask_rel
    h.word_bits_init ?_ h.padding_uninit
  intro i hi
  obtain ⟨hp_i, hfl_i, hprim_i, hvpath_i, sc_i, msc_i, hrpv_i, hrel_i, hsz_i,
      hbool_i, hchar_i, hinit_i, hread_i⟩ := h.fields_rel i hi
  have happ_nil : (hd :: tl) ++ [] = hd :: tl := List.append_nil _
  have hvpath' := hvpath_i []
  have hrpv' := hrpv_i []
  rw [happ_nil] at hvpath' hrpv'
  exact ⟨hp_i, hfl_i, hprim_i, hvpath', sc_i, msc_i, hrpv', hrel_i, hsz_i,
    hbool_i, hchar_i, hinit_i, hread_i⟩

theorem step_two_leaves {layouts : LayoutTable} {ty : Ty}
    {fields : List StructFieldDesc} {paths : List (List ProjectionElem)}
    {k : Nat} {doneVals : List Value}
    {alloc : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    {words : Array UInt64}
    (h : PartialStructState layouts ty fields paths k doneVals alloc words)
    (hk1 : k + 1 < fields.length)
    {v_sub : Value} {sc₀ sc₁ : MirAst.ScalarInt} {msc₀ msc₁ : Miri.Memory.ScalarInt}
    (hv_nz : NoZeroByteLeaves v_sub)
    (hv_bytes :
      valueLeafBytes v_sub =
        (fields[k]'(Nat.lt_of_succ_lt hk1)).fieldLayout.size.bytes.toNat +
          (fields[k + 1]'hk1).fieldLayout.size.bytes.toNat)
    (hp0_ne : (paths[k]'(by rw [h.paths_len]; exact Nat.lt_of_succ_lt hk1)) ≠ [])
    (hp1_ne : (paths[k + 1]'(by rw [h.paths_len]; exact hk1)) ≠ [])
    (hfl0_eq : (fields[k]'(Nat.lt_of_succ_lt hk1)).fieldLayout =
      (translateTy (fields[k]'(Nat.lt_of_succ_lt hk1)).ty layouts).layout)
    (hfl1_eq : (fields[k + 1]'hk1).fieldLayout =
      (translateTy (fields[k + 1]'hk1).ty layouts).layout)
    (hprim0 : IsPrimScalarTy (fields[k]'(Nat.lt_of_succ_lt hk1)).ty)
    (hprim1 : IsPrimScalarTy (fields[k + 1]'hk1).ty)
    (hvpath0 : ∀ sfx, ValidAggregateFieldPath layouts (.aggregate 0 ((doneVals ++ [v_sub]) ++ sfx))
      (paths[k]'(by rw [h.paths_len]; exact Nat.lt_of_succ_lt hk1)))
    (hvpath1 : ∀ sfx, ValidAggregateFieldPath layouts (.aggregate 0 ((doneVals ++ [v_sub]) ++ sfx))
      (paths[k + 1]'(by rw [h.paths_len]; exact hk1)))
    (hrpv0 : ∀ sfx, readProjectedValue [] (.aggregate 0 ((doneVals ++ [v_sub]) ++ sfx))
      (paths[k]'(by rw [h.paths_len]; exact Nat.lt_of_succ_lt hk1)) = .ok (.scalar sc₀))
    (hrpv1 : ∀ sfx, readProjectedValue [] (.aggregate 0 ((doneVals ++ [v_sub]) ++ sfx))
      (paths[k + 1]'(by rw [h.paths_len]; exact hk1)) = .ok (.scalar sc₁))
    (hrel0 : ScalarRel sc₀ msc₀)
    (hrel1 : ScalarRel sc₁ msc₁)
    (hsz0 : (fields[k]'(Nat.lt_of_succ_lt hk1)).fieldLayout.size = translateSizeBytes sc₀.sizeBytes)
    (hsz1 : (fields[k + 1]'hk1).fieldLayout.size = translateSizeBytes sc₁.sizeBytes)
    (hbool0 : (fields[k]'(Nat.lt_of_succ_lt hk1)).ty.kind = .bool →
      sc₀.sizeBytes = 1 ∧ (sc₀.bits = 0 ∨ sc₀.bits = 1))
    (hchar0 : (fields[k]'(Nat.lt_of_succ_lt hk1)).ty.kind = .char →
      sc₀.sizeBytes = 4 ∧ isValidCharCode sc₀.bits = true)
    (hbool1 : (fields[k + 1]'hk1).ty.kind = .bool →
      sc₁.sizeBytes = 1 ∧ (sc₁.bits = 0 ∨ sc₁.bits = 1))
    (hchar1 : (fields[k + 1]'hk1).ty.kind = .char →
      sc₁.sizeBytes = 4 ∧ isValidCharCode sc₁.bits = true) :
    ∃ alloc₁ alloc₂ words₂,
      Miri.Memory.Allocation.writeScalar annealTargetDataLayout
        (Miri.Memory.allocRange (fields[k]'(Nat.lt_of_succ_lt hk1)).offset msc₀.size)
        (.fromScalarInt msc₀) alloc = .ok () alloc₁ ∧
      Miri.Memory.Allocation.writeScalar annealTargetDataLayout
        (Miri.Memory.allocRange (fields[k + 1]'hk1).offset msc₁.size)
        (.fromScalarInt msc₁) alloc₁ = .ok () alloc₂ ∧
      PartialStructState layouts ty fields paths (k + 2) (doneVals ++ [v_sub]) alloc₂ words₂ := by
  have hk0 : k < fields.length := Nat.lt_of_succ_lt hk1
  obtain ⟨alloc₁, alloc₂, words₂, hw₀, hw₁, hbs₂, hlen₂, hmut₂, hpmap₂, hmask₂,
      hbits₂, hinit₀, hread₀, hinit₁, hread₁, hother₂, hpad₂⟩ :=
    writeScalarPairField_preserves_other_fields_and_padding h.valid_layout
      hk0 hk1 (by omega) hrel0 hrel1 hsz0 hsz1
      h.byteSize_eq h.alloc_len_eq h.mut_alloc h.prov_empty h.mask_rel
  refine ⟨alloc₁, alloc₂, words₂, hw₀, hw₁, h.valid_layout, h.paths_len,
    Nat.succ_le_of_lt hk1, h.vals_nz.append_singleton hv_nz, ?_,
    hmut₂, hbs₂, hlen₂, hpmap₂, hmask₂, ?_, ?_, ?_⟩
  · rw [valueLeafBytesList_append_singleton, h.vals_bytes,
      show k + 2 = (k + 1) + 1 from rfl,
      structSumFieldBytes_take_succ hk1, structSumFieldBytes_take_succ hk0, hv_bytes]
    omega
  · intro i hi b hlo hhi
    have hb_lt : b < (translateTy ty layouts).layout.size.bytes.toNat := by
      have := h.valid_layout.fields_in_bounds i (Nat.lt_of_lt_of_le hi (Nat.succ_le_of_lt hk1))
      omega
    rw [hbits₂ b hb_lt]
    by_cases hik0 : i = k
    · subst hik0
      have hin : (fields[i]'hk0).offset.bytes.toNat ≤ b ∧
          b < (fields[i]'hk0).offset.bytes.toNat + (fields[i]'hk0).fieldLayout.size.bytes.toNat :=
        ⟨hlo, hhi⟩
      simp [hin]
    · by_cases hik1 : i = k + 1
      · subst hik1
        have hin : (fields[k + 1]'hk1).offset.bytes.toNat ≤ b ∧
            b < (fields[k + 1]'hk1).offset.bytes.toNat +
              (fields[k + 1]'hk1).fieldLayout.size.bytes.toNat :=
          ⟨hlo, hhi⟩
        simp [hin]
      · have hi_lt : i < k := by omega
        rw [h.word_bits_init i hi_lt b hlo hhi]
        simp
  · intro i hi
    by_cases hik0 : i = k
    · subst hik0
      exact ⟨hp0_ne, hfl0_eq, hprim0, hvpath0, sc₀, msc₀, hrpv0, hrel0, hsz0,
        hbool0, hchar0, hinit₀, hread₀⟩
    · by_cases hik1 : i = k + 1
      · subst hik1
        exact ⟨hp1_ne, hfl1_eq, hprim1, hvpath1, sc₁, msc₁, hrpv1, hrel1, hsz1,
          hbool1, hchar1, hinit₁, hread₁⟩
      · have hi_lt : i < k := by omega
        have hi_f : i < fields.length := Nat.lt_of_lt_of_le hi_lt h.hk_le
        obtain ⟨hp_i, hfl_i, hprim_i, hvpath_i, sc_i, msc_i, hrpv_i, hrel_i, hsz_i,
            hbool_i, hchar_i, _, hread_i⟩ := h.fields_rel i hi_lt
        dsimp at hp_i hfl_i hprim_i hvpath_i hrpv_i hsz_i hbool_i hchar_i hread_i ⊢
        have hpos_i : 0 < (fields[i]'hi_f).fieldLayout.size.bytes.toNat := by
          rw [hsz_i]; exact translateSizeBytes_pos_of_valid hrel_i.validBytes
        obtain ⟨hinit_i', hread_i_eq⟩ := hother₂ i hi_f hik0 hik1 hpos_i (h.word_bits_init i hi_lt)
        exact ⟨hp_i, hfl_i, hprim_i,
          fun sfx => by rw [List.append_assoc]; exact hvpath_i (v_sub :: sfx),
          sc_i, msc_i,
          fun sfx => by rw [List.append_assoc]; exact hrpv_i (v_sub :: sfx),
          hrel_i, hsz_i, hbool_i, hchar_i, hinit_i', hread_i_eq.trans hread_i⟩
  · intro p hp
    exact (hpad₂ p hp).trans (h.padding_uninit p hp)

end PartialStructState

/-- 100% syntactic specification for constructor field `fieldIdx` at leaf cursor
`k` of an aggregate `dstLay` with flattened leaf descriptors `fields` and leaf
paths `paths`:
* `primLeaf`: primitive scalar leaf (`k → k + 1`);
* `scalarWrapSub`: 1-field `.Scalar` wrapper sub-struct (`IsImmediateStructTy`,
  enforcing `ValidStructLayout` at the inner struct level, `k → k + 1`);
* `scalarPairSub`: 2-scalar `.ScalarPair` tuple/sub-struct (`IsImmediateStructTy`,
  enforcing `ValidStructLayout` at the inner struct level, `k → k + 2`). -/
inductive WellTypedLM2_2AggFieldSpec
    (body : CapturedMir) (env : StructTypeEnv) (stEnv : LM2_2StaticEnv)
    (dstLay : Miri.Interpreter.LocalLayout)
    (fields : List StructFieldDesc) (paths : List (List ProjectionElem))
    (fieldIdx k : Nat) (op : MirAst.Operand) : Nat → Prop where
  | primLeaf (hk : k < fields.length) (fl : Miri.Interpreter.LocalLayout) :
      WellTypedLM2_2Operand body env stEnv op (fields[k]'hk).ty →
      env (fields[k]'hk).ty = none →
      IsPrimScalarTy (fields[k]'hk).ty →
      (fields[k]'hk).fieldLayout = (translateTy (fields[k]'hk).ty body.layouts).layout →
      paths[k]? = some [.field fieldIdx (fields[k]'hk).ty] →
      dstLay.layout.fields.offset fieldIdx = .ok (fields[k]'hk).offset →
      annealFieldLayout body.layouts none dstLay fieldIdx = .ok fl →
      fl.layout.isSized = true →
      fl.layout.size = (fields[k]'hk).fieldLayout.size →
      WellTypedLM2_2AggFieldSpec body env stEnv dstLay fields paths fieldIdx k op (k + 1)
  | scalarWrapSub (hk : k < fields.length) (subTy : Ty)
      (f_sub : StructFieldDesc) (p_sub : List ProjectionElem)
      (fl : Miri.Interpreter.LocalLayout) :
      WellTypedLM2_2Operand body env stEnv op subTy →
      IsImmediateStructTy env body.layouts subTy [f_sub] [p_sub] →
      f_sub.ty = (fields[k]'hk).ty →
      (fields[k]'hk).fieldLayout = (translateTy (fields[k]'hk).ty body.layouts).layout →
      paths[k]? = some (.field fieldIdx subTy :: p_sub) →
      dstLay.layout.fields.offset fieldIdx = .ok (fields[k]'hk).offset →
      annealFieldLayout body.layouts none dstLay fieldIdx = .ok fl →
      fl.layout.isSized = true →
      fl.layout.size = (fields[k]'hk).fieldLayout.size →
      WellTypedLM2_2AggFieldSpec body env stEnv dstLay fields paths fieldIdx k op (k + 1)
  | scalarPairSub (hk1 : k + 1 < fields.length) (subTy : Ty)
      (f_sub0 f_sub1 : StructFieldDesc) (mid0 mid1 : Ty)
      (z0 z1 : List ProjectionElem) (fl : Miri.Interpreter.LocalLayout)
      (a b : Miri.ABI.Scalar) (bOff : Miri.ABI.Size) :
      WellTypedLM2_2Operand body env stEnv op subTy →
      IsImmediateStructTy env body.layouts subTy [f_sub0, f_sub1]
        [.field 0 mid0 :: z0, .field 1 mid1 :: z1] →
      f_sub0.ty = (fields[k]'(Nat.lt_of_succ_lt hk1)).ty →
      f_sub1.ty = (fields[k + 1]'hk1).ty →
      (fields[k]'(Nat.lt_of_succ_lt hk1)).fieldLayout =
        (translateTy (fields[k]'(Nat.lt_of_succ_lt hk1)).ty body.layouts).layout →
      (fields[k + 1]'hk1).fieldLayout =
        (translateTy (fields[k + 1]'hk1).ty body.layouts).layout →
      paths[k]? = some (.field fieldIdx subTy :: .field 0 mid0 :: z0) →
      paths[k + 1]? = some (.field fieldIdx subTy :: .field 1 mid1 :: z1) →
      dstLay.layout.fields.offset fieldIdx =
        .ok (fields[k]'(Nat.lt_of_succ_lt hk1)).offset →
      (fields[k + 1]'hk1).offset =
        Miri.ABI.Size.ofBytes ((fields[k]'(Nat.lt_of_succ_lt hk1)).offset.bytes + bOff.bytes) →
      annealFieldLayout body.layouts none dstLay fieldIdx = .ok fl →
      fl.layout.isSized = true →
      fl.layout.backendRepr = .ScalarPair (a := a) (b := b) (bOffset := bOff) →
      (fields[k]'(Nat.lt_of_succ_lt hk1)).offset.bytes.toNat + fl.layout.size.bytes.toNat ≤
        dstLay.layout.size.bytes.toNat →
      WellTypedLM2_2AggFieldSpec body env stEnv dstLay fields paths fieldIdx k op (k + 2)

/-- Inductive left-to-right typing of remaining constructor operands `ops` from
field index `fieldIdx` and leaf cursor `k`, threading `operandPostStaticEnv`
across moves and finishing at `k_end = fields.length`. -/
inductive WellTypedLM2_2AggFields
    (body : CapturedMir) (env : StructTypeEnv)
    (dstIdx : Local) (dstLay : Miri.Interpreter.LocalLayout)
    (fields : List StructFieldDesc) (paths : List (List ProjectionElem)) :
    LM2_2StaticEnv → Nat → Nat → List MirAst.Operand → Prop where
  | nil (stEnv : LM2_2StaticEnv) (fieldIdx : Nat) :
      WellTypedLM2_2AggFields body env dstIdx dstLay fields paths
        stEnv fieldIdx fields.length []
  | cons (stEnv : LM2_2StaticEnv) (fieldIdx k k' : Nat)
      (op : MirAst.Operand) (rest : List MirAst.Operand) :
      OperandDoesNotAccessLocal dstIdx op →
      WellTypedLM2_2AggFieldSpec body env stEnv dstLay fields paths fieldIdx k op k' →
      WellTypedLM2_2AggFields body env dstIdx dstLay fields paths
        (operandPostStaticEnv stEnv op) (fieldIdx + 1) k' rest →
      WellTypedLM2_2AggFields body env dstIdx dstLay fields paths
        stEnv fieldIdx k (op :: rest)

/-- Static environment update after `dstIdx = Rvalue.Aggregate(kind, ops)`:
`ops` update `stEnv` via `opsPostStaticEnv`, `dstIdx` becomes initialized, and
`dstIdx` is materialized in stack memory (removed from `immLocals`). -/
def aggPostStaticEnv (stEnv : LM2_2StaticEnv) (dstIdx : Local)
    (ops : List MirAst.Operand) : LM2_2StaticEnv :=
  let s1 := opsPostStaticEnv stEnv ops
  { initLocals := dstIdx :: s1.initLocals
    immLocals := s1.immLocals.filter (· != dstIdx) }

/-- 100% state-independent typing predicate for non-empty tuple and single-variant
struct aggregate construction `_dst = Rvalue.Aggregate(kind, op₀ :: rest)`. -/
inductive WellTypedLM2_2Aggregate
    (body : CapturedMir) (env : StructTypeEnv) (stEnv : LM2_2StaticEnv)
    (dstIdx : Local) (kind : MirAst.AggregateKind)
    (ops : List MirAst.Operand) : Prop where
  | mk
      (decl : LocalDecl)
      (fields : List StructFieldDesc)
      (paths : List (List ProjectionElem))
      (op₀ : MirAst.Operand)
      (rest : List MirAst.Operand)
      (ops_eq : ops = op₀ :: rest)
      (kind_ok : IsTupleOrSingleAdtKind kind)
      (decl_lookup : get? body.localDecls dstIdx = some decl)
      (env_lookup : env decl.ty = some (fields, paths))
      (valid_layout : ValidStructLayout (translateTy decl.ty body.layouts).layout fields)
      (dst_size_lt_4gib : (translateTy decl.ty body.layouts).layout.size.bytes.toNat < 2 ^ 32)
      (paths_len : paths.length = fields.length)
      (dst_sized : (translateTy decl.ty body.layouts).layout.isSized = true)
      (dst_align : (translateTy decl.ty body.layouts).layout.align.abi.pow2 ≤ 29)
      (fields_ok :
        WellTypedLM2_2AggFields body env dstIdx (translateTy decl.ty body.layouts)
          fields paths stEnv 0 0 (op₀ :: rest)) :
      WellTypedLM2_2Aggregate body env stEnv dstIdx kind ops


/-! ## 6. Aggregate Construction Simulation (`evalRvalue_aggregate_tuple_struct_simulation`) -/

theorem WellTypedLM2_2AggFieldSpec.toSyntacticFieldOperand
    {body : CapturedMir} {env : StructTypeEnv} {stEnv : LM2_2StaticEnv}
    {dstLay : Miri.Interpreter.LocalLayout}
    {fields : List StructFieldDesc} {paths : List (List ProjectionElem)}
    {fieldIdx k k' : Nat} {op : MirAst.Operand} {numLocals : Nat}
    (hlen : numLocals = body.localDecls.length)
    (h : WellTypedLM2_2AggFieldSpec body env stEnv dstLay fields paths fieldIdx k op k') :
    SyntacticFieldOperand numLocals op := by
  cases h with
  | primLeaf _ _ hop _ _ _ _ _ _ _ _ => exact hop.toSyntacticFieldOperand hlen
  | scalarWrapSub _ _ _ _ _ hop _ _ _ _ _ _ _ _ => exact hop.toSyntacticFieldOperand hlen
  | scalarPairSub _ _ _ _ _ _ _ _ _ _ _ _ hop _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact hop.toSyntacticFieldOperand hlen

theorem WellTypedLM2_2AggFields.evalOperands_not_unsupported_and_preserves_dst
    {body : CapturedMir} {env : StructTypeEnv}
    {dstIdx : Local} {dstLay : Miri.Interpreter.LocalLayout}
    {fields : List StructFieldDesc} {paths : List (List ProjectionElem)}
    {stEnv : LM2_2StaticEnv} {fieldIdx k : Nat} {ops : List MirAst.Operand}
    (h : WellTypedLM2_2AggFields body env dstIdx dstLay fields paths stEnv fieldIdx k ops)
    {locals : List LocalSlot} (hlen : locals.length = body.localDecls.length)
    (globals : List CapturedAllocation) :
    evalOperands locals ops .nil globals body.layouts .nil ≠ .unsupported ∧
    ∀ vs locals_end,
      evalOperands locals ops .nil globals body.layouts .nil = .ok vs locals_end →
      get? locals_end dstIdx = get? locals dstIdx := by
  induction h generalizing locals with
  | nil _ _ =>
    refine ⟨nofun, fun _ locals_end hok => ?_⟩
    injection hok with _ hloc; subst hloc; rfl
  | cons _ _ _ _ op rest hno_acc hspec _ ih =>
    obtain ⟨hne_op, hok_op⟩ :=
      (hspec.toSyntacticFieldOperand hlen).evalOperand_shape globals body.layouts
    dsimp only [evalOperands]
    cases hev : evalOperand locals op .nil globals body.layouts .nil with
    | unsupported => exact absurd hev hne_op
    | ub => exact ⟨nofun, fun _ _ hok => nomatch hok⟩
    | ok v locals₁ =>
      dsimp only
      obtain ⟨hlen₁, hpres₁⟩ := hok_op v locals₁ hev
      obtain ⟨hne_rest, hok_rest⟩ := ih (hlen₁.trans hlen)
      refine ⟨by
        cases hev_r : evalOperands locals₁ rest .nil globals body.layouts .nil with
        | unsupported => exact absurd hev_r hne_rest
        | ub | ok _ _ => nofun, fun vs locals_end hok => ?_⟩
      cases hev_rest : evalOperands locals₁ rest .nil globals body.layouts .nil with
      | unsupported => exact absurd hev_rest hne_rest
      | ub => rw [hev_rest] at hok; cases hok
      | ok vs' locals₂ =>
        rw [hev_rest] at hok
        injection hok with _ hloc; subst hloc
        exact (hok_rest vs' locals₂ hev_rest).trans (hpres₁ dstIdx hno_acc.not_move)

theorem aggHooks_projectField_local_ok
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    {dstLay fl : Miri.Interpreter.LocalLayout}
    {dstIdx : Miri.MIR.LocalId} {id0 : Miri.Interpreter.LocalsIdentity}
    {fieldIdx : Nat} {off : Miri.ABI.Size}
    (hfl : annealFieldLayout layouts none dstLay fieldIdx = .ok fl)
    (hoff : dstLay.layout.fields.offset fieldIdx = .ok off)
    (hsized : fl.layout.isSized = true)
    (hbnd : off.bytes.toNat + fl.layout.size.bytes.toNat ≤ dstLay.layout.size.bytes.toNat)
    (hnot_array : ∀ s c, dstLay.layout.fields ≠ Miri.ABI.FieldsShape.Array s c)
    (m : AnnealStepState) :
    (annealAggregateHooks localDecls layouts).projectField ()
        ⟨.local 0 dstIdx none id0, dstLay⟩ fieldIdx m =
      .ok ⟨.local 0 dstIdx (some off) id0, fl⟩ m := by
  have hlt_u64 := dstLay.layout.size.bytes.toNat_lt
  have hproj := annealProjectFieldPlace_local_of_fieldLayout
    (frameIdx := 0) (localId := dstIdx) (baseOffOpt := none) (id0 := id0)
    hfl hoff hsized hbnd
    (by dsimp [Miri.ABI.Size.ZERO]; omega)
  have hz : Miri.ABI.Size.ofBytes ((none.getD Miri.ABI.Size.ZERO).bytes + off.bytes) = off := by
    dsimp [Option.getD, Miri.ABI.Size.ZERO]
    rw [UInt64.zero_add]
    cases off; rfl
  rw [hz] at hproj
  dsimp [annealAggregateHooks]
  rw [hproj]
  cases heq : dstLay.layout.fields <;> simp_all [Pure.pure, EStateM.pure]

private theorem annealWriteImmediate_projected_eq
    {val : Miri.Interpreter.Immediate AnnealProv}
    {m : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {frameIdx : Nat} {localId : Miri.MIR.LocalId} {relOff : Miri.ABI.Size}
    {iden : Miri.Interpreter.LocalsIdentity}
    {fieldLay : Miri.Interpreter.LocalLayout}
    (hframes : m.stack.frames = #[tf]) :
    annealWriteImmediate val ⟨.local frameIdx localId (some relOff) iden, fieldLay⟩ m =
      annealWriteProjectedLocalImmediate val
        ⟨.local frameIdx localId (some relOff) iden, fieldLay⟩ .nil emptyLayoutTable m := by
  unfold annealWriteImmediate
  dsimp only [bind, Bind.bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get]
  rw [stack_currentFrame?_singleton m.stack tf hframes]

private theorem get?_append_singleton_append :
    ∀ (doneVals : List Value) {sfx : List Value} {v : Value} {fieldIdx : Nat},
      doneVals.length = fieldIdx →
      get? ((doneVals ++ [v]) ++ sfx) fieldIdx = some v
  | [], _, _, _, hlen => by subst hlen; rfl
  | _ :: xs, _, _, 0, hlen => by cases hlen
  | _ :: xs, sfx, v, n + 1, hlen =>
      get?_append_singleton_append xs (Nat.succ.inj hlen)

theorem WellTypedLM2_2AggFieldSpec.step_spec
    {body : CapturedMir} {env : StructTypeEnv} {stEnv : LM2_2StaticEnv}
    {dstTy : Ty} {fields : List StructFieldDesc} {paths : List (List ProjectionElem)}
    {fieldIdx k k' : Nat} {op : MirAst.Operand}
    (hvalid : ValidStructLayout (translateTy dstTy body.layouts).layout fields)
    (hplen : paths.length = fields.length)
    (hspec : WellTypedLM2_2AggFieldSpec body env stEnv
      (translateTy dstTy body.layouts) fields paths fieldIdx k op k') :
    ∃ (opTy : Ty) (fl : Miri.Interpreter.LocalLayout) (relOff : Miri.ABI.Size),
      WellTypedLM2_2Operand body env stEnv op opTy ∧
      fl.layout.isSized = true ∧
      relOff.bytes.toNat ≤ (translateTy dstTy body.layouts).layout.size.bytes.toNat ∧
      (∀ dstIdx id0 m,
        (annealAggregateHooks body.localDecls body.layouts).projectField ()
          ⟨.local 0 dstIdx none id0, translateTy dstTy body.layouts⟩ fieldIdx m =
          .ok ⟨.local 0 dstIdx (some relOff) id0, fl⟩ m) ∧
      (∀ {doneVals : List Value} (_ : doneVals.length = fieldIdx)
          {v_f : Value} {imm : Miri.Interpreter.Immediate AnnealProv}
          (_ : LM2_2OperandValRel env body.layouts opTy v_f imm)
          {alloc_in : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
          {words_in : Array UInt64}
          (_ : PartialStructState body.layouts dstTy fields paths k doneVals alloc_in words_in),
        ∃ alloc_out words_out,
          PartialStructState body.layouts dstTy fields paths k'
            (doneVals ++ [v_f]) alloc_out words_out ∧
          (∀ {m : AnnealStepState}
              {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
              {dstIdx : Miri.MIR.LocalId} {id0 : Miri.Interpreter.LocalsIdentity}
              {oldImm : Miri.Interpreter.Immediate AnnealProv}
              {rawAlloc : Miri.Memory.Allocation AnnealProv Unit}
              {mem' : AnnealMemory} {id : Miri.Memory.AllocId},
            (translateTy dstTy body.layouts).layout.isSized = true →
            m.stack.frames = #[tf] →
            (hlt : dstIdx < tf.locals.size) →
            tf.locals[dstIdx]'hlt =
              ⟨.live (.immediate oldImm), some (translateTy dstTy body.layouts)⟩ →
            Miri.Memory.Allocation.tryNew (translateTy dstTy body.layouts).layout.size
              (translateTy dstTy body.layouts).layout.align.abi .Uninit
              annealZeroedStorage = .ok rawAlloc →
            m.machine.memory.reserveAllocId = (mem', .ok id) →
            mem'.live.any (fun entry => entry.1 == id) = false →
            ((oldImm = .uninit ∧ alloc_in = rawAlloc.withExtra none) ∨
              (oldImm ≠ .uninit ∧
                annealWriteIndirectImmediate oldImm (stackAllocPlace id)
                  Miri.ABI.Size.ZERO (translateTy dstTy body.layouts)
                  { m with machine := stackAllocMachine m.machine mem' id (rawAlloc.withExtra none) } =
                .ok () { m with machine := stackAllocMachine m.machine mem' id alloc_in })) →
            (annealStackBaseAddr id).toNat + relOff.bytes.toNat < 2 ^ 64 →
            annealWriteImmediate imm ⟨.local 0 dstIdx (some relOff) id0, fl⟩ m =
              .ok () ⟨⟨#[{ tf with
                locals := tf.locals.set dstIdx
                  ⟨.live (.indirect (stackAllocPlace id)),
                    some (translateTy dstTy body.layouts)⟩ hlt }]⟩,
                stackAllocMachine m.machine mem' id alloc_out⟩) ∧
          (∀ {m : AnnealStepState}
              {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
              {dstIdx : Miri.MIR.LocalId} {id0 : Miri.Interpreter.LocalsIdentity}
              {mp : Miri.Interpreter.MemPlace AnnealProv}
              {c : Option Miri.Interpreter.LocalLayout}
              {allocId : Miri.Memory.AllocId} {tag : Miri.Memory.BorTag} {baseAddr : UInt64}
              {localAlloc : AnnealLocalAlloc} {u : Nat},
            m.stack.frames = #[tf] →
            (hlt : dstIdx < tf.locals.size) →
            tf.locals[dstIdx]'hlt = ⟨.live (.indirect mp), c⟩ →
            mp.ptr.provenance = some (.concrete allocId tag) →
            m.machine.lookupBaseAddr allocId = some baseAddr →
            mp.ptr.offset = Miri.ABI.Size.ofBytes baseAddr →
            baseAddr.toNat + relOff.bytes.toNat < 2 ^ 64 →
            (hu_lt : u < m.machine.memory.live.size) →
            m.machine.memory.live.findIdx? (fun (id, _) => id == allocId) = some u →
            m.machine.memory.live[u]'hu_lt = (allocId, localAlloc) →
            localAlloc.allocation = alloc_in →
            annealWriteImmediate imm ⟨.local 0 dstIdx (some relOff) id0, fl⟩ m =
              .ok () { m with
                machine := updateAllocMachine m.machine u allocId localAlloc.kind alloc_out })) := by
  cases hspec with
  | primLeaf hk fl hop henv_f hprim hfl_eq hpath hdst_off hproj_fl hfl_sized hfl_sz =>
    have hbnd := hvalid.fields_in_bounds k hk
    have hk_p : k < paths.length := by rw [hplen]; exact hk
    have hp_eq : paths[k]'hk_p = [.field fieldIdx (fields[k]'hk).ty] :=
      Option.some.inj ((List.getElem?_eq_getElem hk_p).symm.trans hpath)
    refine ⟨(fields[k]'hk).ty, fl, (fields[k]'hk).offset, hop, hfl_sized,
      by omega,
      fun dstIdx id0 m => aggHooks_projectField_local_ok hproj_fl hdst_off hfl_sized
        (by rw [hfl_sz]; exact hbnd) (by intro s c heq; rcases hvalid.fields_shape_valid with ⟨_, hprim, _⟩ | ⟨_, _, harb, _⟩ <;> simp_all) m, ?_⟩
    intro doneVals hdone v_f imm hvRel alloc_in words_in hpart
    cases hvRel with
    | immStruct _ _ _ _ hsub _ =>
      have := hsub.env_eq; rw [henv_f] at this; cases this
    | primScalar sc msc _ _ himm =>
      obtain ⟨_, _, hsc_eq, hmsc_eq, hrel, hsz_tr, hbool, hchar⟩ :=
        himm.of_primitive_scalar hprim
      injection hsc_eq with hsc_eq'; subst hsc_eq'
      injection hmsc_eq with hmsc_eq'
      injection hmsc_eq' with hmsc_eq''
      injection hmsc_eq'' with hmsc_eq'''
      subst hmsc_eq'''
      have hsz : (fields[k]'hk).fieldLayout.size = translateSizeBytes sc.sizeBytes := by
        rw [hfl_eq, hsz_tr]
      have hsc_pos : 0 < sc.sizeBytes := by
        rcases hrel.validBytes with h1 | h1 | h1 | h1 | h1 <;> omega
      have hbytes : valueLeafBytes (.scalar sc) =
          (fields[k]'hk).fieldLayout.size.bytes.toNat := by
        dsimp [valueLeafBytes]
        rw [hsz]
        rcases hrel.validBytes with h1 | h1 | h1 | h1 | h1 <;> (rw [h1]; rfl)
      obtain ⟨alloc_out, words_out, hw, hpart'⟩ :=
        hpart.step_one_leaf hk (v_f := .scalar sc) hsc_pos hbytes
          (by rw [hp_eq]; nofun) hfl_eq hprim
          (fun sfx => by
            rw [hp_eq]
            exact .single _ fieldIdx _ (.scalar sc) (get?_append_singleton_append doneVals hdone))
          (fun sfx => by
            rw [hp_eq]
            dsimp [readProjectedValue]
            rw [get?_append_singleton_append doneVals hdone])
          hrel hsz hbool hchar
      refine ⟨alloc_out, words_out, hpart', ?_, ?_⟩
      · intro m tf dstIdx id0 oldImm rawAlloc mem' id hsw hfr hlt himm_l htry hres hfresh hw_old hovf
        rw [annealWriteImmediate_projected_eq hfr]
        rcases hw_old with ⟨rfl, rfl⟩ | ⟨hne_u, hw_old'⟩
        · exact annealWriteProjectedLocalImmediate_immediate_scalar_ok
            (alloc_init := rawAlloc.withExtra none)
            hfl_sized hsw hfr hlt himm_l htry hres hfresh rfl hovf hw
        · cases oldImm with
          | uninit => exact absurd rfl hne_u
          | scalar _ | scalarPair _ _ =>
            exact annealWriteProjectedLocalImmediate_immediate_scalar_ok (alloc_init := alloc_in)
              hfl_sized hsw hfr hlt himm_l htry hres hfresh hw_old' hovf hw
      · intro m tf dstIdx id0 mp c allocId tag baseAddr localAlloc u hfr hlt hind hprov hbase hptr hovf hu hf hg ha
        rw [annealWriteImmediate_projected_eq hfr]
        exact annealWriteProjectedLocalImmediate_indirect_scalar_ok
          hfl_sized hfr hlt hind hprov hbase hptr hovf hu hf hg (by rw [ha]; exact hw)
  | scalarWrapSub hk subTy f_sub p_sub fl hop hsub hsub_ty hfl_eq hpath hdst_off hproj_fl hfl_sized hfl_sz =>
    have hbnd := hvalid.fields_in_bounds k hk
    have hk_p : k < paths.length := by rw [hplen]; exact hk
    have hp_eq : paths[k]'hk_p = .field fieldIdx subTy :: p_sub :=
      Option.some.inj ((List.getElem?_eq_getElem hk_p).symm.trans hpath)
    refine ⟨subTy, fl, (fields[k]'hk).offset, hop, hfl_sized,
      by omega,
      fun dstIdx id0 m => aggHooks_projectField_local_ok hproj_fl hdst_off hfl_sized
        (by rw [hfl_sz]; exact hbnd) (by intro s c heq; rcases hvalid.fields_shape_valid with ⟨_, hprim, _⟩ | ⟨_, _, harb, _⟩ <;> simp_all) m, ?_⟩
    intro doneVals hdone v_f imm hvRel alloc_in words_in hpart
    cases hvRel with
    | primScalar _ _ henv_n _ _ =>
      have := hsub.env_eq; rw [henv_n] at this; cases this
    | immStruct fs ps _ _ hsub' himm =>
      have heq_env := hsub.env_eq.symm.trans hsub'.env_eq
      injection heq_env with hpair
      injection hpair with hfs hps; subst hfs hps
      cases himm with
      | scalarWrapper _ _ a sc msc _ _ _ hp_sub_ne _ _ hf_sub_fl hprim_sub hwrap hrel hsz_sub hbool_sub hchar_sub =>
        have hprim_k : IsPrimScalarTy (fields[k]'hk).ty := hsub_ty ▸ hprim_sub
        have hsz_k : (fields[k]'hk).fieldLayout.size = translateSizeBytes sc.sizeBytes := by
          rw [hfl_eq, ← hsub_ty, ← hf_sub_fl, hsz_sub]
        have hsc_pos : 0 < sc.sizeBytes := by
          rcases hrel.validBytes with h1 | h1 | h1 | h1 | h1 <;> omega
        have hbytes : valueLeafBytes v_f = (fields[k]'hk).fieldLayout.size.bytes.toNat := by
          rw [hwrap.valueLeafBytes_eq, hsz_k]
          rcases hrel.validBytes with h1 | h1 | h1 | h1 | h1 <;> (rw [h1]; rfl)
        obtain ⟨alloc_out, words_out, hw, hpart'⟩ :=
          hpart.step_one_leaf hk (hwrap.noZeroByteLeaves hsc_pos) hbytes
            (by rw [hp_eq]; nofun) hfl_eq hprim_k
            (fun sfx => by
              rw [hp_eq]
              exact .cons _ fieldIdx subTy p_sub v_f
                (get?_append_singleton_append doneVals hdone)
                hwrap.agg_length_le_two
                (hwrap.toValidAggregateFieldPath hp_sub_ne))
            (fun sfx => by
              rw [hp_eq]
              dsimp [readProjectedValue]
              rw [get?_append_singleton_append doneVals hdone]
              exact hwrap.readProjectedValue_eq [])
            hrel hsz_k (hsub_ty ▸ hbool_sub) (hsub_ty ▸ hchar_sub)
        refine ⟨alloc_out, words_out, hpart', ?_, ?_⟩
        · intro m tf dstIdx id0 oldImm rawAlloc mem' id hsw hfr hlt himm_l htry hres hfresh hw_old hovf
          rw [annealWriteImmediate_projected_eq hfr]
          rcases hw_old with ⟨rfl, rfl⟩ | ⟨hne_u, hw_old'⟩
          · exact annealWriteProjectedLocalImmediate_immediate_scalar_ok
              (alloc_init := rawAlloc.withExtra none)
              hfl_sized hsw hfr hlt himm_l htry hres hfresh rfl hovf hw
          · cases oldImm with
            | uninit => exact absurd rfl hne_u
            | scalar _ | scalarPair _ _ =>
              exact annealWriteProjectedLocalImmediate_immediate_scalar_ok (alloc_init := alloc_in)
                hfl_sized hsw hfr hlt himm_l htry hres hfresh hw_old' hovf hw
        · intro m tf dstIdx id0 mp c allocId tag baseAddr localAlloc u hfr hlt hind hprov hbase hptr hovf hu hf hg ha
          rw [annealWriteImmediate_projected_eq hfr]
          exact annealWriteProjectedLocalImmediate_indirect_scalar_ok
            hfl_sized hfr hlt hind hprov hbase hptr hovf hu hf hg (by rw [ha]; exact hw)
  | scalarPairSub hk1 subTy f0 f1 mid0 mid1 z0 z1 fl a b bOff
      hop hsub hty0 hty1 hfl0 hfl1 hp0 hp1 hdst_off hoff1 hproj_fl hfl_sized hfl_repr hfl_sz_le =>
    have hk0 : k < fields.length := Nat.lt_of_succ_lt hk1
    have hk0_p : k < paths.length := by rw [hplen]; exact hk0
    have hk1_p : k + 1 < paths.length := by rw [hplen]; exact hk1
    have hp0_eq : paths[k]'hk0_p = .field fieldIdx subTy :: .field 0 mid0 :: z0 :=
      Option.some.inj ((List.getElem?_eq_getElem hk0_p).symm.trans hp0)
    have hp1_eq : paths[k + 1]'hk1_p = .field fieldIdx subTy :: .field 1 mid1 :: z1 :=
      Option.some.inj ((List.getElem?_eq_getElem hk1_p).symm.trans hp1)
    refine ⟨subTy, fl, (fields[k]'hk0).offset, hop, hfl_sized,
      by omega,
      fun dstIdx id0 m => aggHooks_projectField_local_ok hproj_fl hdst_off hfl_sized
        hfl_sz_le (by intro s c heq; rcases hvalid.fields_shape_valid with ⟨_, hprim, _⟩ | ⟨_, _, harb, _⟩ <;> simp_all) m, ?_⟩
    intro doneVals hdone v_f imm hvRel alloc_in words_in hpart
    cases hvRel with
    | primScalar _ _ henv_n _ _ =>
      have := hsub.env_eq; rw [henv_n] at this; cases this
    | immStruct fs ps _ _ hsub' himm =>
      have heq_env := hsub.env_eq.symm.trans hsub'.env_eq
      injection heq_env with hpair
      injection hpair with hfs hps; subst hfs hps
      cases himm with
      | scalarPair _ _ _ _ _ _ _ _ _ sc₀ sc₁ msc₀ msc₁ v₀ v₁
          _ _ _ _ hrepr_sub _ _ _ _ _ _ hf0_fl hf1_fl _ _ hprim0 hprim1 _ _ hw0 hw1
          hrel0 hrel1 hsz0 hsz1 hbool0 hchar0 hbool1 hchar1 =>
        have hsc0_pos : 0 < sc₀.sizeBytes := by
          rcases hrel0.validBytes with h1 | h1 | h1 | h1 | h1 <;> omega
        have hsc1_pos : 0 < sc₁.sizeBytes := by
          rcases hrel1.validBytes with h1 | h1 | h1 | h1 | h1 <;> omega
        have hsz0_k : (fields[k]'hk0).fieldLayout.size = translateSizeBytes sc₀.sizeBytes := by
          rw [hfl0, ← hty0, ← hf0_fl, hsz0]
        have hsz1_k : (fields[k + 1]'hk1).fieldLayout.size = translateSizeBytes sc₁.sizeBytes := by
          rw [hfl1, ← hty1, ← hf1_fl, hsz1]
        have hbytes :
            valueLeafBytes (.aggregate 0 [v₀, v₁]) =
              (fields[k]'hk0).fieldLayout.size.bytes.toNat +
                (fields[k + 1]'hk1).fieldLayout.size.bytes.toNat := by
          dsimp [valueLeafBytes, valueLeafBytes.valueLeafBytesList]
          rw [hw0.valueLeafBytes_eq, hw1.valueLeafBytes_eq, hsz0_k, hsz1_k]
          have hb0 : (translateSizeBytes sc₀.sizeBytes).bytes.toNat = sc₀.sizeBytes := by
            rcases hrel0.validBytes with h1 | h1 | h1 | h1 | h1 <;> (rw [h1]; rfl)
          have hb1 : (translateSizeBytes sc₁.sizeBytes).bytes.toNat = sc₁.sizeBytes := by
            rcases hrel1.validBytes with h1 | h1 | h1 | h1 | h1 <;> (rw [h1]; rfl)
          omega
        have hvp0_sub : ValidAggregateFieldPath body.layouts (.aggregate 0 [v₀, v₁]) (.field 0 mid0 :: z0) := by
          cases z0 with
          | nil => exact .single [v₀, v₁] 0 mid0 v₀ rfl
          | cons q qs =>
            exact .cons [v₀, v₁] 0 mid0 (q :: qs) v₀ rfl hw0.agg_length_le_two
              (hw0.toValidAggregateFieldPath (by nofun))
        have hvp1_sub : ValidAggregateFieldPath body.layouts (.aggregate 0 [v₀, v₁]) (.field 1 mid1 :: z1) := by
          cases z1 with
          | nil => exact .single [v₀, v₁] 1 mid1 v₁ rfl
          | cons q qs =>
            exact .cons [v₀, v₁] 1 mid1 (q :: qs) v₁ rfl hw1.agg_length_le_two
              (hw1.toValidAggregateFieldPath (by nofun))
        have hpair_len : ∀ sf : List Value, Value.aggregate 0 [v₀, v₁] = .aggregate 0 sf →
            (∀ a b bOff, (translateTy subTy body.layouts).layout.backendRepr =
              .ScalarPair (a := a) (b := b) (bOffset := bOff) → sf.length ≤ 2) ∧
            (∀ a, (translateTy subTy body.layouts).layout.backendRepr = .Scalar a → sf.length = 1) := by
          intro sf hsf
          injection hsf with _ hsf'
          subst hsf'
          exact ⟨fun _ _ _ _ => by simp, fun a h => by rw [hrepr_sub] at h; cases h⟩
        obtain ⟨alloc₁, alloc_out, words_out, hw_a0, hw_a1, hpart'⟩ :=
          hpart.step_two_leaves hk1 (v_sub := .aggregate 0 [v₀, v₁])
            ⟨hw0.noZeroByteLeaves hsc0_pos, hw1.noZeroByteLeaves hsc1_pos, True.intro⟩
            hbytes
            (by rw [hp0_eq]; nofun) (by rw [hp1_eq]; nofun)
            hfl0 hfl1 (hty0 ▸ hprim0) (hty1 ▸ hprim1)
            (fun sfx => by
              rw [hp0_eq]
              exact .cons _ fieldIdx subTy _ (.aggregate 0 [v₀, v₁])
                (get?_append_singleton_append doneVals hdone) hpair_len hvp0_sub)
            (fun sfx => by
              rw [hp1_eq]
              exact .cons _ fieldIdx subTy _ (.aggregate 0 [v₀, v₁])
                (get?_append_singleton_append doneVals hdone) hpair_len hvp1_sub)
            (fun sfx => by
              rw [hp0_eq]
              dsimp [readProjectedValue]
              rw [get?_append_singleton_append doneVals hdone]
              dsimp [readProjectedValue, get?]
              exact hw0.readProjectedValue_eq [])
            (fun sfx => by
              rw [hp1_eq]
              dsimp [readProjectedValue]
              rw [get?_append_singleton_append doneVals hdone]
              dsimp [readProjectedValue, get?]
              exact hw1.readProjectedValue_eq [])
            hrel0 hrel1 hsz0_k hsz1_k
            (hty0 ▸ hbool0) (hty0 ▸ hchar0) (hty1 ▸ hbool1) (hty1 ▸ hchar1)
        rw [hoff1] at hw_a1
        refine ⟨alloc_out, words_out, hpart', ?_, ?_⟩
        · intro m tf dstIdx id0 oldImm rawAlloc mem' id hsw hfr hlt himm_l htry hres hfresh hw_old hovf
          rw [annealWriteImmediate_projected_eq hfr]
          rcases hw_old with ⟨rfl, rfl⟩ | ⟨hne_u, hw_old'⟩
          · exact annealWriteProjectedLocalImmediate_immediate_scalarPair_ok
              (alloc_init := rawAlloc.withExtra none)
              hfl_sized hfl_repr hsw hfr hlt himm_l htry hres hfresh rfl hovf hw_a0 hw_a1
          · cases oldImm with
            | uninit => exact absurd rfl hne_u
            | scalar _ | scalarPair _ _ =>
              exact annealWriteProjectedLocalImmediate_immediate_scalarPair_ok (alloc_init := alloc_in)
                hfl_sized hfl_repr hsw hfr hlt himm_l htry hres hfresh hw_old' hovf hw_a0 hw_a1
        · intro m tf dstIdx id0 mp c allocId tag baseAddr localAlloc u hfr hlt hind hprov hbase hptr hovf hu hf hg ha
          rw [annealWriteImmediate_projected_eq hfr]
          exact annealWriteProjectedLocalImmediate_indirect_scalarPair_ok
            hfl_sized hfl_repr hfr hlt hind hprov hbase hptr hovf hu hf hg (by rw [ha]; exact hw_a0) hw_a1

theorem FrameRelLM2_2Except.of_stackAlloc_set_excl
    {body : CapturedMir} {env : StructTypeEnv} {dstIdx : Local}
    {mach : AnnealMachine} {mem' : AnnealMemory} {newId : Miri.Memory.AllocId}
    {alloc : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    {af : StackFrame}
    {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (h : FrameRelLM2_2Except body env (some dstIdx) mach af mf)
    (hres : mach.memory.reserveAllocId = (mem', .ok newId))
    {hlt : dstIdx < mf.locals.size}
    (mls' : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout) :
    FrameRelLM2_2Except body env (some dstIdx) (stackAllocMachine mach mem' newId alloc) af
      { mf with locals := mf.locals.set dstIdx mls' hlt } := by
  refine ⟨h.body_eq, h.location_eq, h.af_locals_len, by simp [h.mf_locals_size], ?_⟩
  intro i d sl ml hne hd hs hm
  have hne_i : dstIdx ≠ i := fun heq => hne (congrArg some heq)
  rw [Array.getElem?_set_ne _ hne_i] at hm
  exact (h.locals_rel i d sl ml hne hd hs hm).of_stackAlloc_other hres

theorem FrameRelLM2_2Except.of_updateAlloc_excl
    {body : CapturedMir} {env : StructTypeEnv} {dstIdx : Local}
    {mach : AnnealMachine} {u : Nat} {allocId : Miri.Memory.AllocId}
    {oldLa : AnnealLocalAlloc}
    {kind : Miri.Memory.MemoryKind Miri.Memory.MiriMemoryKind}
    {alloc' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    {c : Option Miri.Interpreter.LocalLayout}
    {af : StackFrame}
    {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (h : FrameRelLM2_2Except body env (some dstIdx) mach af mf)
    (hdisj : MemoryAllocDisjoint mf)
    {hlt : dstIdx < mf.locals.size}
    (hdst : mf.locals[dstIdx]'hlt = ⟨.live (.indirect mp), c⟩)
    {tag : Miri.Memory.BorTag} (hprov : mp.ptr.provenance = some (.concrete allocId tag))
    (hu_lt : u < mach.memory.live.size)
    (hu_eq : mach.memory.live[u]'hu_lt = (allocId, oldLa)) :
    FrameRelLM2_2Except body env (some dstIdx)
      (updateAllocMachine mach u allocId kind alloc') af mf := by
  refine ⟨h.body_eq, h.location_eq, h.af_locals_len, h.mf_locals_size, ?_⟩
  intro i d sl ml hne hd hs hm
  have hne_i : dstIdx ≠ i := fun heq => hne (congrArg some heq)
  apply (h.locals_rel i d sl ml hne hd hs hm).of_updateAlloc_ne hu_lt hu_eq
  intro mp' hv
  have hml_eq : ml = ⟨.live (.indirect mp'), ml.layout⟩ := by
    cases ml; dsimp at hv ⊢; rw [hv]
  rw [hml_eq] at hm
  have hdst_get : mf.locals[dstIdx]? = some ⟨.live (.indirect mp), c⟩ := by
    rw [Array.getElem?_eq_getElem hlt, hdst]
  have hd_ids := hdisj i dstIdx mp' mp ml.layout c (Ne.symm hne_i) hm hdst_get
  have hmp_id : mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId = some allocId := by
    rw [hprov]; rfl
  rwa [hmp_id] at hd_ids

theorem MemoryAllocDisjoint_set_fresh_stackAlloc
    {body : CapturedMir} {env : StructTypeEnv} {dstIdx : Local}
    {mach : AnnealMachine} {af : StackFrame}
    {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {id : Miri.Memory.AllocId}
    {lay : Option Miri.Interpreter.LocalLayout}
    (hfr : FrameRelLM2_2Except body env (some dstIdx) mach af mf)
    (hdisj : MemoryAllocDisjoint mf)
    (hfresh : mach.memory.live.any (fun entry => entry.1 == id) = false)
    (hlt : dstIdx < mf.locals.size) :
    MemoryAllocDisjoint
      { mf with
        locals := mf.locals.set dstIdx
          ⟨.live (.indirect (stackAllocPlace id)), lay⟩ hlt } := by
  have helper : ∀ k mp_k lk, k ≠ dstIdx →
      mf.locals[k]? = some ⟨.live (.indirect mp_k), lk⟩ →
      mp_k.ptr.provenance.bind Miri.Memory.Provenance.getAllocId ≠ some id := by
    intro k mp_k lk hne hk_get heq
    obtain ⟨hlt_k, _⟩ := Array.getElem?_eq_some_iff.mp hk_get
    have hlt_d : k < body.localDecls.length := by rw [← hfr.mf_locals_size]; exact hlt_k
    have hlt_af : k < af.locals.length := by rw [hfr.af_locals_len]; exact hlt_d
    have hdecl_k : get? body.localDecls k = some (body.localDecls[k]'hlt_d) := by
      rw [get?_eq_getElem?, List.getElem?_eq_getElem hlt_d]
    have hsl_k : get? af.locals k = some (af.locals[k]'hlt_af) := by
      rw [get?_eq_getElem?, List.getElem?_eq_getElem hlt_af]
    have hloc_k := hfr.locals_rel k _ _ _ (fun h => hne (Option.some.inj h.symm)) hdecl_k hsl_k hk_get
    obtain ⟨id_k, hid_k, hany_k⟩ := hloc_k.allocLive mp_k rfl
    rw [heq] at hid_k
    injection hid_k with hid_eq; subst hid_eq
    rw [hfresh] at hany_k; cases hany_k
  intro i j mp₁ mp₂ l₁ l₂ hne hi hj
  by_cases hi_d : i = dstIdx
  · subst hi_d
    have hj_ne : j ≠ i := Ne.symm hne
    rw [Array.getElem?_set_self hlt] at hi
    injection hi with hi'; injection hi' with hmp1 _
    injection hmp1 with hmp1'; injection hmp1' with hmp1''; subst hmp1''
    rw [Array.getElem?_set_ne _ (Ne.symm hj_ne)] at hj
    have hid1 : (stackAllocPlace id).ptr.provenance.bind Miri.Memory.Provenance.getAllocId = some id := rfl
    rw [hid1]
    exact Ne.symm (helper j mp₂ l₂ hj_ne hj)
  · by_cases hj_d : j = dstIdx
    · subst hj_d
      rw [Array.getElem?_set_self hlt] at hj
      injection hj with hj'; injection hj' with hmp2 _
      injection hmp2 with hmp2'; injection hmp2' with hmp2''; subst hmp2''
      rw [Array.getElem?_set_ne _ (Ne.symm hi_d)] at hi
      have hid2 : (stackAllocPlace id).ptr.provenance.bind Miri.Memory.Provenance.getAllocId = some id := rfl
      rw [hid2]
      exact helper i mp₁ l₁ hi_d hi
    · rw [Array.getElem?_set_ne _ (Ne.symm hi_d)] at hi
      rw [Array.getElem?_set_ne _ (Ne.symm hj_d)] at hj
      exact hdisj i j mp₁ mp₂ l₁ l₂ hne hi hj

private theorem except_bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {y : β}
    (h : (x >>= f) = .ok y) :
    ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | error _ => cases h
  | ok a => exact ⟨a, rfl, h⟩

private theorem offsetWithMeta_ok_layout_eq
    {cx : Miri.Interpreter.ProjectionCx AnnealProv}
    {base out : Miri.Interpreter.OpTy AnnealProv}
    {offset : Miri.ABI.Size} {mode : Miri.Interpreter.OffsetMode}
    {metadata : Miri.Interpreter.MemPlaceMeta AnnealProv}
    {layout : Miri.ABI.TyAndLayout Miri.MIR.TyId}
    (hok : Miri.Interpreter.OpTy.offsetWithMeta cx base offset mode metadata layout = .ok out) :
    out.layout = layout := by
  rcases base with ⟨bop, blay⟩
  unfold Miri.Interpreter.OpTy.offsetWithMeta at hok
  cases bop with
  | indirect place =>
    dsimp only at hok
    obtain ⟨_, _, hret⟩ := except_bind_ok hok
    obtain ⟨_, _, hret2⟩ := except_bind_ok hret
    injection hret2 with hret3
    rw [← hret3]
  | immediate value =>
    dsimp only at hok
    by_cases hm : metadata.hasMeta = true
    · simp [hm, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at hok
    · simp only [hm, Bool.false_eq_true, ↓reduceIte] at hok
      obtain ⟨_, _, hret⟩ := except_bind_ok hok
      obtain ⟨_, _, hret2⟩ := except_bind_ok hret
      injection hret2 with hret3
      rw [← hret3]

private theorem projectField_hint_ok_layout_eq
    {layouts : LayoutTable} {base out : Miri.Interpreter.OpTy AnnealProv}
    {idx : Nat} {fty : Ty} (hrt : IsRoundtripTy fty)
    (hok : Miri.Interpreter.project
      (annealStructProjectionCx layouts (some (encodeTyId fty)))
      base (.Field idx (encodeTyId fty)) = .ok out) :
    out.layout = translateTy fty layouts := by
  unfold Miri.Interpreter.project Miri.Interpreter.projectField at hok
  obtain ⟨off0, _, hok1⟩ := except_bind_ok hok
  obtain ⟨lay, hlay, hok2⟩ := except_bind_ok hok1
  have hlay_eq : lay = translateTy fty layouts := by
    unfold annealStructProjectionCx annealFieldLayout at hlay
    dsimp only at hlay
    rw [hrt.layoutOfEncoded] at hlay
    injection hlay with hlay'
    exact hlay'.symm
  subst hlay_eq
  by_cases hns : (!(translateTy fty layouts).layout.isSized) = true
  · simp only [hns, ↓reduceIte] at hok2
    by_cases hbs : base.layout.layout.isSized = true
    · simp [hbs, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at hok2
    · simp only [hbs, Bool.false_eq_true, ↓reduceIte] at hok2
      unfold annealStructProjectionCx at hok2
      dsimp only [bind, Except.bind, pure, Except.pure, Except.mapError] at hok2
      cases hal : off0.alignTo (translateTy fty layouts).layout.align.abi with
      | error _ => rw [hal] at hok2; cases hok2
      | ok off' =>
        rw [hal] at hok2
        exact offsetWithMeta_ok_layout_eq hok2
  · simp only [hns, Bool.false_eq_true, ↓reduceIte, bind, Except.bind, pure, Except.pure] at hok2
    exact offsetWithMeta_ok_layout_eq hok2

private theorem annealEvalProjection_ok_layout_eq
    {layouts : LayoutTable} {baseLay : Miri.Interpreter.LocalLayout}
    {projs : List ProjectionElem} {leafTy : Ty} {totalOff : Miri.ABI.Size}
    (hchain : ValidFieldProjChain layouts baseLay projs leafTy totalOff)
    {base out : Miri.Interpreter.OpTy AnnealProv}
    {m s1 : AnnealStepState}
    (hok : annealEvalProjection layouts base (projs.map translateProjectionElem) m = .ok out s1) :
    out.layout = translateTy leafTy layouts := by
  induction hchain generalizing base m with
  | single _ idx fty _ hrt _ _ _ =>
    dsimp only [List.map, translateProjectionElem, annealEvalProjection,
      Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
      throw, throwThe, MonadExceptOf.throw, EStateM.throw] at hok
    cases hp : Miri.Interpreter.project
        (annealStructProjectionCx layouts (some (encodeTyId fty)))
        base (.Field idx (encodeTyId fty)) with
    | error _ => rw [hp] at hok; cases hok
    | ok next =>
      rw [hp] at hok
      injection hok with h_out _
      rw [← h_out]
      exact projectField_hint_ok_layout_eq hrt hp
  | cons _ idx midTy rest _ _ _ _ _ _ _ _ ih =>
    change annealEvalProjection layouts base
      (translateProjectionElem (.field idx midTy) :: rest.map translateProjectionElem) m =
        .ok out s1 at hok
    dsimp only [translateProjectionElem, annealEvalProjection,
      Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
      throw, throwThe, MonadExceptOf.throw, EStateM.throw] at hok
    cases hp : Miri.Interpreter.project
        (annealStructProjectionCx layouts (some (encodeTyId midTy)))
        base (.Field idx (encodeTyId midTy)) with
    | error _ => rw [hp] at hok; cases hok
    | ok next =>
      rw [hp] at hok
      exact ih hok

private theorem annealEvalOperand_projected_indirect_layout_eq
    {body : CapturedMir} {env : StructTypeEnv} {excl : Option Local}
    {af : StackFrame}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {m s1 : AnnealStepState} {isMove : Bool} {idx : Local}
    {projs : List ProjectionElem} {decl : LocalDecl}
    {leafTy : Ty} {totalOff : Miri.ABI.Size}
    {known : Option Miri.Interpreter.LocalLayout}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    {outLay : Miri.Interpreter.LocalLayout}
    (hframes : m.stack.frames = #[topFrame])
    (hframe : FrameRelLM2_2Except body env excl m.machine af topFrame)
    (hne : excl ≠ some idx)
    (hdecl : get? body.localDecls idx = some decl)
    (hchain : ValidFieldProjChain body.layouts (translateTy decl.ty body.layouts)
      projs leafTy totalOff)
    (hok : annealEvalOperand body.localDecls body.layouts
      (translateOperand (mkPlaceOperand isMove ⟨idx, projs⟩)) known m =
      .ok ⟨.indirect mp, outLay⟩ s1) :
    outLay = translateTy leafTy body.layouts := by
  obtain ⟨_, mls, hlt_mf, _, _, _, hmls_eq, hloc⟩ := hframe.lookup_local hne hdecl
  have hcache := hloc.layout_eq
  rcases mls with ⟨val, lay⟩
  obtain ⟨idx0, fty0, ps, rfl⟩ : ∃ idx0 fty0 ps, projs = .field idx0 fty0 :: ps := by
    cases hpr : projs with
    | nil => exact False.elim (hchain.ne_nil hpr)
    | cons p0 ps =>
      obtain ⟨i, t, rfl⟩ := hchain.only_fields p0 (by rw [hpr]; exact List.mem_cons_self)
      exact ⟨i, t, ps, rfl⟩
  have htr : translateOperand (mkPlaceOperand isMove ⟨idx, .field idx0 fty0 :: ps⟩) =
      (if isMove then .Move ⟨idx, (translateProjectionElem (.field idx0 fty0) ::
        ps.map translateProjectionElem).toArray⟩
       else .Copy ⟨idx, (translateProjectionElem (.field idx0 fty0) ::
        ps.map translateProjectionElem).toArray⟩) := by
    cases isMove <;> rfl
  rw [htr] at hok
  cases val with
  | dead =>
    rw [annealEvalOperand_projected_dead hframes hlt_mf hdecl hmls_eq hcache] at hok
    cases hok
  | live opVal =>
    by_cases hsp : ps = [] ∧ ∃ s0 s1, opVal = .immediate (.scalarPair s0 s1)
    · rcases hsp with ⟨rfl, s0, s1, rfl⟩
      by_cases h01 : idx0 = 0 ∨ idx0 = 1
      · dsimp only [List.map, translateProjectionElem] at hok
        rw [annealEvalOperand_projected_scalarPair_single hframes hlt_mf hdecl
          hmls_eq hcache h01] at hok
        cases hok
      · have hne0 : (idx0 == 0) = false := beq_false_of_ne (fun h => h01 (Or.inl h))
        have hne1 : (idx0 == 1) = false := beq_false_of_ne (fun h => h01 (Or.inr h))
        have hcache' : ∀ l, (topFrame.locals[idx]'hlt_mf).layout = some l →
            l = translateTy decl.ty body.layouts := by rw [hmls_eq]; exact hcache
        have hres := annealResolveAndCacheLocalLayout_eq (known := known)
          hframes hlt_mf hdecl hcache'
        have hget_c := cacheFrameLocalLayout_getLocal topFrame hlt_mf
          (translateTy decl.ty body.layouts)
        rw [hmls_eq] at hget_c
        have hgop := frame_getLocalOperand_live _ hget_c
        have heq_proj :
            annealEvalOperand body.localDecls body.layouts
              (if isMove then .Move ⟨idx, #[.Field idx0 (encodeTyId fty0)]⟩
               else .Copy ⟨idx, #[.Field idx0 (encodeTyId fty0)]⟩) known m =
            annealEvalProjection body.layouts
              ⟨.immediate (.scalarPair s0 s1), translateTy decl.ty body.layouts⟩
              ([ProjectionElem.field idx0 fty0].map translateProjectionElem)
              { m with stack := ⟨#[cacheFrameLocalLayout topFrame idx hlt_mf
                  (translateTy decl.ty body.layouts)]⟩ } := by
          cases isMove <;>
          · with_unfolding_all
              unfold annealEvalOperand
              simp only [Bool.false_eq_true, ↓reduceIte,
                get, getThe, MonadStateOf.get, EStateM.get, Bind.bind, EStateM.bind,
                Pure.pure, EStateM.pure, stack_currentFrame?_singleton m.stack topFrame hframes,
                Option.isNone_some, hres, hgop, hne0, hne1]
              rfl
        dsimp only [List.map, translateProjectionElem] at hok heq_proj
        rw [heq_proj] at hok
        exact annealEvalProjection_ok_layout_eq hchain hok
    · have hnot_sp : ps.map translateProjectionElem ≠ [] ∨
          ∀ s0 s1, opVal ≠ .immediate (.scalarPair s0 s1) := by
        by_cases hps : ps = []
        · right; intro s0 s1 heq; exact hsp ⟨hps, s0, s1, heq⟩
        · left; cases ps with | nil => exact absurd rfl hps | cons _ _ => nofun
      dsimp only [translateProjectionElem] at hok
      rw [annealEvalOperand_projected_live hframes hlt_mf hdecl hmls_eq hcache hnot_sp ⟨idx0, encodeTyId fty0, rfl⟩] at hok
      exact annealEvalProjection_ok_layout_eq hchain hok

private theorem WellTypedLM2_2Operand.annealEvalOperand_indirect_usesStructMemCopyDest_false
    {body : CapturedMir} {env : StructTypeEnv} {stEnv : LM2_2StaticEnv}
    {excl : Option Local} {af : StackFrame}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {m s1 : AnnealStepState} {op : MirAst.Operand} {ty : Ty}
    {known : Option Miri.Interpreter.LocalLayout}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    {outLay : Miri.Interpreter.LocalLayout}
    (hop : WellTypedLM2_2Operand body env stEnv op ty)
    (ref : Miri.Interpreter.RuntimePlaceRef AnnealProv)
    (hframes : m.stack.frames = #[topFrame])
    (hframe : FrameRelLM2_2Except body env excl m.machine af topFrame)
    (hno_excl : ∀ d, excl = some d → OperandDoesNotAccessLocal d op)
    (hok : annealEvalOperand body.localDecls body.layouts
      (translateOperand op) known m = .ok ⟨.indirect mp, outLay⟩ s1) :
    usesStructMemCopyDest ⟨ref, outLay⟩ = false := by
  have hlay : outLay = translateTy ty body.layouts := by
    cases hop with
    | constScalar c _ _ _ _ _ _ _ _ _ =>
      unfold translateOperand annealEvalOperand at hok
      dsimp only [get, getThe, MonadStateOf.get, EStateM.get,
        Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
        throw, throwThe, MonadExceptOf.throw, EStateM.throw] at hok
      rw [stack_currentFrame?_singleton m.stack topFrame hframes] at hok
      dsimp only [Option.isNone_some, Bool.false_eq_true, ↓reduceIte] at hok
      cases hev : evalMirConstImmediate body.layouts (translateConstOperand c) with
      | error _ => rw [hev] at hok; cases hok
      | ok _ => rw [hev] at hok; cases hok
    | primLocal isMove idx decl hdecl _ _ _ =>
      have hne : excl ≠ some idx := fun heq => by
        have hna := hno_excl idx heq; cases isMove <;> exact hna rfl
      obtain ⟨_, mls, hlt_mf, _, _, _, hmls_eq, hloc⟩ := hframe.lookup_local hne hdecl
      have hcache := hloc.layout_eq
      rcases mls with ⟨val, lay⟩
      cases val with
      | dead =>
        cases isMove with
        | false =>
          rw [show translateOperand (mkPlaceOperand false ⟨idx, []⟩) = .Copy ⟨idx, #[]⟩ from rfl,
            annealEvalOperand_copy_dead hframes hlt_mf hdecl hmls_eq hcache] at hok
          cases hok
        | true =>
          rw [show translateOperand (mkPlaceOperand true ⟨idx, []⟩) = .Move ⟨idx, #[]⟩ from rfl,
            annealEvalOperand_move_dead hframes hlt_mf hdecl hmls_eq hcache] at hok
          cases hok
      | live opVal =>
        cases isMove with
        | false =>
          rw [show translateOperand (mkPlaceOperand false ⟨idx, []⟩) = .Copy ⟨idx, #[]⟩ from rfl,
            annealEvalOperand_copy_live hframes hlt_mf hdecl hmls_eq hcache] at hok
          injection hok with hok'; injection hok' with _ hl; exact hl.symm
        | true =>
          rw [show translateOperand (mkPlaceOperand true ⟨idx, []⟩) = .Move ⟨idx, #[]⟩ from rfl,
            annealEvalOperand_move_live hframes hlt_mf hdecl hmls_eq hcache] at hok
          injection hok with hok'; injection hok' with _ hl; exact hl.symm
    | immStructLocal isMove idx decl _ _ hdecl _ =>
      have hne : excl ≠ some idx := fun heq => by
        have hna := hno_excl idx heq; cases isMove <;> exact hna rfl
      obtain ⟨_, mls, hlt_mf, _, _, _, hmls_eq, hloc⟩ := hframe.lookup_local hne hdecl
      have hcache := hloc.layout_eq
      rcases mls with ⟨val, lay⟩
      cases val with
      | dead =>
        cases isMove with
        | false =>
          rw [show translateOperand (mkPlaceOperand false ⟨idx, []⟩) = .Copy ⟨idx, #[]⟩ from rfl,
            annealEvalOperand_copy_dead hframes hlt_mf hdecl hmls_eq hcache] at hok
          cases hok
        | true =>
          rw [show translateOperand (mkPlaceOperand true ⟨idx, []⟩) = .Move ⟨idx, #[]⟩ from rfl,
            annealEvalOperand_move_dead hframes hlt_mf hdecl hmls_eq hcache] at hok
          cases hok
      | live opVal =>
        cases isMove with
        | false =>
          rw [show translateOperand (mkPlaceOperand false ⟨idx, []⟩) = .Copy ⟨idx, #[]⟩ from rfl,
            annealEvalOperand_copy_live hframes hlt_mf hdecl hmls_eq hcache] at hok
          injection hok with hok'; injection hok' with _ hl; exact hl.symm
        | true =>
          rw [show translateOperand (mkPlaceOperand true ⟨idx, []⟩) = .Move ⟨idx, #[]⟩ from rfl,
            annealEvalOperand_move_live hframes hlt_mf hdecl hmls_eq hcache] at hok
          injection hok with hok'; injection hok' with _ hl; exact hl.symm
    | projectedScalar isMove idx projs leafTy _ hproj =>
      rcases hproj with ⟨decl, _, _, _, _, _, hdecl, _, _, _, _, hchain⟩
      have hne : excl ≠ some idx := fun heq => by
        have hna := hno_excl idx heq; cases isMove <;> exact hna rfl
      exact annealEvalOperand_projected_indirect_layout_eq hframes hframe hne hdecl hchain hok
    | projectedSubStruct isMove idx projs _ _ _ _ _ _ hproj =>
      obtain ⟨decl, _, hdecl, hchain⟩ := hproj.decl_and_chain
      have hne : excl ≠ some idx := fun heq => by
        have hna := hno_excl idx heq; cases isMove <;> exact hna rfl
      exact annealEvalOperand_projected_indirect_layout_eq hframes hframe hne hdecl hchain hok
    | projectedScalarWrap isMove idx projs _ _ _ _ hproj =>
      obtain ⟨decl, _, hdecl, hchain⟩ := hproj.decl_and_chain
      have hne : excl ≠ some idx := fun heq => by
        have hna := hno_excl idx heq; cases isMove <;> exact hna rfl
      exact annealEvalOperand_projected_indirect_layout_eq hframes hframe hne hdecl hchain hok
  rw [hlay]
  exact hop.usesStructMemCopyDest_false ref

private theorem writeAggregateFieldsAux_step_eq
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (dest : Miri.Interpreter.RuntimePlace AnnealProv)
    (fieldRef : Miri.Interpreter.RuntimePlaceRef AnnealProv)
    (fl : Miri.Interpreter.LocalLayout)
    (start : Nat) (op : Miri.MIR.Operand) (rest : List Miri.MIR.Operand)
    (m : AnnealStepState)
    (hproj : (annealAggregateHooks localDecls layouts).projectField () dest start m =
      .ok ⟨fieldRef, fl⟩ m)
    (hind_false : ∀ mp lay s1,
      annealEvalOperand localDecls layouts op (some fl) m = .ok ⟨.indirect mp, lay⟩ s1 →
      usesStructMemCopyDest ⟨fieldRef, lay⟩ = false) :
    writeAggregateFieldsAux (annealAggregateHooks localDecls layouts) dest start (op :: rest) m =
      (((annealEvalOperand localDecls layouts op (some fl) >>= annealReadImmediate) >>=
          fun imm => annealWriteImmediate imm.imm ⟨fieldRef, fl⟩) >>=
        fun _ => writeAggregateFieldsAux (annealAggregateHooks localDecls layouts) dest (start + 1) rest) m := by
  dsimp only [writeAggregateFieldsAux, Miri.Interpreter.AggregateHooks.evalOperandAt,
    bind, Bind.bind, EStateM.bind]
  rw [hproj]
  dsimp only [annealAggregateHooks, bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  cases hev : annealEvalOperand localDecls layouts op (some fl) m with
  | error _ _ => rfl
  | ok v s1 =>
    rcases v with ⟨vop, vlay⟩
    dsimp only
    cases vop with
    | immediate imm =>
      cases imm with
      | uninit =>
        dsimp only [annealReadImmediate, pure, EStateM.pure, bind, EStateM.bind,
          throw, throwThe, MonadExceptOf.throw, EStateM.throw]
      | scalar _ =>
        dsimp only [annealReadImmediate, pure, EStateM.pure, bind, EStateM.bind]
        cases usesStructMemCopyDest ⟨fieldRef, vlay⟩ && usesStructMemCopyDest ⟨fieldRef, fl⟩ <;> rfl
      | scalarPair _ _ =>
        dsimp only [annealReadImmediate, pure, EStateM.pure, bind, EStateM.bind]
        cases usesStructMemCopyDest ⟨fieldRef, vlay⟩ && usesStructMemCopyDest ⟨fieldRef, fl⟩ <;> rfl
    | indirect mp =>
      dsimp only [EStateM.pure]
      rw [hind_false mp vlay s1 hev]
      rfl

theorem agg_write_tail
    {body : CapturedMir} {env : StructTypeEnv}
    {dstIdx : Local} {decl : LocalDecl}
    {fields : List StructFieldDesc} {paths : List (List ProjectionElem)}
    {curStEnv : LM2_2StaticEnv} {fieldIdx k k_bud : Nat}
    {rest : List MirAst.Operand}
    (hdecl : get? body.localDecls dstIdx = some decl)
    (henv : env decl.ty = some (fields, paths))
    (hvalid : ValidStructLayout (translateTy decl.ty body.layouts).layout fields)
    (hplen : paths.length = fields.length)
    (htail : WellTypedLM2_2AggFields body env dstIdx (translateTy decl.ty body.layouts)
      fields paths curStEnv fieldIdx k rest)
    {af : StackFrame} {curLocals : List LocalSlot} {doneVals : List Value}
    {m : AnnealStepState}
    {tf tf_orig : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {id0 : Miri.Interpreter.LocalsIdentity}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    {allocId : Miri.Memory.AllocId} {baseAddr : UInt64}
    {localAlloc : AnnealLocalAlloc} {words : Array UInt64}
    {globals : List CapturedAllocation}
    (hdone_len : doneVals.length = fieldIdx)
    (hdone_ne : ∃ hd tl, doneVals = hd :: tl)
    (hframes : m.stack.frames = #[tf])
    (hid0 : tf.localsIdentity = id0)
    (hretc : tf.returnContinuation = tf_orig.returnContinuation)
    (hretp : tf.returnPlace = tf_orig.returnPlace)
    (hlt_mf : dstIdx < tf.locals.size)
    (hdst_ind : tf.locals[dstIdx]'hlt_mf =
      ⟨.live (.indirect mp), some (translateTy decl.ty body.layouts)⟩)
    (hfr : FrameRelLM2_2Except body env (some dstIdx) m.machine { af with locals := curLocals } tf)
    (hdisj : MemoryAllocDisjoint tf)
    (hinit : ∀ j ∈ curStEnv.initLocals, some dstIdx ≠ some j → get? curLocals j ≠ some .uninit)
    (himm_env : ∀ j ∈ curStEnv.immLocals, some dstIdx ≠ some j → ∀ mp' l,
      tf.locals[j]? ≠ some ⟨.live (.indirect mp'), l⟩)
    (hsupply : AllocIdSupplyValid k_bud m.machine.memory)
    {tag : Miri.Memory.BorTag} (hprov : mp.ptr.provenance = some (.concrete allocId tag))
    (hmis : mp.misaligned = none)
    (hmeta : mp.metadata = .none)
    (hlive : LiveAllocEntry m.machine.memory.live allocId localAlloc)
    (hbase : m.machine.lookupBaseAddr allocId = some baseAddr)
    (hptr : mp.ptr.offset = Miri.ABI.Size.ofBytes baseAddr)
    (hovf : baseAddr.toNat + (translateTy decl.ty body.layouts).layout.size.bytes.toNat < 2 ^ 64)
    (halign : mp.ptr.offset.isAligned (translateTy decl.ty body.layouts).layout.align.abi = .ok true)
    (hpart : PartialStructState body.layouts decl.ty fields paths k doneVals localAlloc.allocation words) :
    (evalOperands curLocals rest .nil globals body.layouts .nil = .ub ∧
      ∃ msg m_err,
        writeAggregateFieldsAux (annealAggregateHooks body.localDecls body.layouts)
          ⟨.local 0 dstIdx none id0, translateTy decl.ty body.layouts⟩
          fieldIdx (rest.map translateOperand) m = .error (.undefinedBehavior msg) m_err) ∨
    ∃ tailVals locals_end m_end tf_end,
      evalOperands curLocals rest .nil globals body.layouts .nil = .ok tailVals locals_end ∧
      writeAggregateFieldsAux (annealAggregateHooks body.localDecls body.layouts)
        ⟨.local 0 dstIdx none id0, translateTy decl.ty body.layouts⟩
        fieldIdx (rest.map translateOperand) m = .ok () m_end ∧
      m_end.stack.frames = #[tf_end] ∧
      tf_end.localsIdentity = id0 ∧
      tf_end.returnContinuation = tf_orig.returnContinuation ∧
      tf_end.returnPlace = tf_orig.returnPlace ∧
      get? locals_end dstIdx = get? curLocals dstIdx ∧
      FrameRelLM2_2 body env m_end.machine
        { af with locals := locals_end.set dstIdx (.init (.aggregate 0 (doneVals ++ tailVals))) }
        tf_end ∧
      MemoryAllocDisjoint tf_end ∧
      AllocIdSupplyValid k_bud m_end.machine.memory ∧
      (∀ j ∈ (aggPostStaticEnv curStEnv dstIdx rest).initLocals,
        get? (locals_end.set dstIdx (.init (.aggregate 0 (doneVals ++ tailVals)))) j ≠ some .uninit) ∧
      (∀ j ∈ (aggPostStaticEnv curStEnv dstIdx rest).immLocals, ∀ mp' l,
        tf_end.locals[j]? ≠ some ⟨.live (.indirect mp'), l⟩) := by
  induction htail generalizing m tf curLocals doneVals localAlloc words with
  | nil stEnv_end fIdx =>
    right
    obtain ⟨hd, tl, rfl⟩ := hdone_ne
    have happ_nil : (hd :: tl) ++ [] = hd :: tl := List.append_nil _
    have hsmpr : StructMemPlaceRel m.machine decl.ty body.layouts fields paths
        (.aggregate 0 (hd :: tl)) mp :=
      hpart.toStructMemPlaceRel hprov hmis hmeta hlive hbase hptr hovf halign
    have hfr_set : FrameRelLM2_2Except body env none m.machine
        { af with locals := curLocals.set dstIdx (.init (.aggregate 0 (hd :: tl))) } tf := by
      refine ⟨hfr.body_eq, hfr.location_eq, by simp [hfr.af_locals_len], hfr.mf_locals_size, ?_⟩
      intro i d sl ml _ hd_i hs_i hm_i
      by_cases hi : i = dstIdx
      · subst hi
        rw [hdecl] at hd_i; injection hd_i with hd_eq; subst hd_eq
        have hlt_af : i < curLocals.length := by
          rw [hfr.af_locals_len, ← hfr.mf_locals_size]; exact hlt_mf
        dsimp [get?] at hs_i
        rw [List.getElem?_set_self hlt_af] at hs_i; injection hs_i with hsl; subst hsl
        rw [Array.getElem?_eq_getElem hlt_mf, hdst_ind] at hm_i
        injection hm_i with hml; subst hml
        exact .structInd fields paths _ mp _ henv
          (fun _ hl => (Option.some.inj (Option.mem_def.mp hl)).symm) hsmpr
      · dsimp [get?] at hs_i
        rw [List.getElem?_set_ne (Ne.symm hi)] at hs_i
        exact hfr.locals_rel i d sl ml (fun h => hi (Option.some.inj h.symm)) hd_i hs_i hm_i
    refine ⟨[], curLocals, m, tf, rfl, rfl, hframes, hid0, hretc, hretp, rfl, ?_, hdisj, hsupply, ?_, ?_⟩
    · rw [happ_nil]; exact hfr_set.toFrameRel
    · intro j hj
      rw [happ_nil]
      dsimp [aggPostStaticEnv, opsPostStaticEnv] at hj
      have hlt_af : dstIdx < curLocals.length := by
        rw [hfr.af_locals_len, ← hfr.mf_locals_size]; exact hlt_mf
      rcases List.mem_cons.mp hj with rfl | hj_old
      · dsimp [get?]
        rw [List.getElem?_set_self hlt_af]; nofun
      · by_cases hjd : j = dstIdx
        · subst hjd; dsimp [get?]; rw [List.getElem?_set_self hlt_af]; nofun
        · dsimp [get?]
          rw [List.getElem?_set_ne (Ne.symm hjd), ← get?_eq_getElem?]
          exact hinit j hj_old (fun h => hjd (Option.some.inj h.symm))
    · intro j hj mp' l
      dsimp [aggPostStaticEnv, opsPostStaticEnv] at hj
      rw [List.mem_filter, bne_iff_ne] at hj
      exact himm_env j hj.1 (fun h => hj.2 (Option.some.inj h.symm)) mp' l
  | cons stEnv_cur fIdx k_cur k_next op rest' hno_acc hspec _ ih =>
    obtain ⟨opTy, fl, relOff, hop, _, hrel_le, hproj_ok, hwrite_spec⟩ :=
      hspec.step_spec hvalid hplen
    have hstep_eq := writeAggregateFieldsAux_step_eq body.localDecls body.layouts
      ⟨.local 0 dstIdx none id0, translateTy decl.ty body.layouts⟩
      (.local 0 dstIdx (some relOff) id0) fl
      fIdx (translateOperand op) (rest'.map translateOperand) m (hproj_ok dstIdx id0 m)
      (fun mp lay s1 hev =>
        hop.annealEvalOperand_indirect_usesStructMemCopyDest_false
          (.local 0 dstIdx (some relOff) id0) hframes hfr
          (fun d hd => by injection hd with hd'; subst hd'; exact hno_acc) hev)
    have hsim := evalLM2_2Operand_except hframes hfr hinit himm_env
      (fun d hd => by injection hd with hd'; subst hd'; exact hno_acc)
      hop globals (some fl)
    generalize hev_op :
      evalOperand { af with locals := curLocals }.locals op .nil globals body.layouts .nil = r_a at hsim
    generalize hm_op :
      (annealEvalOperand body.localDecls body.layouts (translateOperand op) (some fl) >>=
        annealReadImmediate) m = r_m at hsim
    cases hsim with
    | ub m' msg =>
      dsimp only at hev_op
      left
      refine ⟨by dsimp [evalOperands]; rw [hev_op], msg, m', ?_⟩
      dsimp only [List.map]
      rw [hstep_eq]
      exact EStateM.bind_eq_error (EStateM.bind_eq_error hm_op)
    | ok v_f locals₁ tf₁ imm _ hfr₁ hvRel _ _ hid₁ hrc₁ hrp₁ hsz₁ hpres_acc hpres_mv hinit₁ himm₁ hdisj₁ =>
      dsimp only at hev_op hpres_mv
      have hlt₁ : dstIdx < tf₁.locals.size := by rw [hsz₁]; exact hlt_mf
      have hdst₁ : tf₁.locals[dstIdx]'hlt₁ =
          ⟨.live (.indirect mp), some (translateTy decl.ty body.layouts)⟩ := by
        have hget₁ := hpres_acc dstIdx hno_acc
        rw [Array.getElem?_eq_getElem hlt₁, Array.getElem?_eq_getElem hlt_mf, hdst_ind] at hget₁
        exact Option.some.inj hget₁
      obtain ⟨alloc_out, word_out, hpart', _, hw_ind⟩ :=
        hwrite_spec hdone_len hvRel hpart
      obtain ⟨hfind_live, u, hu_lt, hfidx, hget_u⟩ := hlive
      let m_mid : AnnealStepState :=
        { stack := ⟨#[tf₁]⟩
          machine := updateAllocMachine m.machine u allocId localAlloc.kind alloc_out }
      have hw_ok : annealWriteImmediate imm ⟨.local 0 dstIdx (some relOff) id0, fl⟩
          { m with stack := ⟨#[tf₁]⟩ } = .ok () m_mid :=
        hw_ind (m := { m with stack := ⟨#[tf₁]⟩ }) rfl hlt₁ hdst₁ hprov hbase hptr
          (by omega) hu_lt hfidx hget_u rfl
      have hdisj_tf₁ := hdisj₁ hdisj
      have hfr_mid : FrameRelLM2_2Except body env (some dstIdx) m_mid.machine
          { af with locals := locals₁ } tf₁ :=
        hfr₁.of_updateAlloc_excl hdisj_tf₁ hdst₁ hprov hu_lt hget_u
      have hlive_mid : LiveAllocEntry m_mid.machine.memory.live allocId
          ⟨localAlloc.kind, alloc_out⟩ :=
        LiveAllocEntry.of_set!_self ⟨hfind_live, u, hu_lt, hfidx, hget_u⟩ hu_lt hfidx _
      have hsupply_mid : AllocIdSupplyValid k_bud m_mid.machine.memory :=
        hsupply.of_updateAlloc hu_lt hget_u
      have hd_ne' : ∃ hd tl, doneVals ++ [v_f] = hd :: tl := by
        obtain ⟨hd, tl, rfl⟩ := hdone_ne
        exact ⟨hd, tl ++ [v_f], rfl⟩
      have hdone_len' : (doneVals ++ [v_f]).length = fIdx + 1 := by
        rw [List.length_append, List.length_singleton, hdone_len]
      have hd_pres₁ : get? locals₁ dstIdx = get? curLocals dstIdx :=
        (hpres_mv dstIdx hno_acc.not_move).1
      rcases ih hdone_len' hd_ne' (m := m_mid) rfl (hid₁.trans hid0)
          (hrc₁.trans hretc) (hrp₁.trans hretp) hlt₁ hdst₁ hfr_mid hdisj_tf₁
          hinit₁ himm₁ hsupply_mid hlive_mid hbase hpart' with
        ⟨hub_rest, msg, m_err, hm_err⟩ |
        ⟨tailVals, locals_end, m_end, tf_end, hok_rest, hm_ok_rest, hf_end, hid_end, hrc_end,
          hrp_end, hpres_end, hfr_end, hdisj_end, hsup_end, hinit_end, himm_end⟩
      · left
        refine ⟨by dsimp only [evalOperands]; rw [hev_op]; dsimp only; rw [hub_rest],
          msg, m_err, ?_⟩
        dsimp only [List.map]
        rw [hstep_eq, EStateM.bind_eq_ok (by rw [EStateM.bind_eq_ok hm_op]; exact hw_ok)]
        exact hm_err
      · right
        have happ_assoc : (doneVals ++ [v_f]) ++ tailVals = doneVals ++ (v_f :: tailVals) := by
          rw [List.append_assoc]; rfl
        rw [happ_assoc] at hfr_end hinit_end
        refine ⟨v_f :: tailVals, locals_end, m_end, tf_end,
          by dsimp only [evalOperands]; rw [hev_op]; dsimp only; rw [hok_rest],
          by
            dsimp only [List.map]
            rw [hstep_eq, EStateM.bind_eq_ok (by rw [EStateM.bind_eq_ok hm_op]; exact hw_ok)]
            exact hm_ok_rest,
          hf_end, hid_end, hrc_end, hrp_end, hpres_end.trans hd_pres₁, hfr_end, hdisj_end, hsup_end,
          hinit_end, himm_end⟩

private theorem evalRvalue_aggregate_eq
    {kind : MirAst.AggregateKind} (hk : IsTupleOrSingleAdtKind kind)
    (locals : List LocalSlot) (ops : List MirAst.Operand)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalRvalue locals (.aggregate kind ops) mem localDecls layouts =
      match evalOperands locals ops mem.borrows mem.globals layouts mem.callerLocals with
      | .ok vals locals' => .ok (.aggregate 0 vals) locals' mem
      | .ub => .ub
      | .unsupported => .unsupported := by
  rcases hk with rfl | ⟨_, rfl⟩ <;> rfl

private theorem finish_agg_from_mid
    {body : CapturedMir} {env : StructTypeEnv} {stEnv : LM2_2StaticEnv}
    {k_bud : Nat} {s : MachineState} {m m_mid : AnnealStepState}
    {topFrame tf_mid : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {bb : BasicBlockData} {dstIdx : Local} {decl : LocalDecl}
    {fields : List StructFieldDesc} {paths : List (List ProjectionElem)}
    {kind : MirAst.AggregateKind} {op₀ : MirAst.Operand} {rest : List MirAst.Operand}
    {span : String} {k₁ : Nat} {v₀ : Value} {locals₁ : List LocalSlot}
    {slot_dst : LocalSlot}
    {mp_mid : Miri.Interpreter.MemPlace AnnealProv}
    {allocId : Miri.Memory.AllocId} {baseAddr : UInt64}
    {la_mid : AnnealLocalAlloc} {words₁ : Array UInt64} {retLay : Miri.Interpreter.LocalLayout}
    (hframes : m.stack.frames = #[topFrame])
    (hbody : topFrame.body = translateBody body)
    (hloc : topFrame.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩)
    (hrc : topFrame.returnContinuation = .stop false)
    (hrp : topFrame.returnPlace = .frameLocal 0 0 none retLay topFrame.localsIdentity)
    (hcal : s.memory.activeCallee = none)
    (hstack : s.memory.callStack = .nil)
    (hbor : s.memory.borrows = .nil)
    (hprot : s.memory.activeProtectors = .nil)
    (hcaller : s.memory.callerLocals = .nil)
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.aggregate kind (op₀ :: rest)), span⟩)
    (hk_kind : IsTupleOrSingleAdtKind kind)
    (hdecl : get? body.localDecls dstIdx = some decl)
    (henv : env decl.ty = some (fields, paths))
    (hvalid : ValidStructLayout (translateTy decl.ty body.layouts).layout fields)
    (hplen : paths.length = fields.length)
    (htail : WellTypedLM2_2AggFields body env dstIdx (translateTy decl.ty body.layouts)
      fields paths (operandPostStaticEnv stEnv op₀) 1 k₁ rest)
    (hev_op₀ : evalOperand s.frame.locals op₀ .nil s.memory.globals body.layouts .nil =
      .ok v₀ locals₁)
    (hdst_slot : get? locals₁ dstIdx = some slot_dst)
    (hnot_dead : slot_dst ≠ .dead)
    (heval_mid :
      Miri.Interpreter.Step.evalStatement (annealStepHooks body.localDecls body.layouts) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.aggregate kind (op₀ :: rest)), span⟩) m =
      Miri.Interpreter.runRvalue
        (writeAggregateFieldsAux (annealAggregateHooks body.localDecls body.layouts)
          ⟨.local 0 dstIdx none topFrame.localsIdentity, translateTy decl.ty body.layouts⟩
          1 (rest.map translateOperand)) m_mid)
    (hframes_mid : m_mid.stack.frames = #[tf_mid])
    (hid_mid : tf_mid.localsIdentity = topFrame.localsIdentity)
    (hrc_mid : tf_mid.returnContinuation = topFrame.returnContinuation)
    (hrp_mid : tf_mid.returnPlace = topFrame.returnPlace)
    (hlt_mid : dstIdx < tf_mid.locals.size)
    (hdst_mid : tf_mid.locals[dstIdx]'hlt_mid =
      ⟨.live (.indirect mp_mid), some (translateTy decl.ty body.layouts)⟩)
    (hfr_mid : FrameRelLM2_2Except body env (some dstIdx) m_mid.machine
      { s.frame with locals := locals₁ } tf_mid)
    (hdisj_mid : MemoryAllocDisjoint tf_mid)
    (hinit_mid : ∀ j ∈ (operandPostStaticEnv stEnv op₀).initLocals,
      some dstIdx ≠ some j → get? locals₁ j ≠ some .uninit)
    (himm_mid : ∀ j ∈ (operandPostStaticEnv stEnv op₀).immLocals,
      some dstIdx ≠ some j → ∀ mp' l,
        tf_mid.locals[j]? ≠ some ⟨.live (.indirect mp'), l⟩)
    (hsup_mid : AllocIdSupplyValid k_bud m_mid.machine.memory)
    {tag : Miri.Memory.BorTag} (hprov : mp_mid.ptr.provenance = some (.concrete allocId tag))
    (hmis : mp_mid.misaligned = none)
    (hmeta : mp_mid.metadata = .none)
    (hlive_mid : LiveAllocEntry m_mid.machine.memory.live allocId la_mid)
    (hbase_mid : m_mid.machine.lookupBaseAddr allocId = some baseAddr)
    (hptr : mp_mid.ptr.offset = Miri.ABI.Size.ofBytes baseAddr)
    (hovf : baseAddr.toNat + (translateTy decl.ty body.layouts).layout.size.bytes.toNat < 2 ^ 64)
    (halign : mp_mid.ptr.offset.isAligned (translateTy decl.ty body.layouts).layout.align.abi = .ok true)
    (hpart₁ : PartialStructState body.layouts decl.ty fields paths k₁ [v₀] la_mid.allocation words₁) :
    StepRelLM2_2 body env (aggPostStaticEnv stEnv dstIdx (op₀ :: rest)) k_bud m
      (evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.aggregate kind (op₀ :: rest)), span⟩
        body.localDecls body.layouts)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  rcases agg_write_tail hdecl henv hvalid hplen htail (doneVals := [v₀]) rfl ⟨v₀, [], rfl⟩
      hframes_mid hid_mid hrc_mid hrp_mid hlt_mid hdst_mid hfr_mid hdisj_mid
      hinit_mid himm_mid hsup_mid hprov hmis hmeta hlive_mid hbase_mid hptr hovf halign hpart₁
      (globals := s.memory.globals) with
    ⟨hub_rest, msg, m_err, hm_err⟩ |
    ⟨tailVals, locals_end, m_end, tf_end, hok_rest, hm_ok_rest, hf_end, hid_end, hrc_end,
      hrp_end, hpres_end, hfr_end, hdisj_end, hsup_end, hinit_end, himm_end⟩
  · have ha_ub :
        evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.aggregate kind (op₀ :: rest)), span⟩
          body.localDecls body.layouts = MirStepNode.fail .ub := by
      unfold evalStmt; dsimp only
      rw [evalRvalue_aggregate_eq hk_kind, hbor, hcaller]
      dsimp only [evalOperands]; rw [hev_op₀]; dsimp only; rw [hub_rest]
    have hm_ub :
        Miri.Interpreter.Step.evalStatement (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.aggregate kind (op₀ :: rest)), span⟩) m =
        (m_err, .error (.undefinedBehavior msg)) := by
      rw [heval_mid]; unfold Miri.Interpreter.runRvalue; rw [hm_err]
    rw [ha_ub, miri_step_at_statement_error _ hframes hbody hloc hbb hstmt hm_ub]
    exact .ub _ _
  · have hdst_end : get? locals_end dstIdx = some slot_dst := hpres_end.trans hdst_slot
    have hlt_end : dstIdx < locals_end.length := by
      dsimp [get?] at hdst_end; exact (List.getElem?_eq_some_iff.mp hdst_end).1
    have ha_ok :
        evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.aggregate kind (op₀ :: rest)), span⟩
          body.localDecls body.layouts =
        MirStepNode.step (advanceStmt s
          (locals_end.set dstIdx (.init (.aggregate 0 (v₀ :: tailVals)))) s.memory) := by
      unfold evalStmt; dsimp only
      rw [evalRvalue_aggregate_eq hk_kind, hbor, hcaller]
      dsimp only [evalOperands]; rw [hev_op₀]; dsimp only; rw [hok_rest]
      dsimp only; rw [hdst_end]
      cases slot_dst with
      | dead => exact absurd rfl hnot_dead
      | uninit | init _ =>
        dsimp only
        rw [set?_eq_some_set hlt_end, hprot, hbor]
        dsimp only [invalidateConflictingBorrows]
        apply congrArg (fun mem =>
          MirStepNode.step (advanceStmt s
            (locals_end.set dstIdx (.init (.aggregate 0 (v₀ :: tailVals)))) mem))
        revert hbor hprot; generalize s.memory = mem; rintro hbor hprot
        cases mem; dsimp only at hbor hprot ⊢; subst hbor hprot; rfl
    have hm_ok :
        Miri.Interpreter.Step.evalStatement (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.aggregate kind (op₀ :: rest)), span⟩) m =
        (m_end, .ok ()) := by
      rw [heval_mid]; unfold Miri.Interpreter.runRvalue; rw [hm_ok_rest]
    rw [ha_ok,
      miri_step_at_statement_ok _ hframes hbody hloc hbb hstmt hm_ok hf_end hfr_end.location_eq]
    refine .step _ _ ?_
    exact .mk _ rfl (hrc_end.trans hrc)
      ⟨retLay, by dsimp; rw [hrp_end, hrp, hid_end]⟩
      hfr_end.step_pc hinit_end
      (fun idx hmem mp' lay' => himm_end idx hmem mp' lay')
      hsup_end hcal hstack hbor hprot hcaller hdisj_end

private theorem finish_agg_imm
    {body : CapturedMir} {env : StructTypeEnv} {stEnv : LM2_2StaticEnv}
    {k_bud : Nat} {s : MachineState} {m : AnnealStepState}
    {topFrame tf₁ : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {bb : BasicBlockData} {dstIdx : Local} {decl : LocalDecl}
    {fields : List StructFieldDesc} {paths : List (List ProjectionElem)}
    {kind : MirAst.AggregateKind} {op₀ : MirAst.Operand} {rest : List MirAst.Operand}
    {span : String} {k₁ : Nat} {v₀ : Value} {locals₁ : List LocalSlot}
    {slot_dst : LocalSlot} {retLay : Miri.Interpreter.LocalLayout}
    {mem' : AnnealMemory}
    {newId : Miri.Memory.AllocId}
    {alloc₁ : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    {words₁ : Array UInt64}
    (hframes : m.stack.frames = #[topFrame])
    (hbody : topFrame.body = translateBody body)
    (hloc : topFrame.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩)
    (hrc : topFrame.returnContinuation = .stop false)
    (hrp : topFrame.returnPlace = .frameLocal 0 0 none retLay topFrame.localsIdentity)
    (hcal : s.memory.activeCallee = none)
    (hstack : s.memory.callStack = .nil)
    (hbor : s.memory.borrows = .nil)
    (hprot : s.memory.activeProtectors = .nil)
    (hcaller : s.memory.callerLocals = .nil)
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.aggregate kind (op₀ :: rest)), span⟩)
    (hk_kind : IsTupleOrSingleAdtKind kind)
    (hdecl : get? body.localDecls dstIdx = some decl)
    (henv : env decl.ty = some (fields, paths))
    (hvalid : ValidStructLayout (translateTy decl.ty body.layouts).layout fields)
    (hplen : paths.length = fields.length)
    (hdst_align : (translateTy decl.ty body.layouts).layout.align.abi.pow2 ≤ 29)
    (htail : WellTypedLM2_2AggFields body env dstIdx (translateTy decl.ty body.layouts)
      fields paths (operandPostStaticEnv stEnv op₀) 1 k₁ rest)
    (hev_op₀ : evalOperand s.frame.locals op₀ .nil s.memory.globals body.layouts .nil =
      .ok v₀ locals₁)
    (hdst_loc₁ : get? locals₁ dstIdx = some slot_dst)
    (hnot_dead : slot_dst ≠ .dead)
    (hlt₁ : dstIdx < tf₁.locals.size)
    (hid₁ : tf₁.localsIdentity = topFrame.localsIdentity)
    (hrc₁ : tf₁.returnContinuation = topFrame.returnContinuation)
    (hrp₁ : tf₁.returnPlace = topFrame.returnPlace)
    (hfr₁ : FrameRelLM2_2Except body env (some dstIdx) m.machine
      { s.frame with locals := locals₁ } tf₁)
    (hdisj₁ : MemoryAllocDisjoint tf₁)
    (hinit₁ : ∀ j ∈ (operandPostStaticEnv stEnv op₀).initLocals,
      some dstIdx ≠ some j → get? locals₁ j ≠ some .uninit)
    (himm₁ : ∀ j ∈ (operandPostStaticEnv stEnv op₀).immLocals,
      some dstIdx ≠ some j → ∀ mp' l,
        tf₁.locals[j]? ≠ some ⟨.live (.indirect mp'), l⟩)
    (hres : m.machine.memory.reserveAllocId = (mem', .ok newId))
    (hfresh_old : m.machine.memory.live.any (fun entry => entry.1 == newId) = false)
    (hfresh : mem'.live.any (fun entry => entry.1 == newId) = false)
    (hwm_next : AllocIdWatermark k_bud
      (stackAllocMachine m.machine mem' newId alloc₁).memory)
    (hovf_sz : (annealStackBaseAddr newId).toNat +
      (translateTy decl.ty body.layouts).layout.size.bytes.toNat < 2 ^ 64)
    (hpart₁ : PartialStructState body.layouts decl.ty fields paths k₁ [v₀] alloc₁ words₁)
    (heval_mid :
      Miri.Interpreter.Step.evalStatement (annealStepHooks body.localDecls body.layouts) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.aggregate kind (op₀ :: rest)), span⟩) m =
      Miri.Interpreter.runRvalue
        (writeAggregateFieldsAux (annealAggregateHooks body.localDecls body.layouts)
          ⟨.local 0 dstIdx none topFrame.localsIdentity, translateTy decl.ty body.layouts⟩
          1 (rest.map translateOperand))
        ⟨⟨#[{ tf₁ with
          locals := tf₁.locals.set dstIdx
            ⟨.live (.indirect (stackAllocPlace newId)),
              some (translateTy decl.ty body.layouts)⟩ hlt₁ }]⟩,
          stackAllocMachine m.machine mem' newId alloc₁⟩) :
    StepRelLM2_2 body env (aggPostStaticEnv stEnv dstIdx (op₀ :: rest)) k_bud m
      (evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.aggregate kind (op₀ :: rest)), span⟩
        body.localDecls body.layouts)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  have hlt_mid : dstIdx <
      (tf₁.locals.set dstIdx
        ⟨.live (.indirect (stackAllocPlace newId)),
          some (translateTy decl.ty body.layouts)⟩ hlt₁).size := by
    rw [Array.size_set]; exact hlt₁
  have hdst_mid :
      ({ tf₁ with
        locals := tf₁.locals.set dstIdx
          ⟨.live (.indirect (stackAllocPlace newId)),
            some (translateTy decl.ty body.layouts)⟩ hlt₁ }).locals[dstIdx]'hlt_mid =
      ⟨.live (.indirect (stackAllocPlace newId)),
        some (translateTy decl.ty body.layouts)⟩ := by
    dsimp only; exact Array.getElem_set_self hlt₁
  have himm_mid : ∀ j ∈ (operandPostStaticEnv stEnv op₀).immLocals,
      some dstIdx ≠ some j → ∀ mp' l,
        ({ tf₁ with
          locals := tf₁.locals.set dstIdx
            ⟨.live (.indirect (stackAllocPlace newId)),
              some (translateTy decl.ty body.layouts)⟩ hlt₁ }).locals[j]? ≠
          some ⟨.live (.indirect mp'), l⟩ := by
    intro j hj hne mp' l
    have hne_i : dstIdx ≠ j := fun h => hne (congrArg some h)
    dsimp only
    rw [Array.getElem?_set_ne _ hne_i]
    exact himm₁ j hj hne mp' l
  exact finish_agg_from_mid hframes hbody hloc hrc hrp
    hcal hstack hbor hprot hcaller hbb hstmt hk_kind hdecl henv hvalid hplen htail
    hev_op₀ hdst_loc₁ hnot_dead heval_mid rfl hid₁ hrc₁ hrp₁ hlt_mid hdst_mid
    (hfr₁.of_stackAlloc_set_excl (alloc := alloc₁) hres _)
    (MemoryAllocDisjoint_set_fresh_stackAlloc hfr₁ hdisj₁ hfresh_old hlt₁)
    hinit₁ himm_mid (Or.inr hwm_next) rfl rfl rfl
    (LiveAllocEntry.of_push_fresh_self (la := ⟨.stack, alloc₁⟩) hfresh)
    (lookupBaseAddr_stackAllocMachine_self m.machine mem' newId alloc₁) rfl
    hovf_sz (annealStackBaseAddr_isAligned newId _ hdst_align) hpart₁
private theorem finish_agg_ind
    {body : CapturedMir} {env : StructTypeEnv} {stEnv : LM2_2StaticEnv}
    {k_bud : Nat} {s : MachineState} {m : AnnealStepState}
    {topFrame tf₁ : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {bb : BasicBlockData} {dstIdx : Local} {decl : LocalDecl}
    {fields : List StructFieldDesc} {paths : List (List ProjectionElem)}
    {kind : MirAst.AggregateKind} {op₀ : MirAst.Operand} {rest : List MirAst.Operand}
    {span : String} {k₁ : Nat} {v₀ : Value} {locals₁ : List LocalSlot}
    {slot_dst : LocalSlot} {retLay : Miri.Interpreter.LocalLayout}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    {allocId : Miri.Memory.AllocId} {baseAddr : UInt64}
    {localAlloc : AnnealLocalAlloc} {u : Nat}
    {alloc₁ : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    {words₁ : Array UInt64}
    (hframes : m.stack.frames = #[topFrame])
    (hbody : topFrame.body = translateBody body)
    (hloc : topFrame.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩)
    (hrc : topFrame.returnContinuation = .stop false)
    (hrp : topFrame.returnPlace = .frameLocal 0 0 none retLay topFrame.localsIdentity)
    (hcal : s.memory.activeCallee = none)
    (hstack : s.memory.callStack = .nil)
    (hbor : s.memory.borrows = .nil)
    (hprot : s.memory.activeProtectors = .nil)
    (hcaller : s.memory.callerLocals = .nil)
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.aggregate kind (op₀ :: rest)), span⟩)
    (hk_kind : IsTupleOrSingleAdtKind kind)
    (hdecl : get? body.localDecls dstIdx = some decl)
    (henv : env decl.ty = some (fields, paths))
    (hvalid : ValidStructLayout (translateTy decl.ty body.layouts).layout fields)
    (hplen : paths.length = fields.length)
    (htail : WellTypedLM2_2AggFields body env dstIdx (translateTy decl.ty body.layouts)
      fields paths (operandPostStaticEnv stEnv op₀) 1 k₁ rest)
    (hev_op₀ : evalOperand s.frame.locals op₀ .nil s.memory.globals body.layouts .nil =
      .ok v₀ locals₁)
    (hdst_loc₁ : get? locals₁ dstIdx = some slot_dst)
    (hnot_dead : slot_dst ≠ .dead)
    (hlt₁ : dstIdx < tf₁.locals.size)
    (hdst_tf₁ : tf₁.locals[dstIdx]'hlt₁ =
      ⟨.live (.indirect mp), some (translateTy decl.ty body.layouts)⟩)
    (hid₁ : tf₁.localsIdentity = topFrame.localsIdentity)
    (hrc₁ : tf₁.returnContinuation = topFrame.returnContinuation)
    (hrp₁ : tf₁.returnPlace = topFrame.returnPlace)
    (hfr₁ : FrameRelLM2_2Except body env (some dstIdx) m.machine
      { s.frame with locals := locals₁ } tf₁)
    (hdisj₁ : MemoryAllocDisjoint tf₁)
    (hinit₁ : ∀ j ∈ (operandPostStaticEnv stEnv op₀).initLocals,
      some dstIdx ≠ some j → get? locals₁ j ≠ some .uninit)
    (himm₁ : ∀ j ∈ (operandPostStaticEnv stEnv op₀).immLocals,
      some dstIdx ≠ some j → ∀ mp' l,
        tf₁.locals[j]? ≠ some ⟨.live (.indirect mp'), l⟩)
    (hsup : AllocIdSupplyValid k_bud m.machine.memory)
    {tag : Miri.Memory.BorTag} (hprov : mp.ptr.provenance = some (.concrete allocId tag))
    (hmis : mp.misaligned = none)
    (hmeta : mp.metadata = .none)
    (hfind_live : m.machine.memory.live.find? (fun (k, _) => k == allocId) =
      some (allocId, localAlloc))
    (hu_lt : u < m.machine.memory.live.size)
    (hfidx : m.machine.memory.live.findIdx? (fun (k, _) => k == allocId) = some u)
    (hget_u : m.machine.memory.live[u]'hu_lt = (allocId, localAlloc))
    (hbase : m.machine.lookupBaseAddr allocId = some baseAddr)
    (hptr : mp.ptr.offset = Miri.ABI.Size.ofBytes baseAddr)
    (hovf : baseAddr.toNat + (translateTy decl.ty body.layouts).layout.size.bytes.toNat < 2 ^ 64)
    (halign : mp.ptr.offset.isAligned (translateTy decl.ty body.layouts).layout.align.abi = .ok true)
    (hpart₁ : PartialStructState body.layouts decl.ty fields paths k₁ [v₀] alloc₁ words₁)
    (heval_mid :
      Miri.Interpreter.Step.evalStatement (annealStepHooks body.localDecls body.layouts) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.aggregate kind (op₀ :: rest)), span⟩) m =
      Miri.Interpreter.runRvalue
        (writeAggregateFieldsAux (annealAggregateHooks body.localDecls body.layouts)
          ⟨.local 0 dstIdx none topFrame.localsIdentity, translateTy decl.ty body.layouts⟩
          1 (rest.map translateOperand))
        ⟨⟨#[tf₁]⟩, updateAllocMachine m.machine u allocId localAlloc.kind alloc₁⟩) :
    StepRelLM2_2 body env (aggPostStaticEnv stEnv dstIdx (op₀ :: rest)) k_bud m
      (evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.aggregate kind (op₀ :: rest)), span⟩
        body.localDecls body.layouts)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  finish_agg_from_mid hframes hbody hloc hrc hrp
    hcal hstack hbor hprot hcaller hbb hstmt hk_kind hdecl henv hvalid hplen htail
    hev_op₀ hdst_loc₁ hnot_dead heval_mid rfl hid₁ hrc₁ hrp₁ hlt₁ hdst_tf₁
    (hfr₁.of_updateAlloc_excl hdisj₁ hdst_tf₁ hprov hu_lt hget_u)
    hdisj₁ hinit₁ himm₁
    (hsup.of_updateAlloc hu_lt hget_u)
    hprov hmis hmeta
    (LiveAllocEntry.of_set!_self ⟨hfind_live, u, hu_lt, hfidx, hget_u⟩
      hu_lt hfidx ⟨localAlloc.kind, alloc₁⟩)
    hbase hptr hovf halign hpart₁

/-- `LM-2.2` Aggregate Construction Simulation: non-empty tuple and single-variant
struct `Rvalue.Aggregate` assignments step in lockstep across `.Scalar`,
`.ScalarPair`, and `.Memory` layouts (both unpadded and padded, including nested
immediate sub-structs with `ValidStructLayout` at every nesting level),
materializing immediate destinations via upstream `forceAllocation` and keeping
every alignment padding byte `.uninit` in `Allocation.initializationMask`. -/
theorem evalRvalue_aggregate_tuple_struct_simulation
    {body : CapturedMir} {env : StructTypeEnv} {stEnv : LM2_2StaticEnv} {k_bud : Nat}
    {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_2 body env stEnv (k_bud + 1) s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx : Local}
    {kind : MirAst.AggregateKind} {ops : List MirAst.Operand} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.aggregate kind ops), span⟩)
    (hwt : WellTypedLM2_2Aggregate body env stEnv dstIdx kind ops) :
    StepRelLM2_2 body env (aggPostStaticEnv stEnv dstIdx ops) k_bud m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  cases hwt with
  | mk decl fields paths op₀ rest hops_eq hk_kind hdecl henv hvalid hdst_sz4g hplen hdst_sized hdst_align hfields =>
    subst hops_eq
    generalize hz : (0 : Nat) = z at hfields
    cases hfields with
    | cons _ _ _ k₁ _ _ hno_acc₀ hspec₀ htail =>
      subst hz
      rcases hstate with
        ⟨topFrame, hframes, hretCont, ⟨retLay, hretPlace⟩, hframe,
          hinit_env, himm_env, hsupply, hcal, hstack, hbor, hprot, hcaller, hdisj⟩
      rw [stepMirFn_eq_of_not_other body s hcal hphase]
      simp only [hbb, hstmt]
      obtain ⟨slot_dst, mls_dst0, hlt_dst0, _, hslot_dst, _, hmls_eq0, hloc_dst0⟩ :=
        hframe.lookup_local hdecl
      have hcache_dst0 : ∀ l, (topFrame.locals[dstIdx]'hlt_dst0).layout = some l →
          l = translateTy decl.ty body.layouts := by
        rw [hmls_eq0]; exact hloc_dst0.layout_eq
      have hevalPlace_dst := annealEvalPlace_unprojected hframes hlt_dst0 hdecl hcache_dst0
      have hfr₀_exc : FrameRelLM2_2Except body env (some dstIdx) m.machine s.frame
          (cacheFrameLocalLayout topFrame dstIdx hlt_dst0 (translateTy decl.ty body.layouts)) :=
        FrameRelLM2_2Except.of_frameRel (some dstIdx) (hframe.cache_local_layout hdecl hlt_dst0)
      have hdisj₀ : MemoryAllocDisjoint
          (cacheFrameLocalLayout topFrame dstIdx hlt_dst0 (translateTy decl.ty body.layouts)) :=
        MemoryAllocDisjoint_cacheFrameLocalLayout hdisj hlt_dst0 (translateTy decl.ty body.layouts)
      have himm_env₀ : ∀ j ∈ stEnv.immLocals, some dstIdx ≠ some j → ∀ mp l,
          (cacheFrameLocalLayout topFrame dstIdx hlt_dst0
            (translateTy decl.ty body.layouts)).locals[j]? ≠
            some ⟨.live (.indirect mp), l⟩ := by
        intro j hj hne mp l
        have hne_i : dstIdx ≠ j := fun h => hne (congrArg some h)
        dsimp only [cacheFrameLocalLayout]
        rw [Array.getElem?_set_ne _ hne_i]
        exact himm_env j hj mp l
      obtain ⟨mkind, htr_rv, hmkind⟩ :=
        translateRvalue_aggregate_of_isTupleOrSingleAdtKind hk_kind (op₀ :: rest)
      have hm_eval_agg :
          Miri.Interpreter.Step.evalStatement (annealStepHooks body.localDecls body.layouts) ()
            (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.aggregate kind (op₀ :: rest)), span⟩) m =
          Miri.Interpreter.runRvalue
            (writeAggregateFieldsAux (annealAggregateHooks body.localDecls body.layouts)
              ⟨.local 0 dstIdx none topFrame.localsIdentity, translateTy decl.ty body.layouts⟩
              0 ((op₀ :: rest).map translateOperand))
            { m with stack := ⟨#[cacheFrameLocalLayout topFrame dstIdx hlt_dst0
                (translateTy decl.ty body.layouts)]⟩ } := by
        unfold Miri.Interpreter.Step.evalStatement translateStmt
        dsimp only [translateStmtKind, translatePlace, List.map, List.toArray, annealStepHooks]
        rw [htr_rv]
        apply runRvalue_eq_of_eq
        unfold Miri.Interpreter.evalRvalueIntoPlace annealRvalueHooks
        rw [EStateM.bind_eq_ok hevalPlace_dst]
        have hdisc_eq :
            (annealAggregateHooks body.localDecls body.layouts).writeDiscriminant () 0
              ⟨.local 0 dstIdx none topFrame.localsIdentity, translateTy decl.ty body.layouts⟩ =
            pure () := by
          unfold annealAggregateHooks
          rcases hvalid.fields_shape_valid with ⟨_, hf, _⟩ | ⟨_, _, hf, _⟩ <;> simp [hf]
        exact congrFun (writeAggregate_list_eq (annealAggregateHooks body.localDecls body.layouts)
          hmkind ((op₀ :: rest).map translateOperand)
          ⟨.local 0 dstIdx none topFrame.localsIdentity, translateTy decl.ty body.layouts⟩
          rfl hdisc_eq rfl rfl) _
      obtain ⟨opTy₀, fl₀, relOff₀, hop₀, hfl₀_sized, hrel₀_le, hproj₀_ok, hwrite₀_spec⟩ :=
        hspec₀.step_spec hvalid hplen
      have hstep₀_eq := writeAggregateFieldsAux_step_eq body.localDecls body.layouts
        ⟨.local 0 dstIdx none topFrame.localsIdentity, translateTy decl.ty body.layouts⟩
        (.local 0 dstIdx (some relOff₀) topFrame.localsIdentity) fl₀
        0 (translateOperand op₀) (rest.map translateOperand)
        { m with stack := ⟨#[cacheFrameLocalLayout topFrame dstIdx hlt_dst0
            (translateTy decl.ty body.layouts)]⟩ }
        (hproj₀_ok dstIdx topFrame.localsIdentity _)
        (fun mp lay s1 hev =>
          hop₀.annealEvalOperand_indirect_usesStructMemCopyDest_false
            (.local 0 dstIdx (some relOff₀) topFrame.localsIdentity)
            (m := { m with stack := ⟨#[cacheFrameLocalLayout topFrame dstIdx hlt_dst0
                (translateTy decl.ty body.layouts)]⟩ })
            rfl hfr₀_exc
            (fun d hd => by injection hd with hd'; subst hd'; exact hno_acc₀) hev)
      have hsim₀ := evalLM2_2Operand_except
        (m := { m with stack := ⟨#[cacheFrameLocalLayout topFrame dstIdx hlt_dst0
            (translateTy decl.ty body.layouts)]⟩ })
        rfl hfr₀_exc (fun j hj _ => hinit_env j hj) himm_env₀
        (fun d hd => by injection hd with hd'; subst hd'; exact hno_acc₀)
        hop₀ s.memory.globals (some fl₀)
      generalize hev_op₀ :
        evalOperand s.frame.locals op₀ .nil s.memory.globals body.layouts .nil = r_a at hsim₀
      generalize hm_op₀ :
        (annealEvalOperand body.localDecls body.layouts (translateOperand op₀) (some fl₀) >>=
          annealReadImmediate)
          { m with stack := ⟨#[cacheFrameLocalLayout topFrame dstIdx hlt_dst0
              (translateTy decl.ty body.layouts)]⟩ } = r_m at hsim₀
      cases hsim₀ with
      | ub m_err msg =>
        have ha_ub :
            evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.aggregate kind (op₀ :: rest)), span⟩
              body.localDecls body.layouts = MirStepNode.fail .ub := by
          unfold evalStmt; dsimp only
          rw [evalRvalue_aggregate_eq hk_kind, hbor, hcaller]
          dsimp only [evalOperands]; rw [hev_op₀]
        have hm_ub :
            Miri.Interpreter.Step.evalStatement (annealStepHooks body.localDecls body.layouts) ()
              (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.aggregate kind (op₀ :: rest)), span⟩) m =
            (m_err, .error (.undefinedBehavior msg)) := by
          rw [hm_eval_agg]; unfold Miri.Interpreter.runRvalue
          dsimp only [List.map]
          rw [hstep₀_eq, EStateM.bind_eq_error (EStateM.bind_eq_error hm_op₀)]
        rw [ha_ub, miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq hbb hstmt hm_ub]
        exact .ub _ _
      | ok v₀ locals₁ tf₁ imm₀ _ hfr₁ hvRel₀ _ _ hid₁ hrc₁ hrp₁ hsz₁ hpres_acc hpres_mv hinit₁ himm₁ hdisj₁ =>
        have hlt₁ : dstIdx < tf₁.locals.size := by
          rw [hsz₁, cacheFrameLocalLayout_size]; exact hlt_dst0
        have hdst_tf₁ : tf₁.locals[dstIdx]'hlt₁ =
            ⟨mls_dst0.value, some (translateTy decl.ty body.layouts)⟩ := by
          have hget₁ := hpres_acc dstIdx hno_acc₀
          have htf₀_get :
              (cacheFrameLocalLayout topFrame dstIdx hlt_dst0
                (translateTy decl.ty body.layouts)).locals[dstIdx]? =
              some ⟨mls_dst0.value, some (translateTy decl.ty body.layouts)⟩ := by
            dsimp only [cacheFrameLocalLayout]
            rw [Array.getElem?_set_self hlt_dst0, hmls_eq0]
          rw [Array.getElem?_eq_getElem hlt₁, htf₀_get] at hget₁
          exact Option.some.inj hget₁
        have hdst_loc₁ : get? locals₁ dstIdx = some slot_dst :=
          (hpres_mv dstIdx hno_acc₀.not_move).1.trans hslot_dst
        have hdisj_tf₁ := hdisj₁ hdisj₀
        cases hloc_dst0 with
        | base _ _ henv_none _ =>
          rw [henv] at henv_none; cases henv_none
        | structDead _ _ _ _ _ =>
          obtain ⟨hne_rest, hpres_rest⟩ :=
            htail.evalOperands_not_unsupported_and_preserves_dst hfr₁.af_locals_len s.memory.globals
          have ha_ub :
              evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.aggregate kind (op₀ :: rest)), span⟩
                body.localDecls body.layouts = MirStepNode.fail .ub := by
            unfold evalStmt; dsimp only
            rw [evalRvalue_aggregate_eq hk_kind, hbor, hcaller]
            dsimp only [evalOperands]; rw [hev_op₀]; dsimp only
            cases hr : evalOperands locals₁ rest .nil s.memory.globals body.layouts .nil with
            | unsupported => exact absurd hr hne_rest
            | ub => rfl
            | ok tailVals locals_end =>
              dsimp only
              rw [hpres_rest tailVals locals_end hr, hdst_loc₁]
          have hw_dead :
              annealWriteImmediate imm₀
                ⟨.local 0 dstIdx (some relOff₀) topFrame.localsIdentity, fl₀⟩
                { m with stack := ⟨#[tf₁]⟩ } =
              .error (.undefinedBehavior "write to dead local") { m with stack := ⟨#[tf₁]⟩ } := by
            rw [annealWriteImmediate_projected_eq (tf := tf₁) rfl]
            exact annealWriteProjectedLocalImmediate_dead_ub hfl₀_sized rfl hlt₁ hdst_tf₁
          have hm_ub :
              Miri.Interpreter.Step.evalStatement (annealStepHooks body.localDecls body.layouts) ()
                (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.aggregate kind (op₀ :: rest)), span⟩) m =
              ({ m with stack := ⟨#[tf₁]⟩ }, .error (.undefinedBehavior "write to dead local")) := by
            rw [hm_eval_agg]; unfold Miri.Interpreter.runRvalue
            dsimp only [List.map]
            rw [hstep₀_eq, EStateM.bind_eq_error (by rw [EStateM.bind_eq_ok hm_op₀]; exact hw_dead)]
          rw [ha_ub, miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq hbb hstmt hm_ub]
          exact .ub _ _
        | structUninitImm _ _ _ _ _ =>
          obtain ⟨rawAlloc, htry, hbs0, hlen0, hmut0, hpmap0, hmask0⟩ :=
            tryNew_uninit_of_pow2_le_29 (translateTy decl.ty body.layouts).layout.size
              (translateTy decl.ty body.layouts).layout.align.abi hdst_align
          obtain ⟨mem', newId, hres, _, hlive_eq, hfresh_old, hwm_next, hovf_all⟩ :=
            (hsupply.of_succ).reserve_step
          have hfresh : mem'.live.any (fun entry => entry.1 == newId) = false := by
            rw [hlive_eq]; exact hfresh_old
          have hpart₀ : PartialStructState body.layouts decl.ty fields paths 0 []
              (rawAlloc.withExtra none)
              (initWordsFalse (rawAlloc.withExtra none).byteSize) :=
            PartialStructState.of_zero_word hvalid hplen hmut0 hbs0
              (by rw [hbs0]; exact hlen0) hpmap0
              (by rw [hmask0, hbs0]; exact initMaskWordRel_new_false)
          obtain ⟨alloc₁, words₁, hpart₁, hw_imm, _⟩ :=
            hwrite₀_spec (doneVals := []) rfl hvRel₀ hpart₀
          have hw_ok := hw_imm (m := { m with stack := ⟨#[tf₁]⟩ })
            (id0 := topFrame.localsIdentity)
            hdst_sized rfl hlt₁ hdst_tf₁ htry hres hfresh (Or.inl ⟨rfl, rfl⟩)
            (hovf_all _ (by omega))
          exact finish_agg_imm hframes hframe.body_eq hframe.location_eq hretCont hretPlace
            hcal hstack hbor hprot hcaller hbb hstmt hk_kind hdecl henv hvalid hplen hdst_align
            htail hev_op₀ hdst_loc₁ (by nofun) hlt₁ hid₁ hrc₁ hrp₁ hfr₁ hdisj_tf₁
            hinit₁ himm₁ hres hfresh_old hfresh (hwm_next alloc₁)
            (hovf_all _ hdst_sz4g) hpart₁
            (by
              rw [hm_eval_agg]; apply runRvalue_eq_of_eq; dsimp only [List.map]
              rw [hstep₀_eq, EStateM.bind_eq_ok (by rw [EStateM.bind_eq_ok hm_op₀]; exact hw_ok)])
        | structImm fs' ps' oldVal oldImm _ henv' _ himm_old =>
          have heq_fp := henv.symm.trans henv'
          injection heq_fp with hpair; injection hpair with hfs hps; rw [← hfs, ← hps] at himm_old
          have hne_uninit : oldImm ≠ .uninit := by cases himm_old <;> nofun
          obtain ⟨rawAlloc, mem', newId, alloc_init, htry, hres, hlive_eq, hfresh,
              hwm_next, hovf_all, hw_old, hsmpr_init⟩ :=
            StructMemPlaceRel.of_immediate (m := { m with stack := ⟨#[tf₁]⟩ })
              himm_old hdst_align (hsupply.of_succ)
          obtain ⟨allocId_init, _, _, la_init, words₀, hprov_init, _, _, hlive_init, _, _, _, _, hpart₀_la⟩ :=
            PartialStructState.of_structMemPlaceRel hsmpr_init
          have hid_eq : allocId_init = newId := by
            dsimp only [stackAllocPlace] at hprov_init
            injection hprov_init with h1; injection h1 with h2 _; exact h2.symm
          cases hid_eq
          have hla_eq : la_init = ⟨.stack, alloc_init⟩ := by
            have hf_self := (LiveAllocEntry.of_push_fresh_self
              (la := ⟨.stack, alloc_init⟩) hfresh).1
            have hf_la :
                (mem'.live.push (newId, ⟨.stack, alloc_init⟩)).find? (fun (k, _) => k == newId) =
                some (newId, la_init) := hlive_init.1
            exact (Prod.mk.inj (Option.some.inj (hf_la.symm.trans hf_self))).2
          subst hla_eq
          obtain ⟨alloc₁, words₁, hpart₁, hw_imm, _⟩ :=
            hwrite₀_spec (doneVals := []) rfl hvRel₀ hpart₀_la
          have hw_ok := hw_imm (m := { m with stack := ⟨#[tf₁]⟩ })
            (id0 := topFrame.localsIdentity)
            hdst_sized rfl hlt₁ hdst_tf₁ htry hres hfresh
            (Or.inr ⟨hne_uninit, hw_old⟩) (hovf_all _ (by omega))
          have hfresh_old : m.machine.memory.live.any (fun entry => entry.1 == newId) = false := by
            rw [← hlive_eq]; exact hfresh
          exact finish_agg_imm hframes hframe.body_eq hframe.location_eq hretCont hretPlace
            hcal hstack hbor hprot hcaller hbb hstmt hk_kind hdecl henv hvalid hplen hdst_align
            htail hev_op₀ hdst_loc₁ (by nofun) hlt₁ hid₁ hrc₁ hrp₁ hfr₁ hdisj_tf₁
            hinit₁ himm₁ hres hfresh_old hfresh (hwm_next alloc₁)
            (hovf_all _ hdst_sz4g) hpart₁
            (by
              rw [hm_eval_agg]; apply runRvalue_eq_of_eq; dsimp only [List.map]
              rw [hstep₀_eq, EStateM.bind_eq_ok (by rw [EStateM.bind_eq_ok hm_op₀]; exact hw_ok)])
        | structUninitInd fs' ps' mp _ henv' _ hmp =>
          have heq_fp := henv.symm.trans henv'
          injection heq_fp with hpair; injection hpair with hfs hps; rw [← hfs] at hmp
          rcases hmp with ⟨allocId, tag_init, baseAddr, localAlloc, _, hprov, hmis, hmeta,
            ⟨hfind_live, u, hu_lt, hfidx, hget_u⟩, hbase, hptr, hovf, hmut, halign,
            hbs, hlen, hpmap, hmask_u⟩
          have hpart₀ : PartialStructState body.layouts decl.ty fields paths 0 []
              localAlloc.allocation
              (initWordsFalse localAlloc.allocation.byteSize) :=
            PartialStructState.of_zero_word hvalid hplen hmut hbs hlen hpmap
              (by rw [hmask_u, hbs]; exact initMaskWordRel_new_false)
          obtain ⟨alloc₁, words₁, hpart₁, _, hw_ind⟩ :=
            hwrite₀_spec (doneVals := []) rfl hvRel₀ hpart₀
          have hw_ok := hw_ind (m := { m with stack := ⟨#[tf₁]⟩ })
            (id0 := topFrame.localsIdentity)
            rfl hlt₁ hdst_tf₁ hprov hbase hptr
            (by omega) hu_lt hfidx hget_u rfl
          exact finish_agg_ind hframes hframe.body_eq hframe.location_eq hretCont hretPlace
            hcal hstack hbor hprot hcaller hbb hstmt hk_kind hdecl henv hvalid hplen htail
            hev_op₀ hdst_loc₁ (by nofun) hlt₁ hdst_tf₁ hid₁ hrc₁ hrp₁ hfr₁ hdisj_tf₁
            hinit₁ himm₁ (hsupply.mono (Nat.le_succ k_bud))
            hprov hmis hmeta hfind_live hu_lt hfidx hget_u hbase hptr hovf halign hpart₁
            (by
              rw [hm_eval_agg]; apply runRvalue_eq_of_eq; dsimp only [List.map]
              rw [hstep₀_eq, EStateM.bind_eq_ok (by rw [EStateM.bind_eq_ok hm_op₀]; exact hw_ok)])
        | structInd fs' ps' _ mp _ henv' _ hsmpr =>
          have heq_fp := henv.symm.trans henv'
          injection heq_fp with hpair; injection hpair with hfs hps; rw [← hfs, ← hps] at hsmpr
          obtain ⟨allocId, tag_init, baseAddr, localAlloc, words₀,
              hprov, hmis, hmeta, hlive_d,
              hbase, hptr, hovf, halign, hpart₀⟩ :=
            PartialStructState.of_structMemPlaceRel hsmpr
          obtain ⟨hfind_live, u, hu_lt, hfidx, hget_u⟩ := hlive_d
          obtain ⟨alloc₁, words₁, hpart₁, _, hw_ind⟩ :=
            hwrite₀_spec (doneVals := []) rfl hvRel₀ hpart₀
          have hw_ok := hw_ind (m := { m with stack := ⟨#[tf₁]⟩ })
            (id0 := topFrame.localsIdentity)
            rfl hlt₁ hdst_tf₁ hprov hbase hptr
            (by omega) hu_lt hfidx hget_u rfl
          exact finish_agg_ind hframes hframe.body_eq hframe.location_eq hretCont hretPlace
            hcal hstack hbor hprot hcaller hbb hstmt hk_kind hdecl henv hvalid hplen htail
            hev_op₀ hdst_loc₁ (by nofun) hlt₁ hdst_tf₁ hid₁ hrc₁ hrp₁ hfr₁ hdisj_tf₁
            hinit₁ himm₁ (hsupply.mono (Nat.le_succ k_bud))
            hprov hmis hmeta hfind_live hu_lt hfidx hget_u hbase hptr hovf halign hpart₁
            (by
              rw [hm_eval_agg]; apply runRvalue_eq_of_eq; dsimp only [List.map]
              rw [hstep₀_eq, EStateM.bind_eq_ok (by rw [EStateM.bind_eq_ok hm_op₀]; exact hw_ok)])


/-! ## 7. Nested Field Write Simulation (`step_assign_nested_field_write_simulation`) -/

/-- Static environment update after a projected field write `_dst.projs = Use(op)`:
`op` updates `stEnv` via `operandPostStaticEnv`, `dstIdx` remains initialized,
and `dstIdx` is materialized in stack memory (removed from `immLocals`). -/
def fieldWritePostStaticEnv (stEnv : LM2_2StaticEnv) (dstIdx : Local)
    (op : MirAst.Operand) : LM2_2StaticEnv :=
  let s1 := operandPostStaticEnv stEnv op
  { s1 with immLocals := s1.immLocals.filter (· != dstIdx) }

/-- 100% state-independent typing predicate for projected scalar leaf writes
`_dst.projs = Rvalue.Use(op)` across immediate (`.Scalar`, `.ScalarPair`) and
memory-backed (`.Memory`) tuples and single-variant structs, including multi-step
nested `.Field` chains. -/
inductive WellTypedLM2_2FieldWrite
    (body : CapturedMir) (env : StructTypeEnv) (stEnv : LM2_2StaticEnv)
    (dstIdx : Local) (projs : List ProjectionElem) (op : MirAst.Operand) : Prop where
  | mk
      (decl : LocalDecl)
      (fields : List StructFieldDesc)
      (paths : List (List ProjectionElem))
      (k : Nat)
      (decl_lookup : get? body.localDecls dstIdx = some decl)
      (env_lookup : env decl.ty = some (fields, paths))
      (dst_init : dstIdx ∈ stEnv.initLocals)
      (dst_sized : (translateTy decl.ty body.layouts).layout.isSized = true)
      (dst_align : (translateTy decl.ty body.layouts).layout.align.abi.pow2 ≤ 29)
      (leaf_idx : k < fields.length)
      (path_eq : paths[k]? = some projs)
      (disj_paths : ∀ j (hj : j < paths.length), j ≠ k →
        DisjointFieldPaths projs (paths[j]'hj))
      (proj_chain : ValidFieldProjChain body.layouts
        (translateTy decl.ty body.layouts) projs
        (fields[k]'leaf_idx).ty (fields[k]'leaf_idx).offset)
      (leaf_sized : (translateTy (fields[k]'leaf_idx).ty body.layouts).layout.isSized = true)
      (leaf_env_none : env (fields[k]'leaf_idx).ty = none)
      (leaf_prim : IsPrimScalarTy (fields[k]'leaf_idx).ty)
      (no_move_dst : OperandDoesNotMoveLocal dstIdx op)
      (op_wt : WellTypedLM2_2Operand body env stEnv op (fields[k]'leaf_idx).ty) :
      WellTypedLM2_2FieldWrite body env stEnv dstIdx projs op

theorem evalRvalue_use_nil_borrows
    (locals : List LocalSlot) (op : MirAst.Operand) (mem : Memory)
    (hbor : mem.borrows = .nil) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalRvalue locals (.use op) mem localDecls layouts =
      match evalOperand locals op .nil mem.globals layouts mem.callerLocals with
      | .ok val locals' => .ok val locals' mem
      | .ub => .ub
      | .unsupported => .unsupported := by
  unfold evalRvalue; dsimp only; rw [hbor]
  cases evalOperand locals op [] mem.globals layouts mem.callerLocals with
  | ub => rfl
  | unsupported => rfl
  | ok v locals' =>
    cases op with
    | constant _ => rfl
    | move pl | copy pl =>
      rcases pl with ⟨_, projs⟩
      cases projs with
      | nil => rfl
      | cons p _ => cases p <;> rfl

theorem evalStatement_assign_use_eq
    {body : CapturedMir} {dst : Place} {op : MirAst.Operand} {span : String}
    {m m₀ : AnnealStepState}
    {destRef : Miri.Interpreter.RuntimePlaceRef AnnealProv}
    {destLay : Miri.Interpreter.LocalLayout}
    (hplace : annealEvalPlace body.localDecls body.layouts (translatePlace dst) m =
      .ok ⟨destRef, destLay⟩ m₀)
    (hnomem : usesStructMemCopyDest ⟨destRef, destLay⟩ = false) :
    Miri.Interpreter.Step.evalStatement (annealStepHooks body.localDecls body.layouts) ()
      (translateStmt ⟨.assign dst (.use op), span⟩) m =
    Miri.Interpreter.runRvalue
      ((annealEvalOperand body.localDecls body.layouts (translateOperand op)
          (some destLay) >>=
        annealReadImmediate) >>= fun r => annealWriteImmediate r.imm ⟨destRef, destLay⟩) m₀ := by
  unfold Miri.Interpreter.Step.evalStatement translateStmt
  dsimp only [translateStmtKind, translateRvalue, annealStepHooks]
  apply runRvalue_eq_of_eq
  unfold Miri.Interpreter.evalRvalueIntoPlace annealRvalueHooks
  rw [EStateM.bind_eq_ok hplace]
  dsimp only [Miri.Interpreter.RvalueHooks.evalOperandAt]
  simp only [hnomem, Bool.false_eq_true, ↓reduceIte, Bind.bind, EStateM.bind]
  cases annealEvalOperand body.localDecls body.layouts (translateOperand op)
      (some destLay) m₀ <;> rfl

theorem evalStatement_assign_use_mem_eq
    {body : CapturedMir} {dst : Place} {op : MirAst.Operand} {span : String}
    {m m₀ : AnnealStepState}
    {destRef : Miri.Interpreter.RuntimePlaceRef AnnealProv}
    {destLay : Miri.Interpreter.LocalLayout}
    (hplace : annealEvalPlace body.localDecls body.layouts (translatePlace dst) m =
      .ok ⟨destRef, destLay⟩ m₀)
    (hmem : usesStructMemCopyDest ⟨destRef, destLay⟩ = true) :
    Miri.Interpreter.Step.evalStatement (annealStepHooks body.localDecls body.layouts) ()
      (translateStmt ⟨.assign dst (.use op), span⟩) m =
    Miri.Interpreter.runRvalue
      (annealEvalOperand body.localDecls body.layouts (translateOperand op) (some destLay) >>=
        fun src => annealStructMemCopyOp body.localDecls body.layouts src ⟨destRef, destLay⟩) m₀ := by
  unfold Miri.Interpreter.Step.evalStatement translateStmt
  dsimp only [translateStmtKind, translateRvalue, annealStepHooks]
  apply runRvalue_eq_of_eq
  unfold Miri.Interpreter.evalRvalueIntoPlace annealRvalueHooks
  rw [EStateM.bind_eq_ok hplace]
  dsimp only [Miri.Interpreter.RvalueHooks.evalOperandAt]
  simp only [hmem, ↓reduceIte]

private theorem updateAllocMachine_stackAllocMachine_self
    (mach : AnnealMachine) (mem' : AnnealMemory) (newId : Miri.Memory.AllocId)
    (alloc_init alloc_final :
      Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)) :
    updateAllocMachine (stackAllocMachine mach mem' newId alloc_init)
      mem'.live.size newId .stack alloc_final =
    stackAllocMachine mach mem' newId alloc_final := by
  let e_init : Miri.Memory.AllocId × AnnealLocalAlloc := (newId, ⟨.stack, alloc_init⟩)
  let e_fin : Miri.Memory.AllocId × AnnealLocalAlloc := (newId, ⟨.stack, alloc_final⟩)
  have hlist :
      (mem'.live.toList ++ [e_init]).set mem'.live.toList.length e_fin =
      mem'.live.toList ++ [e_fin] := by
    induction mem'.live.toList with
    | nil => rfl
    | cons _ _ ih => dsimp [List.set]; rw [ih]
  have harr :
      (mem'.live.push e_init).set! mem'.live.size e_fin = mem'.live.push e_fin := by
    apply Array.ext'
    rw [Array.set!_eq_setIfInBounds, Array.toList_setIfInBounds, Array.toList_push,
      Array.toList_push, ← Array.length_toList]
    exact hlist
  dsimp only [updateAllocMachine, stackAllocMachine]
  rw [harr]

private theorem structMemPlaceRel_fieldLayout_eq
    {mach : AnnealMachine} {ty : Ty} {layouts : LayoutTable}
    {fields : List StructFieldDesc} {paths : List (List ProjectionElem)}
    {rootVal : Value} {mp : Miri.Interpreter.MemPlace AnnealProv}
    (h : StructMemPlaceRel mach ty layouts fields paths rootVal mp)
    {k : Nat} (hk : k < fields.length) :
    (fields[k]'hk).fieldLayout = (translateTy (fields[k]'hk).ty layouts).layout := by
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hfields, _⟩
  obtain ⟨_, hfl, _⟩ := hfields k hk
  exact hfl

private theorem FrameRelLM2_2Except.fill_excluded
    {body : CapturedMir} {env : StructTypeEnv} {dstIdx : Local} {decl : LocalDecl}
    {mach : AnnealMachine} {af : StackFrame}
    {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {slot' : LocalSlot}
    {mls' : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout}
    (h : FrameRelLM2_2Except body env (some dstIdx) mach af mf)
    (hdecl : get? body.localDecls dstIdx = some decl)
    (hlt_af : dstIdx < af.locals.length)
    (hlt_mf : dstIdx < mf.locals.size)
    (hdst_mf : mf.locals[dstIdx]'hlt_mf = mls')
    (hrel : LocalRelLM2_2 env mach decl body.layouts slot' mls') :
    FrameRelLM2_2 body env mach { af with locals := af.locals.set dstIdx slot' } mf := by
  refine ⟨h.body_eq, h.location_eq, by simp [h.af_locals_len], h.mf_locals_size, ?_⟩
  intro i d sl ml hd_i hs_i hm_i
  by_cases hi : i = dstIdx
  · subst hi
    rw [hdecl] at hd_i; injection hd_i with hd_eq; subst hd_eq
    dsimp [get?] at hs_i
    rw [List.getElem?_set_self hlt_af] at hs_i; injection hs_i with hsl; subst hsl
    rw [Array.getElem?_eq_getElem hlt_mf, hdst_mf] at hm_i
    injection hm_i with hml; subst hml
    exact hrel
  · dsimp [get?] at hs_i
    rw [List.getElem?_set_ne (Ne.symm hi)] at hs_i
    exact h.locals_rel i d sl ml (fun heq => hi (Option.some.inj heq.symm)) hd_i hs_i hm_i

/-- Padding-byte extraction witness for `StructMemPlaceRel`: every padding byte
`p` (`isStructPaddingByte fields layout.size p`) is `.ok false` in
`Allocation.initializationMask`, so whole-allocation `isRangeInitialized` cannot
succeed. -/
theorem StructMemPlaceRel.has_uninit_of_padding_byte
    {mach : AnnealMachine} {ty : Ty} {layouts : LayoutTable}
    {fields : List StructFieldDesc} {paths : List (List ProjectionElem)}
    {rootVal : Value} {mp : Miri.Interpreter.MemPlace AnnealProv}
    (h : StructMemPlaceRel mach ty layouts fields paths rootVal mp)
    {p : Nat} (hp : isStructPaddingByte fields (translateTy ty layouts).layout.size p) :
    ∃ allocId localAlloc,
      (∃ tag, mp.ptr.provenance = some (.concrete allocId tag)) ∧
      mach.memory.live.find? (fun (k, _) => k == allocId) = some (allocId, localAlloc) ∧
      (∀ q, isStructPaddingByte fields (translateTy ty layouts).layout.size q →
        localAlloc.allocation.initializationMask.get
          (Miri.ABI.Size.ofBytes (UInt64.ofNat q)) = .ok false) ∧
      localAlloc.allocation.initializationMask.isRangeInitialized
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateTy ty layouts).layout.size) ≠
        .ok (.ok ()) := by
  rcases h with ⟨allocId, _, _, localAlloc, word, _, _, _, _, hprov, _, _,
    ⟨hfind, _⟩, _, _, _, _, _, hbs, _, _, hmask, _, _, hpad⟩
  have hmask_lay : InitMaskWordRel localAlloc.allocation.initializationMask
      (translateTy ty layouts).layout.size word := by
    rw [← hbs]; exact hmask
  exact ⟨allocId, localAlloc, ⟨_, hprov⟩, hfind, hpad,
    initMaskWordRel_not_isRangeInitialized_of_get_false hmask_lay hp.1 (hpad p hp)⟩

private theorem step_assign_nested_field_write_simulation_core
    {body : CapturedMir} {env : StructTypeEnv} {stEnv : LM2_2StaticEnv} {k_bud : Nat}
    {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_2 body env stEnv (k_bud + 1) s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx : Local} {projs : List ProjectionElem}
    {op : MirAst.Operand} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, projs⟩ (.use op), span⟩)
    (hwt : WellTypedLM2_2FieldWrite body env stEnv dstIdx projs op) :
    StepRelLM2_2 body env (fieldWritePostStaticEnv stEnv dstIdx op) k_bud m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    (∀ s' : MachineState,
      stepMirFn body s = .step s' →
      ∃ decl fields paths rootVal mp,
        get? body.localDecls dstIdx = some decl ∧
        env decl.ty = some (fields, paths) ∧
        get? s'.frame.locals dstIdx = some (.init rootVal) ∧
        StructMemPlaceRel
          (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m).1.machine
          decl.ty body.layouts fields paths rootVal mp ∧
        ∃ tf lay,
          (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m).1.stack.frames =
            #[tf] ∧
          tf.locals[dstIdx]? = some ⟨.live (.indirect mp), lay⟩) := by
  cases hwt with
  | mk decl fields paths k hdecl henv hdst_init hdst_sized hdst_align hk hpath_eq
      hdisj_paths hchain hleaf_sized hleaf_env hleaf_prim hno_move hop =>
    rcases hstate with
      ⟨topFrame, hframes, hretCont, ⟨retLay, hretPlace⟩, hframe,
        hinit_env, himm_env, hsupply, hcal, hstack, hbor, hprot, hcaller, hdisj⟩
    rw [stepMirFn_eq_of_not_other body s hcal hphase]
    simp only [hbb, hstmt]
    obtain ⟨idx₀, fty₀, ps, hprojs_eq⟩ : ∃ idx₀ fty₀ ps, projs = .field idx₀ fty₀ :: ps := by
      cases hpr : projs with
      | nil => exact False.elim (hchain.ne_nil hpr)
      | cons p₀ ps =>
        obtain ⟨i, t, rfl⟩ := hchain.only_fields p₀ (by rw [hpr]; exact List.mem_cons_self)
        exact ⟨i, t, ps, rfl⟩
    subst hprojs_eq
    obtain ⟨hk_p, hpk_eq⟩ := List.getElem?_eq_some_iff.mp hpath_eq
    obtain ⟨slot_dst, mls_dst0, hlt_dst0, _, hslot_dst, _, hmls_eq0, hloc_dst0⟩ :=
      hframe.lookup_local hdecl
    have hcache_dst0 : ∀ l, (topFrame.locals[dstIdx]'hlt_dst0).layout = some l →
        l = translateTy decl.ty body.layouts := by
      rw [hmls_eq0]; exact hloc_dst0.layout_eq
    have hevalPlace := annealEvalPlace_projected hframes hlt_dst0 hdecl hcache_dst0 hchain
    have hm_eval := evalStatement_assign_use_eq (op := op) (span := span) hevalPlace
      (hop.usesStructMemCopyDest_false _)
    have hfr₀_exc : FrameRelLM2_2Except body env none m.machine s.frame
        (cacheFrameLocalLayout topFrame dstIdx hlt_dst0 (translateTy decl.ty body.layouts)) :=
      FrameRelLM2_2Except.of_frameRel none (hframe.cache_local_layout hdecl hlt_dst0)
    have hdisj₀ : MemoryAllocDisjoint
        (cacheFrameLocalLayout topFrame dstIdx hlt_dst0 (translateTy decl.ty body.layouts)) :=
      MemoryAllocDisjoint_cacheFrameLocalLayout hdisj hlt_dst0 (translateTy decl.ty body.layouts)
    have himm_env₀ : ∀ j ∈ stEnv.immLocals, (none : Option Local) ≠ some j → ∀ mp l,
        (cacheFrameLocalLayout topFrame dstIdx hlt_dst0
          (translateTy decl.ty body.layouts)).locals[j]? ≠
          some ⟨.live (.indirect mp), l⟩ := by
      intro j hj _ mp l
      dsimp only [cacheFrameLocalLayout]
      by_cases hij : dstIdx = j
      · subst hij
        rw [Array.getElem?_set_self hlt_dst0, hmls_eq0]
        intro heq; injection heq with hls
        rcases mls_dst0 with ⟨val0, lay0⟩
        injection hls with hv_eq _; subst hv_eq
        exact himm_env dstIdx hj mp lay0
          (by rw [Array.getElem?_eq_getElem hlt_dst0, hmls_eq0])
      · rw [Array.getElem?_set_ne _ hij]; exact himm_env j hj mp l
    have hsim := evalLM2_2Operand_except
      (m := { m with stack := ⟨#[cacheFrameLocalLayout topFrame dstIdx hlt_dst0
          (translateTy decl.ty body.layouts)]⟩ })
      rfl hfr₀_exc (fun j hj _ => hinit_env j hj) himm_env₀ (by nofun)
      hop s.memory.globals (some (translateTy (fields[k]'hk).ty body.layouts))
    generalize hev_op :
      evalOperand s.frame.locals op .nil s.memory.globals body.layouts .nil = r_a at hsim
    generalize hm_op :
      (annealEvalOperand body.localDecls body.layouts (translateOperand op)
        (some (translateTy (fields[k]'hk).ty body.layouts)) >>= annealReadImmediate)
        { m with stack := ⟨#[cacheFrameLocalLayout topFrame dstIdx hlt_dst0
            (translateTy decl.ty body.layouts)]⟩ } = r_m at hsim
    cases hsim with
    | ub m_err msg =>
      have ha_ub :
          evalStmt s ⟨.assign ⟨dstIdx, .field idx₀ fty₀ :: ps⟩ (.use op), span⟩
            body.localDecls body.layouts = MirStepNode.fail .ub := by
        unfold evalStmt; dsimp only
        rw [evalRvalue_use_nil_borrows _ _ _ hbor, hcaller, hev_op]
      have hm_ub :
          Miri.Interpreter.Step.evalStatement (annealStepHooks body.localDecls body.layouts) ()
            (translateStmt ⟨.assign ⟨dstIdx, .field idx₀ fty₀ :: ps⟩ (.use op), span⟩) m =
          (m_err, .error (.undefinedBehavior msg)) := by
        rw [hm_eval]; unfold Miri.Interpreter.runRvalue; rw [EStateM.bind_eq_error hm_op]
      rw [ha_ub, miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq hbb hstmt hm_ub]
      exact ⟨.ub _ _, fun _ h => nomatch h⟩
    | ok v locals₁ tf₁ imm _ hfr₁ hvRel _ _ hid₁ hrc₁ hrp₁ hsz₁ _ hpres_mv hinit₁ himm₁ hdisj₁ =>
      dsimp only [cacheFrameLocalLayout] at hid₁ hrc₁ hrp₁
      have hlt₁ : dstIdx < tf₁.locals.size := by
        rw [hsz₁, cacheFrameLocalLayout_size]; exact hlt_dst0
      have htf₀_dst :
          (cacheFrameLocalLayout topFrame dstIdx hlt_dst0
            (translateTy decl.ty body.layouts)).locals[dstIdx]? =
          some ⟨mls_dst0.value, some (translateTy decl.ty body.layouts)⟩ := by
        dsimp only [cacheFrameLocalLayout]
        rw [Array.getElem?_set_self hlt_dst0, hmls_eq0]
      obtain ⟨hdst_loc₁_eq, hdst_tf₁_ex⟩ := hpres_mv dstIdx hno_move
      have hdst_loc₁ : get? locals₁ dstIdx = some slot_dst := hdst_loc₁_eq.trans hslot_dst
      obtain ⟨l1, htf₁_get⟩ := hdst_tf₁_ex mls_dst0.value _ htf₀_dst
      have hl1_eq : l1 = translateTy decl.ty body.layouts :=
        (hfr₁.locals_rel dstIdx decl slot_dst ⟨mls_dst0.value, some l1⟩
          (by nofun) hdecl hdst_loc₁ htf₁_get).layout_eq l1 rfl
      subst hl1_eq
      have hdst_tf₁ : tf₁.locals[dstIdx]'hlt₁ =
          ⟨mls_dst0.value, some (translateTy decl.ty body.layouts)⟩ := by
        rw [Array.getElem?_eq_getElem hlt₁] at htf₁_get
        exact Option.some.inj htf₁_get
      obtain ⟨hlt_loc₁, _⟩ := List.getElem?_eq_some_iff.mp (get?_eq_getElem? locals₁ dstIdx ▸ hdst_loc₁)
      have hdisj_tf₁ := hdisj₁ hdisj₀
      have hfr₁_excl : FrameRelLM2_2Except body env (some dstIdx) m.machine
          { s.frame with locals := locals₁ } tf₁ :=
        ⟨hfr₁.body_eq, hfr₁.location_eq, hfr₁.af_locals_len, hfr₁.mf_locals_size,
          fun i d sl ml _ hd hs hm => hfr₁.locals_rel i d sl ml (by nofun) hd hs hm⟩
      cases hvRel with
      | immStruct _ _ _ _ hsub _ =>
        have := hsub.env_eq; rw [hleaf_env] at this; cases this
      | primScalar sc msc _ _ himmRel =>
        obtain ⟨_, _, hsc_eq, hmsc_eq, hrel, hlay_sz, hbool, hchar⟩ :=
          himmRel.of_primitive_scalar hleaf_prim
        injection hsc_eq with hsc_eq'; subst hsc_eq'
        injection hmsc_eq with hmsc_eq'
        injection hmsc_eq' with hmsc_eq''
        injection hmsc_eq'' with hmsc_eq'''
        subst hmsc_eq'''
        cases hloc_dst0 with
        | base _ _ henv_none _ => rw [henv] at henv_none; cases henv_none
        | structUninitImm _ _ _ _ _ | structUninitInd _ _ _ _ _ _ _ =>
          exact False.elim (hinit_env dstIdx hdst_init hslot_dst)
        | structDead _ _ _ _ _ =>
          have ha_ub :
              evalStmt s ⟨.assign ⟨dstIdx, .field idx₀ fty₀ :: ps⟩ (.use op), span⟩
                body.localDecls body.layouts = MirStepNode.fail .ub := by
            unfold evalStmt; dsimp only
            rw [evalRvalue_use_nil_borrows _ _ _ hbor, hcaller, hev_op]; dsimp only
            rw [hdst_loc₁]
          have hw_dead :
              annealWriteImmediate (.scalar (.fromScalarInt msc))
                ⟨.local 0 dstIdx (some (fields[k]'hk).offset) topFrame.localsIdentity,
                  translateTy (fields[k]'hk).ty body.layouts⟩
                { m with stack := ⟨#[tf₁]⟩ } =
              .error (.undefinedBehavior "write to dead local") { m with stack := ⟨#[tf₁]⟩ } := by
            rw [annealWriteImmediate_projected_eq (tf := tf₁) rfl]
            exact annealWriteProjectedLocalImmediate_dead_ub hleaf_sized rfl hlt₁ hdst_tf₁
          have hm_ub :
              Miri.Interpreter.Step.evalStatement (annealStepHooks body.localDecls body.layouts) ()
                (translateStmt ⟨.assign ⟨dstIdx, .field idx₀ fty₀ :: ps⟩ (.use op), span⟩) m =
              ({ m with stack := ⟨#[tf₁]⟩ }, .error (.undefinedBehavior "write to dead local")) := by
            rw [hm_eval]; unfold Miri.Interpreter.runRvalue
            rw [EStateM.bind_eq_ok hm_op]; dsimp only; rw [hw_dead]
          rw [ha_ub, miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq hbb hstmt hm_ub]
          exact ⟨.ub _ _, fun _ h => nomatch h⟩
        | structImm fs' ps' rootVal oldImm _ henv' _ himm_old =>
          have heq_fp := henv.symm.trans henv'
          injection heq_fp with hpair; injection hpair with hfs hps; rw [← hfs, ← hps] at himm_old
          have hne_uninit : oldImm ≠ .uninit := by cases himm_old <;> nofun
          obtain ⟨rawAlloc, mem', newId, alloc_init, htry, hres, hlive_eq, hfresh,
              hwm_next, hovf_all, hw_old, hsmpr_init⟩ :=
            StructMemPlaceRel.of_immediate (m := { m with stack := ⟨#[tf₁]⟩ })
              himm_old hdst_align (hsupply.of_succ)
          have hfl_sz : (fields[k]'hk).fieldLayout.size = translateSizeBytes sc.sizeBytes := by
            rw [structMemPlaceRel_fieldLayout_eq hsmpr_init hk, hlay_sz]
          obtain ⟨rootVal', allocId_w, _, _, la_w, alloc_final, u_w,
              hprov_w, _, _, _, hu_lt_w, hfidx_w, hget_w, hw_new, hw_proj, hsmpr_fin⟩ :=
            hsmpr_init.write_leaf_field hk hk_p
              (fun j hj hjk => by rw [hpk_eq]; exact hdisj_paths j hj hjk)
              hrel hfl_sz hbool hchar
          have hid_w : allocId_w = newId := by
            dsimp only [stackAllocPlace] at hprov_w
            injection hprov_w with h1; injection h1 with h2 _; exact h2.symm
          cases hid_w
          have hu_eq : u_w = mem'.live.size := by
            obtain ⟨_, u_s, hu_s_lt, hfidx_self, hget_s⟩ :=
              LiveAllocEntry.of_push_fresh_self (la := ⟨.stack, alloc_init⟩) hfresh
            have hu_w_eq : u_w = u_s := Option.some.inj (hfidx_w.symm.trans hfidx_self)
            subst hu_w_eq
            apply Classical.byContradiction
            intro hne_sz
            have hlt_old : u_w < mem'.live.size := by
              rw [Array.size_push] at hu_s_lt; omega
            rw [Array.getElem_push_lt hlt_old] at hget_s
            have hmem_any : mem'.live.any (fun entry => entry.1 == newId) = true := by
              rw [Array.any_eq_true]
              exact ⟨u_w, hlt_old, by rw [hget_s]; simp⟩
            rw [hfresh] at hmem_any; cases hmem_any
          subst hu_eq
          have hla_w : la_w = ⟨.stack, alloc_init⟩ := by
            have hget_self : (mem'.live.push (newId, ⟨.stack, alloc_init⟩))[mem'.live.size]'hu_lt_w =
                (newId, ⟨.stack, alloc_init⟩) := Array.getElem_push_eq
            exact (Prod.mk.inj (hget_w.symm.trans hget_self)).2
          subst hla_w
          rw [updateAllocMachine_stackAllocMachine_self] at hsmpr_fin
          have hoff_lt32 : (fields[k]'hk).offset.bytes.toNat < 2 ^ 32 := by
            have hbnd_k := hchain.bounds
            cases himm_old with
            | scalarWrapper f₀ _ _ _ _ _ _ _ _ _ hf₀_off _ _ _ _ _ _ _ =>
              simp at hk; subst hk; dsimp; rw [hf₀_off]; decide
            | scalarPair _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hsz4g =>
              omega
          have hw_ok :
              annealWriteImmediate (.scalar (.fromScalarInt msc))
                ⟨.local 0 dstIdx (some (fields[k]'hk).offset) topFrame.localsIdentity,
                  translateTy (fields[k]'hk).ty body.layouts⟩
                { m with stack := ⟨#[tf₁]⟩ } =
              .ok () ⟨⟨#[{ tf₁ with
                locals := tf₁.locals.set dstIdx
                  ⟨.live (.indirect (stackAllocPlace newId)),
                    some (translateTy decl.ty body.layouts)⟩ hlt₁ }]⟩,
                stackAllocMachine m.machine mem' newId alloc_final⟩ := by
            rw [annealWriteImmediate_projected_eq (tf := tf₁) rfl]
            cases oldImm with
            | uninit => exact absurd rfl hne_uninit
            | scalar _ | scalarPair _ _ =>
              exact annealWriteProjectedLocalImmediate_immediate_scalar_ok
                (alloc_init := alloc_init) hleaf_sized hdst_sized rfl hlt₁ hdst_tf₁
                htry hres hfresh hw_old (hovf_all _ hoff_lt32) hw_new
          have ha_ok :
              evalStmt s ⟨.assign ⟨dstIdx, .field idx₀ fty₀ :: ps⟩ (.use op), span⟩
                body.localDecls body.layouts =
              MirStepNode.step (advanceStmt s (locals₁.set dstIdx (.init rootVal')) s.memory) := by
            unfold evalStmt; dsimp only
            rw [evalRvalue_use_nil_borrows _ _ _ hbor, hcaller, hev_op]; dsimp only
            rw [hdst_loc₁]; dsimp only
            have hwp : writeProjectedValue locals₁ rootVal (.field idx₀ fty₀ :: ps) (.scalar sc) =
                .ok rootVal' := by rw [← hpk_eq]; exact hw_proj locals₁
            rw [hwp]; dsimp only
            rw [set?_eq_some_set hlt_loc₁, hprot, hbor]
            dsimp only [invalidateConflictingBorrowsAtProj]
            apply congrArg (fun mem =>
              MirStepNode.step (advanceStmt s (locals₁.set dstIdx (.init rootVal')) mem))
            revert hbor hprot; generalize s.memory = mem; rintro hbor hprot
            cases mem; dsimp only at hbor hprot ⊢; subst hbor hprot; rfl
          have hm_ok :
              Miri.Interpreter.Step.evalStatement (annealStepHooks body.localDecls body.layouts) ()
                (translateStmt ⟨.assign ⟨dstIdx, .field idx₀ fty₀ :: ps⟩ (.use op), span⟩) m =
              (⟨⟨#[{ tf₁ with
                locals := tf₁.locals.set dstIdx
                  ⟨.live (.indirect (stackAllocPlace newId)),
                    some (translateTy decl.ty body.layouts)⟩ hlt₁ }]⟩,
                stackAllocMachine m.machine mem' newId alloc_final⟩, .ok ()) := by
            rw [hm_eval]; unfold Miri.Interpreter.runRvalue
            rw [EStateM.bind_eq_ok hm_op]; dsimp only; rw [hw_ok]
          have hfresh_old : m.machine.memory.live.any (fun entry => entry.1 == newId) = false := by
            rw [← hlive_eq]; exact hfresh
          have hfr_end : FrameRelLM2_2 body env
              (stackAllocMachine m.machine mem' newId alloc_final)
              { s.frame with locals := locals₁.set dstIdx (.init rootVal') }
              { tf₁ with
                locals := tf₁.locals.set dstIdx
                  ⟨.live (.indirect (stackAllocPlace newId)),
                    some (translateTy decl.ty body.layouts)⟩ hlt₁ } := by
            have hex := hfr₁_excl.of_stackAlloc_set_excl (alloc := alloc_final) (hlt := hlt₁) hres
              ⟨.live (.indirect (stackAllocPlace newId)), some (translateTy decl.ty body.layouts)⟩
            exact hex.fill_excluded hdecl hlt_loc₁
              (by dsimp only; rw [Array.size_set]; exact hlt₁)
              (by dsimp only; exact Array.getElem_set_self hlt₁)
              (.structInd fields paths rootVal' (stackAllocPlace newId) _ henv
                (fun _ hl => (Option.some.inj (Option.mem_def.mp hl)).symm) hsmpr_fin)
          rw [ha_ok,
            miri_step_at_statement_ok _ hframes hframe.body_eq hframe.location_eq hbb hstmt
              hm_ok rfl hfr_end.location_eq]
          refine ⟨.step _ _ ?_, fun s' hs' => ?_⟩
          · refine .mk _ rfl (hrc₁.trans hretCont)
              ⟨retLay, by dsimp; rw [hrp₁, hretPlace, hid₁]⟩
              hfr_end.step_pc ?_ ?_ (Or.inr (hwm_next alloc_final))
              hcal hstack hbor hprot hcaller
              (MemoryAllocDisjoint_set_fresh_stackAlloc hfr₁_excl hdisj_tf₁ hfresh_old hlt₁)
            · intro j hj
              dsimp only [fieldWritePostStaticEnv] at hj
              dsimp only [advanceStmt, get?]
              by_cases hjd : dstIdx = j
              · subst hjd; rw [List.getElem?_set_self hlt_loc₁]; nofun
              · rw [List.getElem?_set_ne hjd, ← get?_eq_getElem?]
                exact hinit₁ j hj (by nofun)
            · intro j hj mp' lay'
              dsimp only [fieldWritePostStaticEnv] at hj
              rw [List.mem_filter] at hj
              have hjd : dstIdx ≠ j := fun h => by subst h; simp at hj
              dsimp only
              rw [Array.getElem?_set_ne _ hjd]
              exact himm₁ j hj.1 (by nofun) mp' lay'
          · injection hs' with hs_eq; injection hs_eq with hs_st; subst hs_st
            exact ⟨decl, fields, paths, rootVal', stackAllocPlace newId, hdecl, henv,
              by dsimp [advanceStmt, get?]; exact List.getElem?_set_self hlt_loc₁,
              hsmpr_fin, _, some (translateTy decl.ty body.layouts), rfl,
              by dsimp only; exact Array.getElem?_set_self hlt₁⟩
        | structInd fs' ps' rootVal mp _ henv' _ hsmpr =>
          have heq_fp := henv.symm.trans henv'
          injection heq_fp with hpair; injection hpair with hfs hps; rw [← hfs, ← hps] at hsmpr
          have hfl_sz : (fields[k]'hk).fieldLayout.size = translateSizeBytes sc.sizeBytes := by
            rw [structMemPlaceRel_fieldLayout_eq hsmpr hk, hlay_sz]
          obtain ⟨rootVal', allocId, _, baseAddr, localAlloc, alloc_final, u,
              hprov, hbase, hptr, hovf_k, hu_lt, hfidx, hget_u, hw_new, hw_proj, hsmpr_fin⟩ :=
            hsmpr.write_leaf_field hk hk_p
              (fun j hj hjk => by rw [hpk_eq]; exact hdisj_paths j hj hjk)
              hrel hfl_sz hbool hchar
          have hw_ok :
              annealWriteImmediate (.scalar (.fromScalarInt msc))
                ⟨.local 0 dstIdx (some (fields[k]'hk).offset) topFrame.localsIdentity,
                  translateTy (fields[k]'hk).ty body.layouts⟩
                { m with stack := ⟨#[tf₁]⟩ } =
              .ok () ⟨⟨#[tf₁]⟩,
                updateAllocMachine m.machine u allocId localAlloc.kind alloc_final⟩ := by
            rw [annealWriteImmediate_projected_eq (tf := tf₁) rfl]
            exact annealWriteProjectedLocalImmediate_indirect_scalar_ok
              hleaf_sized rfl hlt₁ hdst_tf₁ hprov hbase hptr hovf_k hu_lt hfidx hget_u hw_new
          have ha_ok :
              evalStmt s ⟨.assign ⟨dstIdx, .field idx₀ fty₀ :: ps⟩ (.use op), span⟩
                body.localDecls body.layouts =
              MirStepNode.step (advanceStmt s (locals₁.set dstIdx (.init rootVal')) s.memory) := by
            unfold evalStmt; dsimp only
            rw [evalRvalue_use_nil_borrows _ _ _ hbor, hcaller, hev_op]; dsimp only
            rw [hdst_loc₁]; dsimp only
            have hwp : writeProjectedValue locals₁ rootVal (.field idx₀ fty₀ :: ps) (.scalar sc) =
                .ok rootVal' := by rw [← hpk_eq]; exact hw_proj locals₁
            rw [hwp]; dsimp only
            rw [set?_eq_some_set hlt_loc₁, hprot, hbor]
            dsimp only [invalidateConflictingBorrowsAtProj]
            apply congrArg (fun mem =>
              MirStepNode.step (advanceStmt s (locals₁.set dstIdx (.init rootVal')) mem))
            revert hbor hprot; generalize s.memory = mem; rintro hbor hprot
            cases mem; dsimp only at hbor hprot ⊢; subst hbor hprot; rfl
          have hm_ok :
              Miri.Interpreter.Step.evalStatement (annealStepHooks body.localDecls body.layouts) ()
                (translateStmt ⟨.assign ⟨dstIdx, .field idx₀ fty₀ :: ps⟩ (.use op), span⟩) m =
              (⟨⟨#[tf₁]⟩,
                updateAllocMachine m.machine u allocId localAlloc.kind alloc_final⟩, .ok ()) := by
            rw [hm_eval]; unfold Miri.Interpreter.runRvalue
            rw [EStateM.bind_eq_ok hm_op]; dsimp only; rw [hw_ok]
          have hfr_end : FrameRelLM2_2 body env
              (updateAllocMachine m.machine u allocId localAlloc.kind alloc_final)
              { s.frame with locals := locals₁.set dstIdx (.init rootVal') } tf₁ := by
            have hex := hfr₁_excl.of_updateAlloc_excl (kind := localAlloc.kind) (alloc' := alloc_final)
              hdisj_tf₁ hdst_tf₁ hprov hu_lt hget_u
            exact hex.fill_excluded hdecl hlt_loc₁ hlt₁ hdst_tf₁
              (.structInd fields paths rootVal' mp _ henv
                (fun _ hl => (Option.some.inj (Option.mem_def.mp hl)).symm) hsmpr_fin)
          rw [ha_ok,
            miri_step_at_statement_ok _ hframes hframe.body_eq hframe.location_eq hbb hstmt
              hm_ok rfl hfr_end.location_eq]
          refine ⟨.step _ _ ?_, fun s' hs' => ?_⟩
          · refine .mk _ rfl (hrc₁.trans hretCont)
              ⟨retLay, by dsimp; rw [hrp₁, hretPlace, hid₁]⟩
              hfr_end.step_pc ?_ ?_
              ((hsupply.mono (Nat.le_succ k_bud)).of_updateAlloc hu_lt hget_u)
              hcal hstack hbor hprot hcaller hdisj_tf₁
            · intro j hj
              dsimp only [fieldWritePostStaticEnv] at hj
              dsimp only [advanceStmt, get?]
              by_cases hjd : dstIdx = j
              · subst hjd; rw [List.getElem?_set_self hlt_loc₁]; nofun
              · rw [List.getElem?_set_ne hjd, ← get?_eq_getElem?]
                exact hinit₁ j hj (by nofun)
            · intro j hj mp' lay'
              dsimp only [fieldWritePostStaticEnv] at hj
              rw [List.mem_filter] at hj
              exact himm₁ j hj.1 (by nofun) mp' lay'
          · injection hs' with hs_eq; injection hs_eq with hs_st; subst hs_st
            exact ⟨decl, fields, paths, rootVal', mp, hdecl, henv,
              by dsimp [advanceStmt, get?]; exact List.getElem?_set_self hlt_loc₁,
              hsmpr_fin, _, some (translateTy decl.ty body.layouts), rfl,
              by dsimp only; rw [Array.getElem?_eq_getElem hlt₁, hdst_tf₁]⟩

/-- `LM-2.2` Nested Field Write Simulation: projected scalar leaf assignments
`_dst.projs = Rvalue.Use(op)` step in lockstep across `.Scalar`, `.ScalarPair`,
and `.Memory` aggregates (both unpadded and padded, including multi-step nested
`.Field` chains), materializing immediate destinations via upstream
`Miri.Interpreter.writePlaceImmediateNoValidate` (`forceAllocation`), preserving
every disjoint leaf field, and keeping every alignment padding byte `.uninit`. -/
theorem step_assign_nested_field_write_simulation
    {body : CapturedMir} {env : StructTypeEnv} {stEnv : LM2_2StaticEnv} {k_bud : Nat}
    {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_2 body env stEnv (k_bud + 1) s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx : Local} {projs : List ProjectionElem}
    {op : MirAst.Operand} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, projs⟩ (.use op), span⟩)
    (hwt : WellTypedLM2_2FieldWrite body env stEnv dstIdx projs op) :
    StepRelLM2_2 body env (fieldWritePostStaticEnv stEnv dstIdx op) k_bud m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  (step_assign_nested_field_write_simulation_core hstate hphase hbb hstmt hwt).1

/-- After any non-UB projected field write `_dst.projs = Rvalue.Use(op)`
(including `forceAllocation` on an immediate `.Scalar` or `.ScalarPair` local),
`dstIdx` is held in memory: its `lean-miri` local is `.live (.indirect mp)` in the
post-step frame, and `mp` satisfies `StructMemPlaceRel` for the new Anneal value
in the post-step machine state. -/
theorem step_assign_nested_field_write_post_structMemPlaceRel
    {body : CapturedMir} {env : StructTypeEnv} {stEnv : LM2_2StaticEnv} {k_bud : Nat}
    {s s' : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_2 body env stEnv (k_bud + 1) s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx : Local} {projs : List ProjectionElem}
    {op : MirAst.Operand} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, projs⟩ (.use op), span⟩)
    (hwt : WellTypedLM2_2FieldWrite body env stEnv dstIdx projs op)
    (hstep : stepMirFn body s = .step s') :
    ∃ decl fields paths rootVal mp,
      get? body.localDecls dstIdx = some decl ∧
      env decl.ty = some (fields, paths) ∧
      get? s'.frame.locals dstIdx = some (.init rootVal) ∧
      StructMemPlaceRel
        (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m).1.machine
        decl.ty body.layouts fields paths rootVal mp ∧
      ∃ tf lay,
        (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m).1.stack.frames =
          #[tf] ∧
        tf.locals[dstIdx]? = some ⟨.live (.indirect mp), lay⟩ :=
  (step_assign_nested_field_write_simulation_core hstate hphase hbb hstmt hwt).2 s' hstep

/-- 100% state-independent typing predicate for projected whole-sub-struct
(`ScalarPair`) writes `_dst.projs = Rvalue.Use(op)` (e.g. `_2.1 = move _3`)
into an aggregate local `_dst`, updating the two scalar leaves of the nested
sub-struct at `projs ++ [.field 0 mid₀]` and `projs ++ [.field 1 mid₁]` while
preserving every disjoint leaf field and keeping every padding byte `.uninit`. -/
inductive WellTypedLM2_2SubStructWrite
    (body : CapturedMir) (env : StructTypeEnv) (stEnv : LM2_2StaticEnv)
    (dstIdx : Local) (projs : List ProjectionElem) (op : MirAst.Operand) : Prop where
  | mk
      (decl : LocalDecl)
      (fields : List StructFieldDesc)
      (paths : List (List ProjectionElem))
      (k₀ k₁ : Nat)
      (hk₀ : k₀ < fields.length)
      (hk₁ : k₁ < fields.length)
      (hk₀_p : k₀ < paths.length)
      (hk₁_p : k₁ < paths.length)
      (subTy : Ty)
      (sf₀ sf₁ : StructFieldDesc)
      (mid₀ mid₁ : Ty)
      (a b : Miri.ABI.Scalar)
      (bOff : Miri.ABI.Size)
      (decl_lookup : get? body.localDecls dstIdx = some decl)
      (env_lookup : env decl.ty = some (fields, paths))
      (dst_init : dstIdx ∈ stEnv.initLocals)
      (ne_idx : k₀ ≠ k₁)
      (path₀_eq : paths[k₀]'hk₀_p = projs ++ [.field 0 mid₀])
      (path₁_eq : paths[k₁]'hk₁_p = projs ++ [.field 1 mid₁])
      (disj_paths : ∀ j (hj : j < paths.length), j ≠ k₀ → j ≠ k₁ →
        DisjointFieldPaths projs (paths[j]'hj))
      (proj_chain : ValidFieldProjChain body.layouts
        (translateTy decl.ty body.layouts) projs
        subTy (fields[k₀]'hk₀).offset)
      (off_k₁ : (fields[k₁]'hk₁).offset =
        Miri.ABI.Size.ofBytes ((fields[k₀]'hk₀).offset.bytes + bOff.bytes))
      (sub_sized : (translateTy subTy body.layouts).layout.isSized = true)
      (sub_repr : (translateTy subTy body.layouts).layout.backendRepr =
        .ScalarPair (a := a) (b := b) (bOffset := bOff))
      (sub_imm : IsImmediateStructTy env body.layouts subTy
        [sf₀, sf₁] [[.field 0 mid₀], [.field 1 mid₁]])
      (sf₀_ty : sf₀.ty = (fields[k₀]'hk₀).ty)
      (sf₁_ty : sf₁.ty = (fields[k₁]'hk₁).ty)
      (sf₀_fl : sf₀.fieldLayout = (fields[k₀]'hk₀).fieldLayout)
      (sf₁_fl : sf₁.fieldLayout = (fields[k₁]'hk₁).fieldLayout)
      (no_move_dst : OperandDoesNotMoveLocal dstIdx op)
      (op_wt : WellTypedLM2_2Operand body env stEnv op subTy) :
      WellTypedLM2_2SubStructWrite body env stEnv dstIdx projs op

/-- `LM-2.2` Nested Sub-Struct (`ScalarPair`) Write Simulation: projected
whole-sub-struct assignments `_dst.projs = Rvalue.Use(op)` (e.g. `_2.1 = move _3`
or `_2.1 = copy _3` where `_2.1` has `AbiRepr.ScalarPair`) step in lockstep,
writing both scalar components at `(fields[k₀]).offset` and `(fields[k₁]).offset`,
preserving all disjoint leaf fields, and keeping every inter-field and trailing
padding byte `.uninit`. -/
theorem step_assign_nested_substruct_write_simulation
    {body : CapturedMir} {env : StructTypeEnv} {stEnv : LM2_2StaticEnv} {k_bud : Nat}
    {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_2 body env stEnv k_bud s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx : Local} {projs : List ProjectionElem}
    {op : MirAst.Operand} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, projs⟩ (.use op), span⟩)
    (hwt : WellTypedLM2_2SubStructWrite body env stEnv dstIdx projs op) :
    StepRelLM2_2 body env (fieldWritePostStaticEnv stEnv dstIdx op) k_bud m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  cases hwt with
  | mk decl fields paths k₀ k₁ hk₀ hk₁ hk₀_p hk₁_p subTy sf₀ sf₁ mid₀ mid₁ a b bOff
      hdecl henv hdst_init hne_k hpath₀ hpath₁ hdisj_paths hchain hoff_k₁
      hsub_sized hsub_repr hsub_imm hsf₀_ty hsf₁_ty hsf₀_fl hsf₁_fl hno_move hop =>
    rcases hstate with
      ⟨topFrame, hframes, hretCont, ⟨retLay, hretPlace⟩, hframe,
        hinit_env, himm_env, hsupply, hcal, hstack, hbor, hprot, hcaller, hdisj⟩
    rw [stepMirFn_eq_of_not_other body s hcal hphase]
    simp only [hbb, hstmt]
    obtain ⟨idx₀, fty₀, ps, hprojs_eq⟩ : ∃ idx₀ fty₀ ps, projs = .field idx₀ fty₀ :: ps := by
      cases hpr : projs with
      | nil => exact False.elim (hchain.ne_nil hpr)
      | cons p₀ ps =>
        obtain ⟨i, t, rfl⟩ := hchain.only_fields p₀ (by rw [hpr]; exact List.mem_cons_self)
        exact ⟨i, t, ps, rfl⟩
    subst hprojs_eq
    obtain ⟨slot_dst, mls_dst0, hlt_dst0, _, hslot_dst, _, hmls_eq0, hloc_dst0⟩ :=
      hframe.lookup_local hdecl
    have hcache_dst0 : ∀ l, (topFrame.locals[dstIdx]'hlt_dst0).layout = some l →
        l = translateTy decl.ty body.layouts := by
      rw [hmls_eq0]; exact hloc_dst0.layout_eq
    have hevalPlace := annealEvalPlace_projected hframes hlt_dst0 hdecl hcache_dst0 hchain
    have hm_eval := evalStatement_assign_use_eq (op := op) (span := span) hevalPlace
      (hop.usesStructMemCopyDest_false _)
    have hfr₀_exc : FrameRelLM2_2Except body env none m.machine s.frame
        (cacheFrameLocalLayout topFrame dstIdx hlt_dst0 (translateTy decl.ty body.layouts)) :=
      FrameRelLM2_2Except.of_frameRel none (hframe.cache_local_layout hdecl hlt_dst0)
    have hdisj₀ : MemoryAllocDisjoint
        (cacheFrameLocalLayout topFrame dstIdx hlt_dst0 (translateTy decl.ty body.layouts)) :=
      MemoryAllocDisjoint_cacheFrameLocalLayout hdisj hlt_dst0 (translateTy decl.ty body.layouts)
    have himm_env₀ : ∀ j ∈ stEnv.immLocals, (none : Option Local) ≠ some j → ∀ mp l,
        (cacheFrameLocalLayout topFrame dstIdx hlt_dst0
          (translateTy decl.ty body.layouts)).locals[j]? ≠
          some ⟨.live (.indirect mp), l⟩ := by
      intro j hj _ mp l
      dsimp only [cacheFrameLocalLayout]
      by_cases hij : dstIdx = j
      · subst hij
        rw [Array.getElem?_set_self hlt_dst0, hmls_eq0]
        intro heq; injection heq with hls
        rcases mls_dst0 with ⟨val0, lay0⟩
        injection hls with hv_eq _; subst hv_eq
        exact himm_env dstIdx hj mp lay0
          (by rw [Array.getElem?_eq_getElem hlt_dst0, hmls_eq0])
      · rw [Array.getElem?_set_ne _ hij]; exact himm_env j hj mp l
    have hsim := evalLM2_2Operand_except
      (m := { m with stack := ⟨#[cacheFrameLocalLayout topFrame dstIdx hlt_dst0
          (translateTy decl.ty body.layouts)]⟩ })
      rfl hfr₀_exc (fun j hj _ => hinit_env j hj) himm_env₀ (by nofun)
      hop s.memory.globals (some (translateTy subTy body.layouts))
    generalize hev_op :
      evalOperand s.frame.locals op .nil s.memory.globals body.layouts .nil = r_a at hsim
    generalize hm_op :
      (annealEvalOperand body.localDecls body.layouts (translateOperand op)
        (some (translateTy subTy body.layouts)) >>= annealReadImmediate)
        { m with stack := ⟨#[cacheFrameLocalLayout topFrame dstIdx hlt_dst0
            (translateTy decl.ty body.layouts)]⟩ } = r_m at hsim
    cases hsim with
    | ub m_err msg =>
      have ha_ub :
          evalStmt s ⟨.assign ⟨dstIdx, .field idx₀ fty₀ :: ps⟩ (.use op), span⟩
            body.localDecls body.layouts = MirStepNode.fail .ub := by
        unfold evalStmt; dsimp only
        rw [evalRvalue_use_nil_borrows _ _ _ hbor, hcaller, hev_op]
      have hm_ub :
          Miri.Interpreter.Step.evalStatement (annealStepHooks body.localDecls body.layouts) ()
            (translateStmt ⟨.assign ⟨dstIdx, .field idx₀ fty₀ :: ps⟩ (.use op), span⟩) m =
          (m_err, .error (.undefinedBehavior msg)) := by
        rw [hm_eval]; unfold Miri.Interpreter.runRvalue; rw [EStateM.bind_eq_error hm_op]
      rw [ha_ub, miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq hbb hstmt hm_ub]
      exact .ub _ _
    | ok v locals₁ tf₁ imm _ hfr₁ hvRel _ _ hid₁ hrc₁ hrp₁ hsz₁ _ hpres_mv hinit₁ himm₁ hdisj₁ =>
      dsimp only [cacheFrameLocalLayout] at hid₁ hrc₁ hrp₁
      have hlt₁ : dstIdx < tf₁.locals.size := by
        rw [hsz₁, cacheFrameLocalLayout_size]; exact hlt_dst0
      have htf₀_dst :
          (cacheFrameLocalLayout topFrame dstIdx hlt_dst0
            (translateTy decl.ty body.layouts)).locals[dstIdx]? =
          some ⟨mls_dst0.value, some (translateTy decl.ty body.layouts)⟩ := by
        dsimp only [cacheFrameLocalLayout]
        rw [Array.getElem?_set_self hlt_dst0, hmls_eq0]
      obtain ⟨hdst_loc₁_eq, hdst_tf₁_ex⟩ := hpres_mv dstIdx hno_move
      have hdst_loc₁ : get? locals₁ dstIdx = some slot_dst := hdst_loc₁_eq.trans hslot_dst
      obtain ⟨l1, htf₁_get⟩ := hdst_tf₁_ex mls_dst0.value _ htf₀_dst
      have hl1_eq : l1 = translateTy decl.ty body.layouts :=
        (hfr₁.locals_rel dstIdx decl slot_dst ⟨mls_dst0.value, some l1⟩
          (by nofun) hdecl hdst_loc₁ htf₁_get).layout_eq l1 rfl
      subst hl1_eq
      have hdst_tf₁ : tf₁.locals[dstIdx]'hlt₁ =
          ⟨mls_dst0.value, some (translateTy decl.ty body.layouts)⟩ := by
        rw [Array.getElem?_eq_getElem hlt₁] at htf₁_get
        exact Option.some.inj htf₁_get
      obtain ⟨hlt_loc₁, _⟩ := List.getElem?_eq_some_iff.mp (get?_eq_getElem? locals₁ dstIdx ▸ hdst_loc₁)
      have hdisj_tf₁ := hdisj₁ hdisj₀
      have hfr₁_excl : FrameRelLM2_2Except body env (some dstIdx) m.machine
          { s.frame with locals := locals₁ } tf₁ :=
        ⟨hfr₁.body_eq, hfr₁.location_eq, hfr₁.af_locals_len, hfr₁.mf_locals_size,
          fun i d sl ml _ hd hs hm => hfr₁.locals_rel i d sl ml (by nofun) hd hs hm⟩
      cases hvRel with
      | primScalar _ _ henv_none _ _ =>
        have := hsub_imm.env_eq; rw [henv_none] at this; cases this
      | immStruct fs ps _ _ hsub' himm =>
        have heq_sub := hsub_imm.env_eq.symm.trans hsub'.env_eq
        injection heq_sub with hpair_s
        injection hpair_s with hfs_s hps_s; subst hfs_s hps_s
        cases himm with
        | scalarPair _ _ _ _ _ _ a' b' bOff' sc₀ sc₁ msc₀ msc₁ v₀ v₁
            _ _ _ _ hrepr' _ _ _ _ _ _ _ _ _ _ _ _ _ _ hw₀ hw₁
            hrel₀ hrel₁ hsz₀ hsz₁ hbool₀ hchar₀ hbool₁ hchar₁ =>
          cases hw₀
          cases hw₁
          cases hloc_dst0 with
          | base _ _ henv_none _ => rw [henv] at henv_none; cases henv_none
          | structUninitImm _ _ _ _ _ | structUninitInd _ _ _ _ _ _ _ =>
            exact False.elim (hinit_env dstIdx hdst_init hslot_dst)
          | structDead _ _ _ _ _ =>
            have ha_ub :
                evalStmt s ⟨.assign ⟨dstIdx, .field idx₀ fty₀ :: ps⟩ (.use op), span⟩
                  body.localDecls body.layouts = MirStepNode.fail .ub := by
              unfold evalStmt; dsimp only
              rw [evalRvalue_use_nil_borrows _ _ _ hbor, hcaller, hev_op]; dsimp only
              rw [hdst_loc₁]
            have hw_dead :
                annealWriteImmediate (.scalarPair (.fromScalarInt msc₀) (.fromScalarInt msc₁))
                  ⟨.local 0 dstIdx (some (fields[k₀]'hk₀).offset) topFrame.localsIdentity,
                    translateTy subTy body.layouts⟩
                  { m with stack := ⟨#[tf₁]⟩ } =
                .error (.undefinedBehavior "write to dead local") { m with stack := ⟨#[tf₁]⟩ } := by
              rw [annealWriteImmediate_projected_eq (tf := tf₁) rfl]
              exact annealWriteProjectedLocalImmediate_dead_ub hsub_sized rfl hlt₁ hdst_tf₁
            have hm_ub :
                Miri.Interpreter.Step.evalStatement (annealStepHooks body.localDecls body.layouts) ()
                  (translateStmt ⟨.assign ⟨dstIdx, .field idx₀ fty₀ :: ps⟩ (.use op), span⟩) m =
                ({ m with stack := ⟨#[tf₁]⟩ }, .error (.undefinedBehavior "write to dead local")) := by
              rw [hm_eval]; unfold Miri.Interpreter.runRvalue
              rw [EStateM.bind_eq_ok hm_op]; dsimp only; rw [hw_dead]
            rw [ha_ub, miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq hbb hstmt hm_ub]
            exact .ub _ _
          | structImm fs' ps' rootVal oldImm _ henv' _ himm_old =>
            rw [henv] at henv'
            simp only [Option.some.injEq, Prod.mk.injEq] at henv'
            rcases henv' with ⟨rfl, rfl⟩
            cases himm_old with
            | scalarWrapper =>
              simp at hk₀ hk₁; omega
            | scalarPair _ _ m₀ m₁ z₀ z₁ =>
              simp at hk₀ hk₁
              have hk01 : (k₀ = 0 ∧ k₁ = 1) ∨ (k₀ = 1 ∧ k₁ = 0) := by omega
              rcases hk01 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · dsimp [List.append] at hpath₀ hpath₁
                injection hpath₀ with hh0 _
                injection hpath₁ with hh1 _
                rw [← hh0] at hh1; cases hh1
              · dsimp [List.append] at hpath₀ hpath₁
                injection hpath₀ with hh0 _
                injection hpath₁ with hh1 _
                rw [← hh0] at hh1; cases hh1
          | structInd fs' ps' rootVal mp _ henv' _ hsmpr =>
            have heq_fp := henv.symm.trans henv'
            injection heq_fp with hpair; injection hpair with hfs hps; rw [← hfs, ← hps] at hsmpr
            have hfl_sz₀ : (fields[k₀]'hk₀).fieldLayout.size = translateSizeBytes sc₀.sizeBytes := by
              rw [← hsf₀_fl, hsz₀]
            have hfl_sz₁ : (fields[k₁]'hk₁).fieldLayout.size = translateSizeBytes sc₁.sizeBytes := by
              rw [← hsf₁_fl, hsz₁]
            obtain ⟨_, hlast_p⟩ := hchain.last_eq
            obtain ⟨rootVal', allocId, _, baseAddr, localAlloc, alloc₁, alloc₂, u,
                hprov, hbase, hptr, hovf_k₀, hu_lt, hfidx, hget_u,
                hw₀_new, hw₁_new, hw_proj, hsmpr_fin⟩ :=
              hsmpr.write_substruct_scalarPair hk₀ hk₁ hk₀_p hk₁_p hne_k (by nofun)
                hlast_p hrepr' hpath₀ hpath₁ hdisj_paths hrel₀ hrel₁ hfl_sz₀ hfl_sz₁
                (hsf₀_ty ▸ hbool₀) (hsf₀_ty ▸ hchar₀)
                (hsf₁_ty ▸ hbool₁) (hsf₁_ty ▸ hchar₁)
            have hw₁_new' :
                Miri.Memory.Allocation.writeScalar annealTargetDataLayout
                  (Miri.Memory.allocRange
                    (Miri.ABI.Size.ofBytes ((fields[k₀]'hk₀).offset.bytes + bOff.bytes))
                    (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) msc₁).size)
                  (.fromScalarInt msc₁) alloc₁ = .ok () alloc₂ := by
              rw [← hoff_k₁]; exact hw₁_new
            have hw_ok :
                annealWriteImmediate (.scalarPair (.fromScalarInt msc₀) (.fromScalarInt msc₁))
                  ⟨.local 0 dstIdx (some (fields[k₀]'hk₀).offset) topFrame.localsIdentity,
                    translateTy subTy body.layouts⟩
                  { m with stack := ⟨#[tf₁]⟩ } =
                .ok () ⟨⟨#[tf₁]⟩,
                  updateAllocMachine m.machine u allocId localAlloc.kind alloc₂⟩ := by
              rw [annealWriteImmediate_projected_eq (tf := tf₁) rfl]
              exact annealWriteProjectedLocalImmediate_indirect_scalarPair_ok
                hsub_sized hsub_repr rfl hlt₁ hdst_tf₁ hprov hbase hptr hovf_k₀
                hu_lt hfidx hget_u hw₀_new hw₁_new'
            have ha_ok :
                evalStmt s ⟨.assign ⟨dstIdx, .field idx₀ fty₀ :: ps⟩ (.use op), span⟩
                  body.localDecls body.layouts =
                MirStepNode.step (advanceStmt s (locals₁.set dstIdx (.init rootVal')) s.memory) := by
              unfold evalStmt; dsimp only
              rw [evalRvalue_use_nil_borrows _ _ _ hbor, hcaller, hev_op]; dsimp only
              rw [hdst_loc₁]; dsimp only
              rw [hw_proj locals₁]; dsimp only
              rw [set?_eq_some_set hlt_loc₁, hprot, hbor]
              dsimp only [invalidateConflictingBorrowsAtProj]
              apply congrArg (fun mem =>
                MirStepNode.step (advanceStmt s (locals₁.set dstIdx (.init rootVal')) mem))
              revert hbor hprot; generalize s.memory = mem; rintro hbor hprot
              cases mem; dsimp only at hbor hprot ⊢; subst hbor hprot; rfl
            have hm_ok :
                Miri.Interpreter.Step.evalStatement (annealStepHooks body.localDecls body.layouts) ()
                  (translateStmt ⟨.assign ⟨dstIdx, .field idx₀ fty₀ :: ps⟩ (.use op), span⟩) m =
                (⟨⟨#[tf₁]⟩,
                  updateAllocMachine m.machine u allocId localAlloc.kind alloc₂⟩, .ok ()) := by
              rw [hm_eval]; unfold Miri.Interpreter.runRvalue
              rw [EStateM.bind_eq_ok hm_op]; dsimp only; rw [hw_ok]
            have hfr_end : FrameRelLM2_2 body env
                (updateAllocMachine m.machine u allocId localAlloc.kind alloc₂)
                { s.frame with locals := locals₁.set dstIdx (.init rootVal') } tf₁ := by
              have hex := hfr₁_excl.of_updateAlloc_excl (kind := localAlloc.kind) (alloc' := alloc₂)
                hdisj_tf₁ hdst_tf₁ hprov hu_lt hget_u
              exact hex.fill_excluded hdecl hlt_loc₁ hlt₁ hdst_tf₁
                (.structInd fields paths rootVal' mp _ henv
                  (fun _ hl => (Option.some.inj (Option.mem_def.mp hl)).symm) hsmpr_fin)
            rw [ha_ok,
              miri_step_at_statement_ok _ hframes hframe.body_eq hframe.location_eq hbb hstmt
                hm_ok rfl hfr_end.location_eq]
            refine .step _ _ ?_
            refine .mk _ rfl (hrc₁.trans hretCont)
              ⟨retLay, by dsimp; rw [hrp₁, hretPlace, hid₁]⟩
              hfr_end.step_pc ?_ ?_
              (hsupply.of_updateAlloc hu_lt hget_u)
              hcal hstack hbor hprot hcaller hdisj_tf₁
            · intro j hj
              dsimp only [fieldWritePostStaticEnv] at hj
              dsimp only [advanceStmt, get?]
              by_cases hjd : dstIdx = j
              · subst hjd; rw [List.getElem?_set_self hlt_loc₁]; nofun
              · rw [List.getElem?_set_ne hjd, ← get?_eq_getElem?]
                exact hinit₁ j hj (by nofun)
            · intro j hj mp' lay'
              dsimp only [fieldWritePostStaticEnv] at hj
              rw [List.mem_filter] at hj
              exact himm₁ j hj.1 (by nofun) mp' lay'

/-- 100% syntactic (state-independent) typing predicate for a projected
whole-sub-struct write `_dst.projs = Rvalue.Use(op)` where `_dst.projs : subTy`
is a 1-field `.Scalar` wrapper sub-struct (e.g. `_1.1 = move _2` or
`_1.1 = copy _2` with `_1.1 : InnerU32`), backed by leaf `k₀` at
`projs ++ [.field 0 mid₀]`. -/
inductive WellTypedLM2_2ScalarWrapWrite
    (body : CapturedMir)
    (env : StructTypeEnv)
    (stEnv : LM2_2StaticEnv)
    (dstIdx : Local)
    (projs : List ProjectionElem)
    (op : MirAst.Operand) : Prop where
  | mk
      (decl : LocalDecl)
      (fields : List StructFieldDesc)
      (paths : List (List ProjectionElem))
      (k₀ : Nat)
      (hk₀ : k₀ < fields.length)
      (hk₀_p : k₀ < paths.length)
      (subTy : Ty)
      (sf₀ : StructFieldDesc)
      (mid₀ : Ty)
      (a : Miri.ABI.Scalar)
      (decl_lookup : get? body.localDecls dstIdx = some decl)
      (env_lookup : env decl.ty = some (fields, paths))
      (dst_init : dstIdx ∈ stEnv.initLocals)
      (dst_sized : (translateTy decl.ty body.layouts).layout.isSized = true)
      (dst_align : (translateTy decl.ty body.layouts).layout.align.abi.pow2 ≤ 29)
      (path₀_eq : paths[k₀]'hk₀_p = projs ++ [.field 0 mid₀])
      (disj_paths : ∀ j (hj : j < paths.length), j ≠ k₀ →
        DisjointFieldPaths projs (paths[j]'hj))
      (proj_chain : ValidFieldProjChain body.layouts
        (translateTy decl.ty body.layouts) projs
        subTy (fields[k₀]'hk₀).offset)
      (sub_sized : (translateTy subTy body.layouts).layout.isSized = true)
      (sub_repr : (translateTy subTy body.layouts).layout.backendRepr = .Scalar a)
      (sub_imm : IsImmediateStructTy env body.layouts subTy
        [sf₀] [[.field 0 mid₀]])
      (sf₀_ty : sf₀.ty = (fields[k₀]'hk₀).ty)
      (sf₀_fl : sf₀.fieldLayout = (fields[k₀]'hk₀).fieldLayout)
      (no_move_dst : OperandDoesNotMoveLocal dstIdx op)
      (op_wt : WellTypedLM2_2Operand body env stEnv op subTy) :
      WellTypedLM2_2ScalarWrapWrite body env stEnv dstIdx projs op

/-- `LM-2.2` Nested `.Scalar` Wrapper Sub-Struct Write Simulation: projected
whole-sub-struct assignments `_dst.projs = Rvalue.Use(op)` (e.g. `_1.1 = move _2`
or `_1.1 = copy _2` where `_1.1` has `AbiRepr.Scalar`, such as `InnerU32`) step
in lockstep across both immediate (`.Scalar`/`.ScalarPair`) and memory-backed
(`.Memory`) outer aggregates, writing the wrapped scalar at `(fields[k₀]).offset`,
preserving all disjoint leaf fields, and keeping every alignment padding byte
`.uninit`. -/
theorem step_assign_nested_scalar_wrap_write_simulation
    {body : CapturedMir} {env : StructTypeEnv} {stEnv : LM2_2StaticEnv} {k_bud : Nat}
    {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_2 body env stEnv (k_bud + 1) s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx : Local} {projs : List ProjectionElem}
    {op : MirAst.Operand} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, projs⟩ (.use op), span⟩)
    (hwt : WellTypedLM2_2ScalarWrapWrite body env stEnv dstIdx projs op) :
    StepRelLM2_2 body env (fieldWritePostStaticEnv stEnv dstIdx op) k_bud m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  cases hwt with
  | mk decl fields paths k₀ hk₀ hk₀_p subTy sf₀ mid₀ a
      hdecl henv hdst_init hdst_sized hdst_align hpath₀ hdisj_paths hchain
      hsub_sized hsub_repr hsub_imm hsf₀_ty hsf₀_fl hno_move hop =>
    rcases hstate with
      ⟨topFrame, hframes, hretCont, ⟨retLay, hretPlace⟩, hframe,
        hinit_env, himm_env, hsupply, hcal, hstack, hbor, hprot, hcaller, hdisj⟩
    rw [stepMirFn_eq_of_not_other body s hcal hphase]
    simp only [hbb, hstmt]
    obtain ⟨subIdx, hlast_p⟩ := hchain.last_eq
    obtain ⟨idx₀, fty₀, ps, hprojs_eq⟩ : ∃ idx₀ fty₀ ps, projs = .field idx₀ fty₀ :: ps := by
      cases hpr : projs with
      | nil => exact False.elim (hchain.ne_nil hpr)
      | cons p₀ ps =>
        obtain ⟨i, t, rfl⟩ := hchain.only_fields p₀ (by rw [hpr]; exact List.mem_cons_self)
        exact ⟨i, t, ps, rfl⟩
    subst hprojs_eq
    obtain ⟨slot_dst, mls_dst0, hlt_dst0, _, hslot_dst, _, hmls_eq0, hloc_dst0⟩ :=
      hframe.lookup_local hdecl
    have hcache_dst0 : ∀ l, (topFrame.locals[dstIdx]'hlt_dst0).layout = some l →
        l = translateTy decl.ty body.layouts := by
      rw [hmls_eq0]; exact hloc_dst0.layout_eq
    have hevalPlace := annealEvalPlace_projected hframes hlt_dst0 hdecl hcache_dst0 hchain
    have hm_eval := evalStatement_assign_use_eq (op := op) (span := span) hevalPlace
      (hop.usesStructMemCopyDest_false _)
    have hfr₀_exc : FrameRelLM2_2Except body env none m.machine s.frame
        (cacheFrameLocalLayout topFrame dstIdx hlt_dst0 (translateTy decl.ty body.layouts)) :=
      FrameRelLM2_2Except.of_frameRel none (hframe.cache_local_layout hdecl hlt_dst0)
    have hdisj₀ : MemoryAllocDisjoint
        (cacheFrameLocalLayout topFrame dstIdx hlt_dst0 (translateTy decl.ty body.layouts)) :=
      MemoryAllocDisjoint_cacheFrameLocalLayout hdisj hlt_dst0 (translateTy decl.ty body.layouts)
    have himm_env₀ : ∀ j ∈ stEnv.immLocals, (none : Option Local) ≠ some j → ∀ mp l,
        (cacheFrameLocalLayout topFrame dstIdx hlt_dst0
          (translateTy decl.ty body.layouts)).locals[j]? ≠
          some ⟨.live (.indirect mp), l⟩ := by
      intro j hj _ mp l
      dsimp only [cacheFrameLocalLayout]
      by_cases hij : dstIdx = j
      · subst hij
        rw [Array.getElem?_set_self hlt_dst0, hmls_eq0]
        intro heq; injection heq with hls
        rcases mls_dst0 with ⟨val0, lay0⟩
        injection hls with hv_eq _; subst hv_eq
        exact himm_env dstIdx hj mp lay0
          (by rw [Array.getElem?_eq_getElem hlt_dst0, hmls_eq0])
      · rw [Array.getElem?_set_ne _ hij]; exact himm_env j hj mp l
    have hsim := evalLM2_2Operand_except
      (m := { m with stack := ⟨#[cacheFrameLocalLayout topFrame dstIdx hlt_dst0
          (translateTy decl.ty body.layouts)]⟩ })
      rfl hfr₀_exc (fun j hj _ => hinit_env j hj) himm_env₀ (by nofun)
      hop s.memory.globals (some (translateTy subTy body.layouts))
    generalize hev_op :
      evalOperand s.frame.locals op .nil s.memory.globals body.layouts .nil = r_a at hsim
    generalize hm_op :
      (annealEvalOperand body.localDecls body.layouts (translateOperand op)
        (some (translateTy subTy body.layouts)) >>= annealReadImmediate)
        { m with stack := ⟨#[cacheFrameLocalLayout topFrame dstIdx hlt_dst0
            (translateTy decl.ty body.layouts)]⟩ } = r_m at hsim
    cases hsim with
    | ub m_err msg =>
      have ha_ub :
          evalStmt s ⟨.assign ⟨dstIdx, .field idx₀ fty₀ :: ps⟩ (.use op), span⟩
            body.localDecls body.layouts = MirStepNode.fail .ub := by
        unfold evalStmt; dsimp only
        rw [evalRvalue_use_nil_borrows _ _ _ hbor, hcaller, hev_op]
      have hm_ub :
          Miri.Interpreter.Step.evalStatement (annealStepHooks body.localDecls body.layouts) ()
            (translateStmt ⟨.assign ⟨dstIdx, .field idx₀ fty₀ :: ps⟩ (.use op), span⟩) m =
          (m_err, .error (.undefinedBehavior msg)) := by
        rw [hm_eval]; unfold Miri.Interpreter.runRvalue; rw [EStateM.bind_eq_error hm_op]
      rw [ha_ub, miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq hbb hstmt hm_ub]
      exact .ub _ _
    | ok v locals₁ tf₁ imm _ hfr₁ hvRel _ _ hid₁ hrc₁ hrp₁ hsz₁ _ hpres_mv hinit₁ himm₁ hdisj₁ =>
      dsimp only [cacheFrameLocalLayout] at hid₁ hrc₁ hrp₁
      have hlt₁ : dstIdx < tf₁.locals.size := by
        rw [hsz₁, cacheFrameLocalLayout_size]; exact hlt_dst0
      have htf₀_dst :
          (cacheFrameLocalLayout topFrame dstIdx hlt_dst0
            (translateTy decl.ty body.layouts)).locals[dstIdx]? =
          some ⟨mls_dst0.value, some (translateTy decl.ty body.layouts)⟩ := by
        dsimp only [cacheFrameLocalLayout]
        rw [Array.getElem?_set_self hlt_dst0, hmls_eq0]
      obtain ⟨hdst_loc₁_eq, hdst_tf₁_ex⟩ := hpres_mv dstIdx hno_move
      have hdst_loc₁ : get? locals₁ dstIdx = some slot_dst := hdst_loc₁_eq.trans hslot_dst
      obtain ⟨l1, htf₁_get⟩ := hdst_tf₁_ex mls_dst0.value _ htf₀_dst
      have hl1_eq : l1 = translateTy decl.ty body.layouts :=
        (hfr₁.locals_rel dstIdx decl slot_dst ⟨mls_dst0.value, some l1⟩
          (by nofun) hdecl hdst_loc₁ htf₁_get).layout_eq l1 rfl
      subst hl1_eq
      have hdst_tf₁ : tf₁.locals[dstIdx]'hlt₁ =
          ⟨mls_dst0.value, some (translateTy decl.ty body.layouts)⟩ := by
        rw [Array.getElem?_eq_getElem hlt₁] at htf₁_get
        exact Option.some.inj htf₁_get
      obtain ⟨hlt_loc₁, _⟩ := List.getElem?_eq_some_iff.mp (get?_eq_getElem? locals₁ dstIdx ▸ hdst_loc₁)
      have hdisj_tf₁ := hdisj₁ hdisj₀
      have hfr₁_excl : FrameRelLM2_2Except body env (some dstIdx) m.machine
          { s.frame with locals := locals₁ } tf₁ :=
        ⟨hfr₁.body_eq, hfr₁.location_eq, hfr₁.af_locals_len, hfr₁.mf_locals_size,
          fun i d sl ml _ hd hs hm => hfr₁.locals_rel i d sl ml (by nofun) hd hs hm⟩
      cases hvRel with
      | primScalar _ _ henv_none _ _ =>
        have := hsub_imm.env_eq; rw [henv_none] at this; cases this
      | immStruct fs ps _ _ hsub' himm =>
        have heq_sub := hsub_imm.env_eq.symm.trans hsub'.env_eq
        injection heq_sub with hpair_s
        injection hpair_s with hfs_s hps_s; subst hfs_s hps_s
        cases himm with
        | scalarWrapper _ _ _ sc₀ msc₀ _ _ _ _ _ _ _ _ hw₀ hrel₀ hsz₀ hbool₀ hchar₀ =>
          cases hw₀ with
          | wrap_cons _ _ _ hw_sub =>
            cases hw_sub
            have hfl_sz₀ : (fields[k₀]'hk₀).fieldLayout.size = translateSizeBytes sc₀.sizeBytes := by
              rw [← hsf₀_fl, hsz₀]
            cases hloc_dst0 with
            | base _ _ henv_none _ => rw [henv] at henv_none; cases henv_none
            | structUninitImm _ _ _ _ _ | structUninitInd _ _ _ _ _ _ _ =>
              exact False.elim (hinit_env dstIdx hdst_init hslot_dst)
            | structDead _ _ _ _ _ =>
              have ha_ub :
                  evalStmt s ⟨.assign ⟨dstIdx, .field idx₀ fty₀ :: ps⟩ (.use op), span⟩
                    body.localDecls body.layouts = MirStepNode.fail .ub := by
                unfold evalStmt; dsimp only
                rw [evalRvalue_use_nil_borrows _ _ _ hbor, hcaller, hev_op]; dsimp only
                rw [hdst_loc₁]
              have hw_dead :
                  annealWriteImmediate (.scalar (.fromScalarInt msc₀))
                    ⟨.local 0 dstIdx (some (fields[k₀]'hk₀).offset) topFrame.localsIdentity,
                      translateTy subTy body.layouts⟩
                    { m with stack := ⟨#[tf₁]⟩ } =
                  .error (.undefinedBehavior "write to dead local") { m with stack := ⟨#[tf₁]⟩ } := by
                rw [annealWriteImmediate_projected_eq (tf := tf₁) rfl]
                exact annealWriteProjectedLocalImmediate_dead_ub hsub_sized rfl hlt₁ hdst_tf₁
              have hm_ub :
                  Miri.Interpreter.Step.evalStatement (annealStepHooks body.localDecls body.layouts) ()
                    (translateStmt ⟨.assign ⟨dstIdx, .field idx₀ fty₀ :: ps⟩ (.use op), span⟩) m =
                  ({ m with stack := ⟨#[tf₁]⟩ }, .error (.undefinedBehavior "write to dead local")) := by
                rw [hm_eval]; unfold Miri.Interpreter.runRvalue
                rw [EStateM.bind_eq_ok hm_op]; dsimp only; rw [hw_dead]
              rw [ha_ub, miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq hbb hstmt hm_ub]
              exact .ub _ _
            | structImm fs' ps' rootVal oldImm _ henv' _ himm_old =>
              have heq_fp := henv.symm.trans henv'
              injection heq_fp with hpair; injection hpair with hfs hps; rw [← hfs, ← hps] at himm_old
              have hne_uninit : oldImm ≠ .uninit := by cases himm_old <;> nofun
              obtain ⟨rawAlloc, mem', newId, alloc_init, htry, hres, hlive_eq, hfresh,
                  hwm_next, hovf_all, hw_old, hsmpr_init⟩ :=
                StructMemPlaceRel.of_immediate (m := { m with stack := ⟨#[tf₁]⟩ })
                  himm_old hdst_align (hsupply.of_succ)
              obtain ⟨rootVal', allocId_w, _, _, la_w, alloc_final, u_w,
                  hprov_w, _, _, _, hu_lt_w, hfidx_w, hget_w, hw_new, hw_proj, hsmpr_fin⟩ :=
                hsmpr_init.write_substruct_scalarWrap hk₀ hk₀_p (by nofun) hlast_p hsub_repr
                  hpath₀ hdisj_paths hrel₀ hfl_sz₀ (hsf₀_ty ▸ hbool₀) (hsf₀_ty ▸ hchar₀)
              have hid_w : allocId_w = newId := by
                dsimp only [stackAllocPlace] at hprov_w
                injection hprov_w with h1; injection h1 with h2 _; exact h2.symm
              cases hid_w
              have hu_eq : u_w = mem'.live.size := by
                obtain ⟨_, u_s, hu_s_lt, hfidx_self, hget_s⟩ :=
                  LiveAllocEntry.of_push_fresh_self (la := ⟨.stack, alloc_init⟩) hfresh
                have hu_w_eq : u_w = u_s := Option.some.inj (hfidx_w.symm.trans hfidx_self)
                subst hu_w_eq
                apply Classical.byContradiction
                intro hne_sz
                have hlt_old : u_w < mem'.live.size := by
                  rw [Array.size_push] at hu_s_lt; omega
                rw [Array.getElem_push_lt hlt_old] at hget_s
                have hmem_any : mem'.live.any (fun entry => entry.1 == newId) = true := by
                  rw [Array.any_eq_true]
                  exact ⟨u_w, hlt_old, by rw [hget_s]; simp⟩
                rw [hfresh] at hmem_any; cases hmem_any
              subst hu_eq
              have hla_w : la_w = ⟨.stack, alloc_init⟩ := by
                have hget_self : (mem'.live.push (newId, ⟨.stack, alloc_init⟩))[mem'.live.size]'hu_lt_w =
                    (newId, ⟨.stack, alloc_init⟩) := Array.getElem_push_eq
                exact (Prod.mk.inj (hget_w.symm.trans hget_self)).2
              subst hla_w
              rw [updateAllocMachine_stackAllocMachine_self] at hsmpr_fin
              have hoff_lt32 : (fields[k₀]'hk₀).offset.bytes.toNat < 2 ^ 32 := by
                have hbnd_k := hchain.bounds
                cases himm_old with
                | scalarWrapper f₀ _ _ _ _ _ _ _ _ _ hf₀_off _ _ _ _ _ _ _ =>
                  simp at hk₀; subst hk₀; dsimp; rw [hf₀_off]; decide
                | scalarPair _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hsz4g =>
                  omega
              have hw_ok :
                  annealWriteImmediate (.scalar (.fromScalarInt msc₀))
                    ⟨.local 0 dstIdx (some (fields[k₀]'hk₀).offset) topFrame.localsIdentity,
                      translateTy subTy body.layouts⟩
                    { m with stack := ⟨#[tf₁]⟩ } =
                  .ok () ⟨⟨#[{ tf₁ with
                    locals := tf₁.locals.set dstIdx
                      ⟨.live (.indirect (stackAllocPlace newId)),
                        some (translateTy decl.ty body.layouts)⟩ hlt₁ }]⟩,
                    stackAllocMachine m.machine mem' newId alloc_final⟩ := by
                rw [annealWriteImmediate_projected_eq (tf := tf₁) rfl]
                cases oldImm with
                | uninit => exact absurd rfl hne_uninit
                | scalar _ | scalarPair _ _ =>
                  exact annealWriteProjectedLocalImmediate_immediate_scalar_ok
                    (alloc_init := alloc_init) hsub_sized hdst_sized rfl hlt₁ hdst_tf₁
                    htry hres hfresh hw_old (hovf_all _ hoff_lt32) hw_new
              have ha_ok :
                  evalStmt s ⟨.assign ⟨dstIdx, .field idx₀ fty₀ :: ps⟩ (.use op), span⟩
                    body.localDecls body.layouts =
                  MirStepNode.step (advanceStmt s (locals₁.set dstIdx (.init rootVal')) s.memory) := by
                unfold evalStmt; dsimp only
                rw [evalRvalue_use_nil_borrows _ _ _ hbor, hcaller, hev_op]; dsimp only
                rw [hdst_loc₁]; dsimp only
                rw [hw_proj locals₁]; dsimp only
                rw [set?_eq_some_set hlt_loc₁, hprot, hbor]
                dsimp only [invalidateConflictingBorrowsAtProj]
                apply congrArg (fun mem =>
                  MirStepNode.step (advanceStmt s (locals₁.set dstIdx (.init rootVal')) mem))
                revert hbor hprot; generalize s.memory = mem; rintro hbor hprot
                cases mem; dsimp only at hbor hprot ⊢; subst hbor hprot; rfl
              have hm_ok :
                  Miri.Interpreter.Step.evalStatement (annealStepHooks body.localDecls body.layouts) ()
                    (translateStmt ⟨.assign ⟨dstIdx, .field idx₀ fty₀ :: ps⟩ (.use op), span⟩) m =
                  (⟨⟨#[{ tf₁ with
                    locals := tf₁.locals.set dstIdx
                      ⟨.live (.indirect (stackAllocPlace newId)),
                        some (translateTy decl.ty body.layouts)⟩ hlt₁ }]⟩,
                    stackAllocMachine m.machine mem' newId alloc_final⟩, .ok ()) := by
                rw [hm_eval]; unfold Miri.Interpreter.runRvalue
                rw [EStateM.bind_eq_ok hm_op]; dsimp only; rw [hw_ok]
              have hfresh_old : m.machine.memory.live.any (fun entry => entry.1 == newId) = false := by
                rw [← hlive_eq]; exact hfresh
              have hfr_end : FrameRelLM2_2 body env
                  (stackAllocMachine m.machine mem' newId alloc_final)
                  { s.frame with locals := locals₁.set dstIdx (.init rootVal') }
                  { tf₁ with
                    locals := tf₁.locals.set dstIdx
                      ⟨.live (.indirect (stackAllocPlace newId)),
                        some (translateTy decl.ty body.layouts)⟩ hlt₁ } := by
                have hex := hfr₁_excl.of_stackAlloc_set_excl (alloc := alloc_final) (hlt := hlt₁) hres
                  ⟨.live (.indirect (stackAllocPlace newId)), some (translateTy decl.ty body.layouts)⟩
                exact hex.fill_excluded hdecl hlt_loc₁
                  (by dsimp only; rw [Array.size_set]; exact hlt₁)
                  (by dsimp only; exact Array.getElem_set_self hlt₁)
                  (.structInd fields paths rootVal' (stackAllocPlace newId) _ henv
                    (fun _ hl => (Option.some.inj (Option.mem_def.mp hl)).symm) hsmpr_fin)
              rw [ha_ok,
                miri_step_at_statement_ok _ hframes hframe.body_eq hframe.location_eq hbb hstmt
                  hm_ok rfl hfr_end.location_eq]
              refine .step _ _ ?_
              refine .mk _ rfl (hrc₁.trans hretCont)
                ⟨retLay, by dsimp; rw [hrp₁, hretPlace, hid₁]⟩
                hfr_end.step_pc ?_ ?_ (Or.inr (hwm_next alloc_final))
                hcal hstack hbor hprot hcaller
                (MemoryAllocDisjoint_set_fresh_stackAlloc hfr₁_excl hdisj_tf₁ hfresh_old hlt₁)
              · intro j hj
                dsimp only [fieldWritePostStaticEnv] at hj
                dsimp only [advanceStmt, get?]
                by_cases hjd : dstIdx = j
                · subst hjd; rw [List.getElem?_set_self hlt_loc₁]; nofun
                · rw [List.getElem?_set_ne hjd, ← get?_eq_getElem?]
                  exact hinit₁ j hj (by nofun)
              · intro j hj mp' lay'
                dsimp only [fieldWritePostStaticEnv] at hj
                rw [List.mem_filter] at hj
                have hjd : dstIdx ≠ j := fun h => by subst h; simp at hj
                dsimp only
                rw [Array.getElem?_set_ne _ hjd]
                exact himm₁ j hj.1 (by nofun) mp' lay'
            | structInd fs' ps' rootVal mp _ henv' _ hsmpr =>
              have heq_fp := henv.symm.trans henv'
              injection heq_fp with hpair; injection hpair with hfs hps; rw [← hfs, ← hps] at hsmpr
              obtain ⟨rootVal', allocId, _, baseAddr, localAlloc, alloc', u,
                  hprov, hbase, hptr, hovf_k₀, hu_lt, hfidx, hget_u,
                  hw₀_new, hw_proj, hsmpr_fin⟩ :=
                hsmpr.write_substruct_scalarWrap hk₀ hk₀_p (by nofun) hlast_p hsub_repr
                  hpath₀ hdisj_paths hrel₀ hfl_sz₀ (hsf₀_ty ▸ hbool₀) (hsf₀_ty ▸ hchar₀)
              have hw_ok :
                  annealWriteImmediate (.scalar (.fromScalarInt msc₀))
                    ⟨.local 0 dstIdx (some (fields[k₀]'hk₀).offset) topFrame.localsIdentity,
                      translateTy subTy body.layouts⟩
                    { m with stack := ⟨#[tf₁]⟩ } =
                  .ok () ⟨⟨#[tf₁]⟩,
                    updateAllocMachine m.machine u allocId localAlloc.kind alloc'⟩ := by
                rw [annealWriteImmediate_projected_eq (tf := tf₁) rfl]
                exact annealWriteProjectedLocalImmediate_indirect_scalar_ok
                  hsub_sized rfl hlt₁ hdst_tf₁ hprov hbase hptr hovf_k₀ hu_lt hfidx hget_u hw₀_new
              have ha_ok :
                  evalStmt s ⟨.assign ⟨dstIdx, .field idx₀ fty₀ :: ps⟩ (.use op), span⟩
                    body.localDecls body.layouts =
                  MirStepNode.step (advanceStmt s (locals₁.set dstIdx (.init rootVal')) s.memory) := by
                unfold evalStmt; dsimp only
                rw [evalRvalue_use_nil_borrows _ _ _ hbor, hcaller, hev_op]; dsimp only
                rw [hdst_loc₁]; dsimp only
                rw [hw_proj locals₁]; dsimp only
                rw [set?_eq_some_set hlt_loc₁, hprot, hbor]
                dsimp only [invalidateConflictingBorrowsAtProj]
                apply congrArg (fun mem =>
                  MirStepNode.step (advanceStmt s (locals₁.set dstIdx (.init rootVal')) mem))
                revert hbor hprot; generalize s.memory = mem; rintro hbor hprot
                cases mem; dsimp only at hbor hprot ⊢; subst hbor hprot; rfl
              have hm_ok :
                  Miri.Interpreter.Step.evalStatement (annealStepHooks body.localDecls body.layouts) ()
                    (translateStmt ⟨.assign ⟨dstIdx, .field idx₀ fty₀ :: ps⟩ (.use op), span⟩) m =
                  (⟨⟨#[tf₁]⟩,
                    updateAllocMachine m.machine u allocId localAlloc.kind alloc'⟩, .ok ()) := by
                rw [hm_eval]; unfold Miri.Interpreter.runRvalue
                rw [EStateM.bind_eq_ok hm_op]; dsimp only; rw [hw_ok]
              have hfr_end : FrameRelLM2_2 body env
                  (updateAllocMachine m.machine u allocId localAlloc.kind alloc')
                  { s.frame with locals := locals₁.set dstIdx (.init rootVal') } tf₁ := by
                have hex := hfr₁_excl.of_updateAlloc_excl (kind := localAlloc.kind) (alloc' := alloc')
                  hdisj_tf₁ hdst_tf₁ hprov hu_lt hget_u
                exact hex.fill_excluded hdecl hlt_loc₁ hlt₁ hdst_tf₁
                  (.structInd fields paths rootVal' mp _ henv
                    (fun _ hl => (Option.some.inj (Option.mem_def.mp hl)).symm) hsmpr_fin)
              rw [ha_ok,
                miri_step_at_statement_ok _ hframes hframe.body_eq hframe.location_eq hbb hstmt
                  hm_ok rfl hfr_end.location_eq]
              refine .step _ _ ?_
              refine .mk _ rfl (hrc₁.trans hretCont)
                ⟨retLay, by dsimp; rw [hrp₁, hretPlace, hid₁]⟩
                hfr_end.step_pc ?_ ?_
                ((hsupply.mono (Nat.le_succ k_bud)).of_updateAlloc hu_lt hget_u)
                hcal hstack hbor hprot hcaller hdisj_tf₁
              · intro j hj
                dsimp only [fieldWritePostStaticEnv] at hj
                dsimp only [advanceStmt, get?]
                by_cases hjd : dstIdx = j
                · subst hjd; rw [List.getElem?_set_self hlt_loc₁]; nofun
                · rw [List.getElem?_set_ne hjd, ← get?_eq_getElem?]
                  exact hinit₁ j hj (by nofun)
              · intro j hj mp' lay'
                dsimp only [fieldWritePostStaticEnv] at hj
                rw [List.mem_filter] at hj
                exact himm₁ j hj.1 (by nofun) mp' lay'


/-! ## 6. Storage Operations, Unprojected `Use`, & Statement Composition (`WellTypedLM2_2Stmt`) -/

theorem FrameRelLM2_2.update_local_dealloc
    {body : CapturedMir} {env : StructTypeEnv} {mach : AnnealMachine}
    {af : StackFrame}
    {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hrel : FrameRelLM2_2 body env mach af mf)
    (hdisj : MemoryAllocDisjoint mf)
    {idx : Nat} {decl : LocalDecl}
    (hdecl : get? body.localDecls idx = some decl)
    {hlt_mf : idx < mf.locals.size}
    (newSlot : LocalSlot) (newVal : Miri.Interpreter.LocalValue AnnealProv)
    (hnew : LocalRelLM2_2 env
      { mach with memory := deallocLocalMemory mach.memory (mf.locals[idx]'hlt_mf).value }
      decl body.layouts newSlot { mf.locals[idx]'hlt_mf with value := newVal }) :
    FrameRelLM2_2 body env
      { mach with memory := deallocLocalMemory mach.memory (mf.locals[idx]'hlt_mf).value }
      { af with locals := af.locals.set idx newSlot }
      { mf with locals := mf.locals.set idx { mf.locals[idx]'hlt_mf with value := newVal } hlt_mf } := by
  refine ⟨hrel.body_eq, hrel.location_eq, by rw [List.length_set, hrel.af_locals_len],
    by rw [Array.size_set, hrel.mf_locals_size], ?_⟩
  intro i decl_i slot_i mls_i hdecl_i hslot_i hmls_i
  have hlt_af : idx < af.locals.length := by
    rw [hrel.af_locals_len, ← hrel.mf_locals_size]; exact hlt_mf
  dsimp only [get?] at hslot_i
  by_cases h_eq : idx = i
  · subst h_eq
    rw [List.getElem?_set_self hlt_af] at hslot_i; injection hslot_i with hsl; subst hsl
    rw [Array.getElem?_set_self hlt_mf] at hmls_i; injection hmls_i with hml; subst hml
    rw [hdecl] at hdecl_i; injection hdecl_i with hd; subst hd
    exact hnew
  · rw [List.getElem?_set_ne h_eq, ← get?_eq_getElem?] at hslot_i
    rw [Array.getElem?_set_ne _ h_eq] at hmls_i
    apply (hrel.locals_rel i decl_i slot_i mls_i hdecl_i hslot_i hmls_i).of_dealloc
    intro mp mp' hv hv'
    apply hdisj idx i mp mp' (mf.locals[idx]'hlt_mf).layout mls_i.layout h_eq
    · rw [Array.getElem?_eq_getElem hlt_mf]
      cases hls : mf.locals[idx]'hlt_mf
      rw [hls] at hv; dsimp only at hv ⊢; rw [hv]
    · rw [hmls_i]
      cases mls_i; dsimp only at hv' ⊢; rw [hv']

/-- Post-state static environment after `StorageLive(loc)`. -/
def storageLivePostStaticEnv (stEnv : LM2_2StaticEnv) (loc : Local) : LM2_2StaticEnv where
  initLocals := stEnv.initLocals.filter (· != loc)
  immLocals := loc :: stEnv.immLocals

/-- Post-state static environment after `StorageDead(loc)`. -/
def storageDeadPostStaticEnv (stEnv : LM2_2StaticEnv) (loc : Local) : LM2_2StaticEnv where
  initLocals := loc :: stEnv.initLocals
  immLocals := loc :: stEnv.immLocals

/-- `StorageLive(loc)` simulation in `StateRelLM2_2` for any declared local
(immediate or memory-backed). -/
theorem step_storageLive_lm2_2_simulation
    {body : CapturedMir} {env : StructTypeEnv} {stEnv : LM2_2StaticEnv} {k_bud : Nat}
    {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_2 body env stEnv k_bud s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {loc : Local} {decl : LocalDecl} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.storageLive loc, span⟩)
    (hdecl : get? body.localDecls loc = some decl) :
    StepRelLM2_2 body env (storageLivePostStaticEnv stEnv loc) k_bud m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  rcases hstate with
    ⟨topFrame, hframes, hretCont, ⟨retLay, hretPlace⟩, hframe,
      hinit_env, himm_env, hsupply, hcal, hstack, hbor, hprot, hcaller, hdisj⟩
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  simp only [hbb, hstmt]
  obtain ⟨slot, mls, hlt_mf, hlt_af, hslot, _, hmls_eq, hloc⟩ := hframe.lookup_local hdecl
  have ha : evalStmt s ⟨.storageLive loc, span⟩ body.localDecls body.layouts =
      MirStepNode.step (advanceStmt s (s.frame.locals.set loc .uninit)) := by
    unfold evalStmt; dsimp only; rw [hslot, set?_eq_some_set hlt_af]
  have hty : ∃ ty, topFrame.body.locals[loc]? = some ty := by
    rw [hframe.body_eq, translateBody_locals_getElem?, hdecl]; exact ⟨_, rfl⟩
  have hlive : LocalAllocLive m.machine.memory (topFrame.locals[loc]'hlt_mf).value := by
    rw [hmls_eq]; exact hloc.allocLive
  have hm : Miri.Interpreter.Step.evalStatement (annealStepHooks body.localDecls body.layouts) ()
      (translateStmt ⟨.storageLive loc, span⟩) m =
      ({ stack := ⟨#[{ topFrame with
            locals := topFrame.locals.set loc
              { topFrame.locals[loc]'hlt_mf with value := .live (.immediate .uninit) } hlt_mf }]⟩
         machine := { m.machine with
            memory := deallocLocalMemory m.machine.memory (topFrame.locals[loc]'hlt_mf).value } },
       .ok ()) := by
    unfold Miri.Interpreter.Step.evalStatement translateStmt
    exact annealStepHooks_storageLive_any_eq hframes hlt_mf hty hlive
  have hnew_loc : LocalRelLM2_2 env
      { m.machine with memory := deallocLocalMemory m.machine.memory (topFrame.locals[loc]'hlt_mf).value }
      decl body.layouts .uninit
      { topFrame.locals[loc]'hlt_mf with value := .live (.immediate .uninit) } := by
    rw [hmls_eq]
    cases henv : env decl.ty with
    | none =>
      exact .base .uninit _ henv
        (.immediate .uninit .uninit mls.layout hloc.cachedLayout_eq (Or.inl ⟨rfl, rfl⟩))
    | some fp =>
      exact .structUninitImm fp.1 fp.2 mls.layout henv hloc.cachedLayout_eq
  have hfr' := hframe.update_local_dealloc hdisj hdecl .uninit (.live (.immediate .uninit)) hnew_loc
  rw [ha, miri_step_at_statement_ok _ hframes hframe.body_eq hframe.location_eq hbb hstmt
    hm rfl hframe.location_eq]
  refine .step _ _ ?_
  refine .mk _ rfl hretCont ⟨retLay, hretPlace⟩ hfr'.step_pc ?_ ?_
    (hsupply.of_dealloc _) hcal hstack hbor hprot hcaller ?_
  · intro j hj
    dsimp only [storageLivePostStaticEnv] at hj
    rw [List.mem_filter] at hj
    have hne : loc ≠ j := fun h => by subst h; simp at hj
    dsimp only [advanceStmt, get?]
    rw [List.getElem?_set_ne hne, ← get?_eq_getElem?]
    exact hinit_env j hj.1
  · intro j hj mp lay
    dsimp only [storageLivePostStaticEnv] at hj
    dsimp only
    by_cases hlj : loc = j
    · subst hlj; rw [Array.getElem?_set_self hlt_mf]; nofun
    · rw [Array.getElem?_set_ne _ hlj]
      rcases List.mem_cons.mp hj with rfl | hj_old
      · exact False.elim (hlj rfl)
      · exact himm_env j hj_old mp lay
  · apply MemoryAllocDisjoint.mono_immediate hdisj
    intro k
    by_cases hk : loc = k
    · subst hk
      exact Or.inr ⟨.uninit, (topFrame.locals[loc]'hlt_mf).layout, by simp⟩
    · exact Or.inl (by dsimp only; rw [Array.getElem?_set_ne _ hk])

/-- `StorageDead(loc)` simulation in `StateRelLM2_2` for any declared non-return
local `loc ≠ 0` (immediate or memory-backed). -/
theorem step_storageDead_lm2_2_simulation
    {body : CapturedMir} {env : StructTypeEnv} {stEnv : LM2_2StaticEnv} {k_bud : Nat}
    {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_2 body env stEnv k_bud s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {loc : Local} {decl : LocalDecl} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.storageDead loc, span⟩)
    (hdecl : get? body.localDecls loc = some decl)
    (hne : loc ≠ 0) :
    StepRelLM2_2 body env (storageDeadPostStaticEnv stEnv loc) k_bud m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  rcases hstate with
    ⟨topFrame, hframes, hretCont, ⟨retLay, hretPlace⟩, hframe,
      hinit_env, himm_env, hsupply, hcal, hstack, hbor, hprot, hcaller, hdisj⟩
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  simp only [hbb, hstmt]
  obtain ⟨slot, mls, hlt_mf, hlt_af, hslot, _, hmls_eq, hloc⟩ := hframe.lookup_local hdecl
  have ha : evalStmt s ⟨.storageDead loc, span⟩ body.localDecls body.layouts =
      MirStepNode.step (advanceStmt s (s.frame.locals.set loc .dead)) := by
    unfold evalStmt; dsimp only; rw [hslot, set?_eq_some_set hlt_af]
  have hlive : LocalAllocLive m.machine.memory (topFrame.locals[loc]'hlt_mf).value := by
    rw [hmls_eq]; exact hloc.allocLive
  have hm : Miri.Interpreter.Step.evalStatement (annealStepHooks body.localDecls body.layouts) ()
      (translateStmt ⟨.storageDead loc, span⟩) m =
      ({ stack := ⟨#[{ topFrame with
            locals := topFrame.locals.set loc
              { topFrame.locals[loc]'hlt_mf with value := .dead } hlt_mf }]⟩
         machine := { m.machine with
            memory := deallocLocalMemory m.machine.memory (topFrame.locals[loc]'hlt_mf).value } },
       .ok ()) := by
    unfold Miri.Interpreter.Step.evalStatement translateStmt
    exact annealStepHooks_storageDead_any_eq hframes hlt_mf hne hlive
  have hnew_loc : LocalRelLM2_2 env
      { m.machine with memory := deallocLocalMemory m.machine.memory (topFrame.locals[loc]'hlt_mf).value }
      decl body.layouts .dead
      { topFrame.locals[loc]'hlt_mf with value := .dead } := by
    rw [hmls_eq]
    cases henv : env decl.ty with
    | none => exact .base .dead _ henv (.dead mls.layout hloc.cachedLayout_eq)
    | some fp => exact .structDead fp.1 fp.2 mls.layout henv hloc.cachedLayout_eq
  have hfr' := hframe.update_local_dealloc hdisj hdecl .dead .dead hnew_loc
  rw [ha, miri_step_at_statement_ok _ hframes hframe.body_eq hframe.location_eq hbb hstmt
    hm rfl hframe.location_eq]
  refine .step _ _ ?_
  refine .mk _ rfl hretCont ⟨retLay, hretPlace⟩ hfr'.step_pc ?_ ?_
    (hsupply.of_dealloc _) hcal hstack hbor hprot hcaller ?_
  · intro j hj
    dsimp only [storageDeadPostStaticEnv] at hj
    dsimp only [advanceStmt, get?]
    by_cases hlj : loc = j
    · subst hlj; rw [List.getElem?_set_self hlt_af]; nofun
    · rw [List.getElem?_set_ne hlj, ← get?_eq_getElem?]
      rcases List.mem_cons.mp hj with rfl | hj_old
      · exact False.elim (hlj rfl)
      · exact hinit_env j hj_old
  · intro j hj mp lay
    dsimp only [storageDeadPostStaticEnv] at hj
    dsimp only
    by_cases hlj : loc = j
    · subst hlj; rw [Array.getElem?_set_self hlt_mf]; nofun
    · rw [Array.getElem?_set_ne _ hlj]
      rcases List.mem_cons.mp hj with rfl | hj_old
      · exact False.elim (hlj rfl)
      · exact himm_env j hj_old mp lay
  · apply MemoryAllocDisjoint.mono_dead hdisj
    intro k
    by_cases hk : loc = k
    · subst hk
      exact Or.inr ⟨(topFrame.locals[loc]'hlt_mf).layout, by simp⟩
    · exact Or.inl (by dsimp only; rw [Array.getElem?_set_ne _ hk])

/-- `StatementKind.nop` simulation in `StateRelLM2_2`. -/
theorem step_nop_lm2_2_simulation
    {body : CapturedMir} {env : StructTypeEnv} {stEnv : LM2_2StaticEnv} {k_bud : Nat}
    {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_2 body env stEnv k_bud s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.nop, span⟩) :
    StepRelLM2_2 body env stEnv k_bud m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  rcases hstate with
    ⟨topFrame, hframes, hretCont, ⟨retLay, hretPlace⟩, hframe,
      hinit_env, himm_env, hsupply, hcal, hstack, hbor, hprot, hcaller, hdisj⟩
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  simp only [hbb, hstmt]
  have ha : evalStmt s ⟨.nop, span⟩ body.localDecls body.layouts =
      MirStepNode.step (advanceStmt s s.frame.locals) := rfl
  have hm : Miri.Interpreter.Step.evalStatement (annealStepHooks body.localDecls body.layouts) ()
      (translateStmt ⟨.nop, span⟩) m = (m, .ok ()) := rfl
  rw [ha, miri_step_at_statement_ok _ hframes hframe.body_eq hframe.location_eq hbb hstmt
    hm hframes hframe.location_eq]
  exact .step _ _ (.mk _ rfl hretCont ⟨retLay, hretPlace⟩ hframe.step_pc
    hinit_env himm_env hsupply hcal hstack hbor hprot hcaller hdisj)

/-- Post-state static environment after an unprojected `_dst = Rvalue.Use(op)`. -/
def usePostStaticEnv (stEnv : LM2_2StaticEnv) (dstIdx : Local) (op : MirAst.Operand) :
    LM2_2StaticEnv :=
  let s1 := operandPostStaticEnv stEnv op
  { initLocals := dstIdx :: s1.initLocals
    immLocals := dstIdx :: s1.immLocals }

/-- Syntactic (state-independent) typing predicate for an unprojected assignment
`_dst = Rvalue.Use(op)` in `LM-2.2`, supporting primitive scalar values as well
as immediate-ABI structs/tuples (`.Scalar` wrappers and `.ScalarPair` pairs). -/
inductive WellTypedLM2_2UseAssign
    (body : CapturedMir)
    (env : StructTypeEnv)
    (stEnv : LM2_2StaticEnv)
    (dstIdx : Local)
    (op : MirAst.Operand) : Prop where
  | mk
      (decl : LocalDecl)
      (decl_lookup : get? body.localDecls dstIdx = some decl)
      (dst_imm : dstIdx ∈ stEnv.immLocals)
      (op_wt : WellTypedLM2_2Operand body env stEnv op decl.ty) :
      WellTypedLM2_2UseAssign body env stEnv dstIdx op

private theorem mem_operandPostStaticEnv_immLocals
    {stEnv : LM2_2StaticEnv} {dstIdx : Local} {op : MirAst.Operand}
    (h : dstIdx ∈ stEnv.immLocals) :
    dstIdx ∈ (operandPostStaticEnv stEnv op).immLocals := by
  cases op with
  | constant _ | copy _ => exact h
  | move pl =>
    rcases pl with ⟨idx, projs⟩
    cases projs with
    | nil => exact List.mem_cons_of_mem idx h
    | cons _ _ => exact h

/-- Unprojected `_dst = Rvalue.Use(op)` simulation in `StateRelLM2_2`, supporting
scalar constants, scalar/projected reads, and immediate `Scalar`/`ScalarPair`
tuple/struct copies and moves (`_2 = Use(Copy(_1))`, `_2 = Use(Move(_1))`). -/
theorem step_assign_use_lm2_2_simulation
    {body : CapturedMir} {env : StructTypeEnv} {stEnv : LM2_2StaticEnv} {k_bud : Nat}
    {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_2 body env stEnv k_bud s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx : Local} {op : MirAst.Operand} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.use op), span⟩)
    (hwt : WellTypedLM2_2UseAssign body env stEnv dstIdx op) :
    StepRelLM2_2 body env (usePostStaticEnv stEnv dstIdx op) k_bud m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  cases hwt with
  | mk decl hdecl hdst_imm hop =>
    rcases hstate with
      ⟨topFrame, hframes, hretCont, ⟨retLay, hretPlace⟩, hframe,
        hinit_env, himm_env, hsupply, hcal, hstack, hbor, hprot, hcaller, hdisj⟩
    rw [stepMirFn_eq_of_not_other body s hcal hphase]
    simp only [hbb, hstmt]
    obtain ⟨_, mls_dst0, hlt_dst0, _, _, _, hmls_eq0, hloc_dst0⟩ := hframe.lookup_local hdecl
    have hcache_dst0 : ∀ l, (topFrame.locals[dstIdx]'hlt_dst0).layout = some l →
        l = translateTy decl.ty body.layouts := by
      rw [hmls_eq0]; exact hloc_dst0.layout_eq
    have hevalPlace := annealEvalPlace_unprojected hframes hlt_dst0 hdecl hcache_dst0
    have hm_eval := evalStatement_assign_use_eq (dst := ⟨dstIdx, .nil⟩) (op := op) (span := span)
      hevalPlace (hop.usesStructMemCopyDest_false _)
    have hfr₀_exc : FrameRelLM2_2Except body env none m.machine s.frame
        (cacheFrameLocalLayout topFrame dstIdx hlt_dst0 (translateTy decl.ty body.layouts)) :=
      FrameRelLM2_2Except.of_frameRel none (hframe.cache_local_layout hdecl hlt_dst0)
    have hdisj₀ : MemoryAllocDisjoint
        (cacheFrameLocalLayout topFrame dstIdx hlt_dst0 (translateTy decl.ty body.layouts)) :=
      MemoryAllocDisjoint_cacheFrameLocalLayout hdisj hlt_dst0 (translateTy decl.ty body.layouts)
    have himm_env₀ : ∀ j ∈ stEnv.immLocals, (none : Option Local) ≠ some j → ∀ mp l,
        (cacheFrameLocalLayout topFrame dstIdx hlt_dst0
          (translateTy decl.ty body.layouts)).locals[j]? ≠
          some ⟨.live (.indirect mp), l⟩ := by
      intro j hj _ mp l
      dsimp only [cacheFrameLocalLayout]
      by_cases hij : dstIdx = j
      · subst hij
        rw [Array.getElem?_set_self hlt_dst0, hmls_eq0]
        intro heq; injection heq with hls
        rcases mls_dst0 with ⟨val0, lay0⟩
        injection hls with hv_eq _; subst hv_eq
        exact himm_env dstIdx hj mp lay0
          (by rw [Array.getElem?_eq_getElem hlt_dst0, hmls_eq0])
      · rw [Array.getElem?_set_ne _ hij]; exact himm_env j hj mp l
    have hsim := evalLM2_2Operand_except
      (m := { m with stack := ⟨#[cacheFrameLocalLayout topFrame dstIdx hlt_dst0
          (translateTy decl.ty body.layouts)]⟩ })
      rfl hfr₀_exc (fun j hj _ => hinit_env j hj) himm_env₀ (by nofun)
      hop s.memory.globals (some (translateTy decl.ty body.layouts))
    generalize hev_op :
      evalOperand s.frame.locals op .nil s.memory.globals body.layouts .nil = r_a at hsim
    generalize hm_op :
      (annealEvalOperand body.localDecls body.layouts (translateOperand op)
        (some (translateTy decl.ty body.layouts)) >>= annealReadImmediate)
        { m with stack := ⟨#[cacheFrameLocalLayout topFrame dstIdx hlt_dst0
            (translateTy decl.ty body.layouts)]⟩ } = r_m at hsim
    cases hsim with
    | ub m_err msg =>
      have ha_ub : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.use op), span⟩
          body.localDecls body.layouts = MirStepNode.fail .ub := by
        unfold evalStmt; dsimp only
        rw [evalRvalue_use_nil_borrows _ _ _ hbor, hcaller, hev_op]
      have hm_ub : Miri.Interpreter.Step.evalStatement (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.use op), span⟩) m =
          (m_err, .error (.undefinedBehavior msg)) := by
        rw [hm_eval]; unfold Miri.Interpreter.runRvalue; rw [EStateM.bind_eq_error hm_op]
      rw [ha_ub, miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq hbb hstmt hm_ub]
      exact .ub _ _
    | ok v locals₁ tf₁ imm _ hfr₁ hvRel _ _ hid₁ hrc₁ hrp₁ _ _ _ hinit₁ himm₁ hdisj₁ =>
      dsimp only [cacheFrameLocalLayout] at hid₁ hrc₁ hrp₁
      have hfr₁' := hfr₁.toFrameRel
      have hdisj_tf₁ := hdisj₁ hdisj₀
      obtain ⟨slot_d, mls_d, hlt_mf₁, hlt_af₁, hslot_d, hmls_d, hmls_eq₁, hloc_d⟩ :=
        hfr₁'.lookup_local hdecl
      have hget_d := frame_getLocal_of_getElem? tf₁ dstIdx mls_d hmls_d
      have hnot_ind_d : ∀ mp lay, tf₁.locals[dstIdx]? ≠ some ⟨.live (.indirect mp), lay⟩ :=
        himm₁ dstIdx (mem_operandPostStaticEnv_immLocals hdst_imm) (by nofun)
      have hm_dead_or_live :
          (slot_d = .dead ∧ ∃ lay, mls_d = ⟨.dead, lay⟩) ∨
          (slot_d ≠ .dead ∧ ∃ oldImm lay, mls_d = ⟨.live (.immediate oldImm), lay⟩) := by
        cases hloc_d with
        | base _ _ _ hb =>
          cases hb with
          | dead c _ => exact Or.inl ⟨rfl, c, rfl⟩
          | immediate _ oldImm c _ hv =>
            refine Or.inr ⟨?_, oldImm, c, rfl⟩
            rcases hv with ⟨rfl, _⟩ | ⟨_, rfl, _⟩ <;> nofun
          | indirect _ mp c _ _ _ => exact False.elim (hnot_ind_d mp c hmls_d)
        | structDead _ _ c _ _ => exact Or.inl ⟨rfl, c, rfl⟩
        | structUninitImm _ _ c _ _ => exact Or.inr ⟨by nofun, .uninit, c, rfl⟩
        | structImm _ _ _ oldImm c _ _ _ => exact Or.inr ⟨by nofun, oldImm, c, rfl⟩
        | structUninitInd _ _ mp c _ _ _ | structInd _ _ _ mp c _ _ _ =>
          exact False.elim (hnot_ind_d mp c hmls_d)
      rcases hm_dead_or_live with ⟨rfl, lay_d, rfl⟩ | ⟨hnot_dead, oldImm, lay_d, rfl⟩
      · have ha_ub : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.use op), span⟩
            body.localDecls body.layouts = MirStepNode.fail .ub := by
          unfold evalStmt; dsimp only
          rw [evalRvalue_use_nil_borrows _ _ _ hbor, hcaller, hev_op]; dsimp only
          rw [hprot, hbor, hslot_d]
        have hm_ub : Miri.Interpreter.Step.evalStatement (annealStepHooks body.localDecls body.layouts) ()
            (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.use op), span⟩) m =
            ({ m with stack := ⟨#[tf₁]⟩ }, .error (.undefinedBehavior "write to dead local")) := by
          rw [hm_eval]; unfold Miri.Interpreter.runRvalue
          rw [EStateM.bind_eq_ok hm_op]; dsimp only
          rw [annealWriteImmediate_dead (topFrame := tf₁) rfl hget_d]
        rw [ha_ub, miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq hbb hstmt hm_ub]
        exact .ub _ _
      · have ha_ok : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.use op), span⟩
            body.localDecls body.layouts =
            MirStepNode.step (advanceStmt s (locals₁.set dstIdx (.init v)) s.memory) := by
          unfold evalStmt; dsimp only
          rw [evalRvalue_use_nil_borrows _ _ _ hbor, hcaller, hev_op]; dsimp only
          rw [hprot, hbor, hslot_d]
          cases slot_d with
          | dead => exact absurd rfl hnot_dead
          | uninit | init _ =>
            dsimp only; rw [set?_eq_some_set hlt_af₁]
            apply congrArg (fun mem =>
              MirStepNode.step (advanceStmt s (locals₁.set dstIdx (.init v)) mem))
            revert hbor hprot; generalize s.memory = mem; rintro hbor hprot
            cases mem; dsimp only at hbor hprot ⊢; subst hbor hprot; rfl
        have hm_ok : Miri.Interpreter.Step.evalStatement (annealStepHooks body.localDecls body.layouts) ()
            (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.use op), span⟩) m =
            ({ m with
                stack := ⟨#[{ tf₁ with
                  locals := tf₁.locals.set dstIdx
                    { tf₁.locals[dstIdx]'hlt_mf₁ with value := .live (.immediate imm) } hlt_mf₁ }]⟩ },
             .ok ()) := by
          rw [hm_eval]; unfold Miri.Interpreter.runRvalue
          rw [EStateM.bind_eq_ok hm_op]; dsimp only
          rw [annealWriteImmediate_live (topFrame := tf₁) rfl hlt_mf₁ hget_d]
        have hloc_new : LocalRelLM2_2 env m.machine decl body.layouts (.init v)
            { tf₁.locals[dstIdx]'hlt_mf₁ with value := .live (.immediate imm) } := by
          rw [hmls_eq₁]
          cases hvRel with
          | primScalar sc msc henv_none _ himmRel =>
            exact .base (.init (.scalar sc)) _ henv_none
              (.immediate _ _ lay_d hloc_d.cachedLayout_eq (Or.inr ⟨_, rfl, himmRel⟩))
          | immStruct fs ps _ _ hsub himmS =>
            exact .structImm fs ps v imm lay_d hsub.env_eq hloc_d.cachedLayout_eq himmS
        have hfr₂ := hfr₁'.update_local hdecl (.init v) (.live (.immediate imm)) hloc_new
        rw [ha_ok, miri_step_at_statement_ok _ hframes hframe.body_eq hframe.location_eq hbb hstmt
          hm_ok rfl hfr₂.location_eq]
        refine .step _ _ ?_
        refine .mk _ rfl (hrc₁.trans hretCont)
          ⟨retLay, by dsimp; rw [hrp₁, hretPlace, hid₁]⟩
          hfr₂.step_pc ?_ ?_ hsupply hcal hstack hbor hprot hcaller ?_
        · intro j hj
          dsimp only [usePostStaticEnv] at hj
          dsimp only [advanceStmt, get?]
          by_cases hjd : dstIdx = j
          · subst hjd; rw [List.getElem?_set_self hlt_af₁]; nofun
          · rw [List.getElem?_set_ne hjd, ← get?_eq_getElem?]
            rcases List.mem_cons.mp hj with rfl | hj_old
            · exact False.elim (hjd rfl)
            · exact hinit₁ j hj_old (by nofun)
        · intro j hj mp lay
          dsimp only [usePostStaticEnv] at hj
          dsimp only
          by_cases hjd : dstIdx = j
          · subst hjd; rw [Array.getElem?_set_self hlt_mf₁]; nofun
          · rw [Array.getElem?_set_ne _ hjd]
            rcases List.mem_cons.mp hj with rfl | hj_old
            · exact False.elim (hjd rfl)
            · exact himm₁ j hj_old (by nofun) mp lay
        · apply MemoryAllocDisjoint.mono_immediate hdisj_tf₁
          intro k
          by_cases hk : dstIdx = k
          · subst hk
            exact Or.inr ⟨imm, (tf₁.locals[dstIdx]'hlt_mf₁).layout, by simp⟩
          · exact Or.inl (by dsimp only; rw [Array.getElem?_set_ne _ hk])

/-! ## 8. Whole-Value Reassignment of Immediate-ABI Structs (`step_assign_use_struct_lm2_2_simulation`)

Aggregate construction and projected field writes move `.Scalar` and
`.ScalarPair` struct locals into memory (`forceAllocation`), so a later
whole-value assignment `_dst = Use(copy _src)` must handle a memory-backed
destination. Upstream `writePlaceImmediateNoValidate` then writes the immediate
through the local's `MemPlace`, and so does `annealWriteImmediate`. -/

/-- An unprojected `annealWriteImmediate` to an `.indirect` (memory-backed) local
writes the whole immediate through its `MemPlace` at relative offset `0`. -/
theorem annealWriteImmediate_unprojected_indirect_eq
    {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {dstIdx : Nat} {val : Miri.Interpreter.Immediate AnnealProv}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    {lay : Option Miri.Interpreter.LocalLayout}
    {dstLay : Miri.Interpreter.LocalLayout}
    {id0 : Miri.Interpreter.LocalsIdentity}
    (hframes : m.stack.frames = #[topFrame])
    (hget : topFrame.getLocal dstIdx = .ok ⟨.live (.indirect mp), lay⟩) :
    annealWriteImmediate val ⟨.local 0 dstIdx none id0, dstLay⟩ m =
      annealWriteIndirectImmediate val mp Miri.ABI.Size.ZERO dstLay m := by
  have hgop := frame_getLocalOperand_live topFrame hget
  with_unfolding_all
    unfold annealWriteImmediate
    simp only [get, getThe, MonadStateOf.get, EStateM.get, Bind.bind, EStateM.bind,
      stack_currentFrame?_singleton m.stack topFrame hframes, hframes, hgop]
    rfl

/-- Post-state static environment after a whole-value struct assignment
`_dst = Rvalue.Use(op)`: `dstIdx` becomes initialized, and because it may stay in
memory it is removed from `immLocals`. -/
def useStructPostStaticEnv (stEnv : LM2_2StaticEnv) (dstIdx : Local) (op : MirAst.Operand) :
    LM2_2StaticEnv :=
  let s1 := operandPostStaticEnv stEnv op
  { initLocals := dstIdx :: s1.initLocals
    immLocals := s1.immLocals.filter (· != dstIdx) }

/-- Syntactic (state-independent) typing predicate for a whole-value assignment
`_dst = Rvalue.Use(op)` of an immediate-ABI tuple/struct (`.Scalar` wrapper or
`.ScalarPair`). Unlike `WellTypedLM2_2UseAssign`, the destination need not be in
`immLocals`: it may be dead, immediate, or held in a stack allocation (for
example after an earlier `Aggregate` or projected field write moved it to
memory). -/
inductive WellTypedLM2_2UseAssignStruct
    (body : CapturedMir)
    (env : StructTypeEnv)
    (stEnv : LM2_2StaticEnv)
    (dstIdx : Local)
    (op : MirAst.Operand) : Prop where
  | mk
      (decl : LocalDecl)
      (fields : List StructFieldDesc)
      (paths : List (List ProjectionElem))
      (decl_lookup : get? body.localDecls dstIdx = some decl)
      (dst_struct : IsImmediateStructTy env body.layouts decl.ty fields paths)
      (op_wt : WellTypedLM2_2Operand body env stEnv op decl.ty) :
      WellTypedLM2_2UseAssignStruct body env stEnv dstIdx op

/-- Whole-value struct assignment `_dst = Rvalue.Use(op)` in `StateRelLM2_2`, for
every state of the destination:
* `.dead`: both sides raise UB;
* immediate (`.uninit` or a `.Scalar`/`.ScalarPair` immediate): the local is
  replaced by the new immediate (`.structImm`);
* memory-backed (`UninitStructMemPlaceRel` or `StructMemPlaceRel`): the immediate
  is written through the local's `MemPlace`, exactly as upstream
  `writePlaceImmediateNoValidate` does, re-establishing `StructMemPlaceRel` for
  the new value with every padding byte still `.uninit` (`.structInd`).
No allocation happens, so the allocation budget is unchanged. -/
theorem step_assign_use_struct_lm2_2_simulation
    {body : CapturedMir} {env : StructTypeEnv} {stEnv : LM2_2StaticEnv} {k_bud : Nat}
    {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_2 body env stEnv k_bud s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx : Local} {op : MirAst.Operand} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.use op), span⟩)
    (hwt : WellTypedLM2_2UseAssignStruct body env stEnv dstIdx op) :
    StepRelLM2_2 body env (useStructPostStaticEnv stEnv dstIdx op) k_bud m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  cases hwt with
  | mk decl fields paths hdecl hdst_struct hop =>
    rcases hstate with
      ⟨topFrame, hframes, hretCont, ⟨retLay, hretPlace⟩, hframe,
        hinit_env, himm_env, hsupply, hcal, hstack, hbor, hprot, hcaller, hdisj⟩
    rw [stepMirFn_eq_of_not_other body s hcal hphase]
    simp only [hbb, hstmt]
    have henv_d := hdst_struct.env_eq
    obtain ⟨_, mls_dst0, hlt_dst0, _, _, _, hmls_eq0, hloc_dst0⟩ := hframe.lookup_local hdecl
    have hcache_dst0 : ∀ l, (topFrame.locals[dstIdx]'hlt_dst0).layout = some l →
        l = translateTy decl.ty body.layouts := by
      rw [hmls_eq0]; exact hloc_dst0.layout_eq
    have hevalPlace := annealEvalPlace_unprojected hframes hlt_dst0 hdecl hcache_dst0
    have hm_eval := evalStatement_assign_use_eq (dst := ⟨dstIdx, .nil⟩) (op := op) (span := span)
      hevalPlace (hop.usesStructMemCopyDest_false _)
    have hfr₀_exc : FrameRelLM2_2Except body env none m.machine s.frame
        (cacheFrameLocalLayout topFrame dstIdx hlt_dst0 (translateTy decl.ty body.layouts)) :=
      FrameRelLM2_2Except.of_frameRel none (hframe.cache_local_layout hdecl hlt_dst0)
    have hdisj₀ : MemoryAllocDisjoint
        (cacheFrameLocalLayout topFrame dstIdx hlt_dst0 (translateTy decl.ty body.layouts)) :=
      MemoryAllocDisjoint_cacheFrameLocalLayout hdisj hlt_dst0 (translateTy decl.ty body.layouts)
    have himm_env₀ : ∀ j ∈ stEnv.immLocals, (none : Option Local) ≠ some j → ∀ mp l,
        (cacheFrameLocalLayout topFrame dstIdx hlt_dst0
          (translateTy decl.ty body.layouts)).locals[j]? ≠
          some ⟨.live (.indirect mp), l⟩ := by
      intro j hj _ mp l
      dsimp only [cacheFrameLocalLayout]
      by_cases hij : dstIdx = j
      · subst hij
        rw [Array.getElem?_set_self hlt_dst0, hmls_eq0]
        intro heq; injection heq with hls
        rcases mls_dst0 with ⟨val0, lay0⟩
        injection hls with hv_eq _; subst hv_eq
        exact himm_env dstIdx hj mp lay0
          (by rw [Array.getElem?_eq_getElem hlt_dst0, hmls_eq0])
      · rw [Array.getElem?_set_ne _ hij]; exact himm_env j hj mp l
    have hsim := evalLM2_2Operand_except
      (m := { m with stack := ⟨#[cacheFrameLocalLayout topFrame dstIdx hlt_dst0
          (translateTy decl.ty body.layouts)]⟩ })
      rfl hfr₀_exc (fun j hj _ => hinit_env j hj) himm_env₀ (by nofun)
      hop s.memory.globals (some (translateTy decl.ty body.layouts))
    generalize hev_op :
      evalOperand s.frame.locals op .nil s.memory.globals body.layouts .nil = r_a at hsim
    generalize hm_op :
      (annealEvalOperand body.localDecls body.layouts (translateOperand op)
        (some (translateTy decl.ty body.layouts)) >>= annealReadImmediate)
        { m with stack := ⟨#[cacheFrameLocalLayout topFrame dstIdx hlt_dst0
            (translateTy decl.ty body.layouts)]⟩ } = r_m at hsim
    cases hsim with
    | ub m_err msg =>
      have ha_ub : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.use op), span⟩
          body.localDecls body.layouts = MirStepNode.fail .ub := by
        unfold evalStmt; dsimp only
        rw [evalRvalue_use_nil_borrows _ _ _ hbor, hcaller, hev_op]
      have hm_ub : Miri.Interpreter.Step.evalStatement (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.use op), span⟩) m =
          (m_err, .error (.undefinedBehavior msg)) := by
        rw [hm_eval]; unfold Miri.Interpreter.runRvalue; rw [EStateM.bind_eq_error hm_op]
      rw [ha_ub, miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq hbb hstmt hm_ub]
      exact .ub _ _
    | ok v locals₁ tf₁ imm _ hfr₁ hvRel _ _ hid₁ hrc₁ hrp₁ _ _ _ hinit₁ himm₁ hdisj₁ =>
      dsimp only [cacheFrameLocalLayout] at hid₁ hrc₁ hrp₁
      have hfr₁' := hfr₁.toFrameRel
      have hdisj_tf₁ := hdisj₁ hdisj₀
      obtain ⟨slot_d, mls_d, hlt_mf₁, hlt_af₁, hslot_d, hmls_d, hmls_eq₁, hloc_d⟩ :=
        hfr₁'.lookup_local hdecl
      have hget_d := frame_getLocal_of_getElem? tf₁ dstIdx mls_d hmls_d
      -- The operand is an immediate struct of the destination type.
      have himmS : ImmediateStructRel decl.ty body.layouts fields paths v imm := by
        cases hvRel with
        | primScalar _ _ henv_none _ _ => rw [henv_d] at henv_none; cases henv_none
        | immStruct fs ps _ _ hsub himmS =>
          have hfp := hsub.env_eq.symm.trans henv_d
          injection hfp with hfp'; injection hfp' with hfs hps; subst hfs hps
          exact himmS
      have hcases :
          (slot_d = .dead ∧ ∃ lay, mls_d = ⟨.dead, lay⟩) ∨
          (slot_d ≠ .dead ∧ ∃ oldImm lay, mls_d = ⟨.live (.immediate oldImm), lay⟩) ∨
          (slot_d ≠ .dead ∧ ∃ (mp : Miri.Interpreter.MemPlace AnnealProv)
            (lay : Option Miri.Interpreter.LocalLayout)
            (allocId : Miri.Memory.AllocId) (tag : Miri.Memory.BorTag) (la : AnnealLocalAlloc)
            (u : Nat) (hu_lt : u < m.machine.memory.live.size)
            (alloc' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)),
            mls_d = ⟨.live (.indirect mp), lay⟩ ∧
            mp.ptr.provenance = some (.concrete allocId tag) ∧
            m.machine.memory.live[u]'hu_lt = (allocId, la) ∧
            annealWriteIndirectImmediate imm mp Miri.ABI.Size.ZERO
                (translateTy decl.ty body.layouts) { m with stack := ⟨#[tf₁]⟩ } =
              .ok () ⟨⟨#[tf₁]⟩, updateAllocMachine m.machine u allocId la.kind alloc'⟩ ∧
            StructMemPlaceRel (updateAllocMachine m.machine u allocId la.kind alloc')
              decl.ty body.layouts fields paths v mp) := by
        cases hloc_d with
        | base _ _ henv_none _ => rw [henv_d] at henv_none; cases henv_none
        | structDead _ _ c _ _ => exact Or.inl ⟨rfl, c, rfl⟩
        | structUninitImm _ _ c _ _ => exact Or.inr (Or.inl ⟨by nofun, .uninit, c, rfl⟩)
        | structImm _ _ _ oldImm c _ _ _ => exact Or.inr (Or.inl ⟨by nofun, oldImm, c, rfl⟩)
        | structUninitInd fs' ps' mp c henv' _ humpr =>
          have hfp := henv'.symm.trans henv_d
          injection hfp with hfp'; injection hfp' with hfs hps; subst hfs hps
          obtain ⟨allocId, tag, la, u, hu_lt, alloc', hprov, hget_u, hw, hsmpr'⟩ :=
            UninitStructMemPlaceRel.overwrite_immediate
              (m := { m with stack := ⟨#[tf₁]⟩ }) humpr himmS
          exact Or.inr (Or.inr ⟨by nofun, mp, c, allocId, tag, la, u, hu_lt, alloc', rfl,
            hprov, hget_u, hw, hsmpr'⟩)
        | structInd fs' ps' oldV mp c henv' _ hsmpr =>
          have hfp := henv'.symm.trans henv_d
          injection hfp with hfp'; injection hfp' with hfs hps; subst hfs hps
          obtain ⟨allocId, tag, la, u, hu_lt, alloc', hprov, hget_u, hw, hsmpr'⟩ :=
            StructMemPlaceRel.overwrite_immediate
              (m := { m with stack := ⟨#[tf₁]⟩ }) hsmpr himmS
          exact Or.inr (Or.inr ⟨by nofun, mp, c, allocId, tag, la, u, hu_lt, alloc', rfl,
            hprov, hget_u, hw, hsmpr'⟩)
      have ha_ok_of : slot_d ≠ .dead →
          evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.use op), span⟩
            body.localDecls body.layouts =
          MirStepNode.step (advanceStmt s (locals₁.set dstIdx (.init v)) s.memory) := by
        intro hnot_dead
        unfold evalStmt; dsimp only
        rw [evalRvalue_use_nil_borrows _ _ _ hbor, hcaller, hev_op]; dsimp only
        rw [hprot, hbor, hslot_d]
        cases slot_d with
        | dead => exact absurd rfl hnot_dead
        | uninit | init _ =>
          dsimp only; rw [set?_eq_some_set hlt_af₁]
          apply congrArg (fun mem =>
            MirStepNode.step (advanceStmt s (locals₁.set dstIdx (.init v)) mem))
          revert hbor hprot; generalize s.memory = mem; rintro hbor hprot
          cases mem; dsimp only at hbor hprot ⊢; subst hbor hprot; rfl
      have hinit_post : ∀ j ∈ (useStructPostStaticEnv stEnv dstIdx op).initLocals,
          get? (locals₁.set dstIdx (.init v)) j ≠ some .uninit := by
        intro j hj
        dsimp only [useStructPostStaticEnv] at hj
        dsimp only [get?]
        by_cases hjd : dstIdx = j
        · subst hjd; rw [List.getElem?_set_self hlt_af₁]; nofun
        · rw [List.getElem?_set_ne hjd, ← get?_eq_getElem?]
          rcases List.mem_cons.mp hj with rfl | hj_old
          · exact False.elim (hjd rfl)
          · exact hinit₁ j hj_old (by nofun)
      rcases hcases with ⟨rfl, lay_d, rfl⟩ | ⟨hnot_dead, oldImm, lay_d, rfl⟩ |
          ⟨hnot_dead, mp, lay_d, allocId, tag, la, u, hu_lt, alloc', rfl, hprov, hget_u, hw, hsmpr'⟩
      · -- Dead destination: both sides raise UB.
        have ha_ub : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.use op), span⟩
            body.localDecls body.layouts = MirStepNode.fail .ub := by
          unfold evalStmt; dsimp only
          rw [evalRvalue_use_nil_borrows _ _ _ hbor, hcaller, hev_op]; dsimp only
          rw [hprot, hbor, hslot_d]
        have hm_ub : Miri.Interpreter.Step.evalStatement (annealStepHooks body.localDecls body.layouts) ()
            (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.use op), span⟩) m =
            ({ m with stack := ⟨#[tf₁]⟩ }, .error (.undefinedBehavior "write to dead local")) := by
          rw [hm_eval]; unfold Miri.Interpreter.runRvalue
          rw [EStateM.bind_eq_ok hm_op]; dsimp only
          rw [annealWriteImmediate_dead (topFrame := tf₁) rfl hget_d]
        rw [ha_ub, miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq hbb hstmt hm_ub]
        exact .ub _ _
      · -- Immediate destination: the local is replaced by the new immediate.
        have hm_ok : Miri.Interpreter.Step.evalStatement (annealStepHooks body.localDecls body.layouts) ()
            (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.use op), span⟩) m =
            ({ m with
                stack := ⟨#[{ tf₁ with
                  locals := tf₁.locals.set dstIdx
                    { tf₁.locals[dstIdx]'hlt_mf₁ with value := .live (.immediate imm) } hlt_mf₁ }]⟩ },
             .ok ()) := by
          rw [hm_eval]; unfold Miri.Interpreter.runRvalue
          rw [EStateM.bind_eq_ok hm_op]; dsimp only
          rw [annealWriteImmediate_live (topFrame := tf₁) rfl hlt_mf₁ hget_d]
        have hloc_new : LocalRelLM2_2 env m.machine decl body.layouts (.init v)
            { tf₁.locals[dstIdx]'hlt_mf₁ with value := .live (.immediate imm) } := by
          rw [hmls_eq₁]
          exact .structImm fields paths v imm lay_d henv_d hloc_d.cachedLayout_eq himmS
        have hfr₂ := hfr₁'.update_local hdecl (.init v) (.live (.immediate imm)) hloc_new
        rw [ha_ok_of hnot_dead, miri_step_at_statement_ok _ hframes hframe.body_eq hframe.location_eq
          hbb hstmt hm_ok rfl hfr₂.location_eq]
        refine .step _ _ ?_
        refine .mk _ rfl (hrc₁.trans hretCont)
          ⟨retLay, by dsimp; rw [hrp₁, hretPlace, hid₁]⟩
          hfr₂.step_pc hinit_post ?_ hsupply hcal hstack hbor hprot hcaller ?_
        · intro j hj mp lay
          dsimp only [useStructPostStaticEnv] at hj
          rw [List.mem_filter] at hj
          have hjd : dstIdx ≠ j := fun h => by subst h; simp at hj
          dsimp only
          rw [Array.getElem?_set_ne _ hjd]
          exact himm₁ j hj.1 (by nofun) mp lay
        · apply MemoryAllocDisjoint.mono_immediate hdisj_tf₁
          intro k
          by_cases hk : dstIdx = k
          · subst hk
            exact Or.inr ⟨imm, (tf₁.locals[dstIdx]'hlt_mf₁).layout, by simp⟩
          · exact Or.inl (by dsimp only; rw [Array.getElem?_set_ne _ hk])
      · -- Memory-backed destination: write through the local's `MemPlace`.
        have hdst_tf₁ : tf₁.locals[dstIdx]'hlt_mf₁ = ⟨.live (.indirect mp), lay_d⟩ := hmls_eq₁
        have hm_ok : Miri.Interpreter.Step.evalStatement (annealStepHooks body.localDecls body.layouts) ()
            (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.use op), span⟩) m =
            (⟨⟨#[tf₁]⟩, updateAllocMachine m.machine u allocId la.kind alloc'⟩, .ok ()) := by
          rw [hm_eval]; unfold Miri.Interpreter.runRvalue
          rw [EStateM.bind_eq_ok hm_op]; dsimp only
          rw [annealWriteImmediate_unprojected_indirect_eq (topFrame := tf₁) rfl hget_d, hw]
        have hfr₁_excl : FrameRelLM2_2Except body env (some dstIdx) m.machine
            { s.frame with locals := locals₁ } tf₁ :=
          ⟨hfr₁.body_eq, hfr₁.location_eq, hfr₁.af_locals_len, hfr₁.mf_locals_size,
            fun i d sl ml _ hd hs hm => hfr₁.locals_rel i d sl ml (by nofun) hd hs hm⟩
        have hfr_end : FrameRelLM2_2 body env
            (updateAllocMachine m.machine u allocId la.kind alloc')
            { s.frame with locals := locals₁.set dstIdx (.init v) } tf₁ := by
          have hex := hfr₁_excl.of_updateAlloc_excl (kind := la.kind) (alloc' := alloc')
            hdisj_tf₁ hdst_tf₁ hprov hu_lt hget_u
          exact hex.fill_excluded hdecl hlt_af₁ hlt_mf₁ hdst_tf₁
            (.structInd fields paths v mp lay_d henv_d hloc_d.cachedLayout_eq hsmpr')
        rw [ha_ok_of hnot_dead, miri_step_at_statement_ok _ hframes hframe.body_eq hframe.location_eq
          hbb hstmt hm_ok rfl hfr_end.location_eq]
        refine .step _ _ ?_
        refine .mk _ rfl (hrc₁.trans hretCont)
          ⟨retLay, by dsimp; rw [hrp₁, hretPlace, hid₁]⟩
          hfr_end.step_pc hinit_post ?_ (hsupply.of_updateAlloc hu_lt hget_u)
          hcal hstack hbor hprot hcaller hdisj_tf₁
        intro j hj mp' lay'
        dsimp only [useStructPostStaticEnv] at hj
        rw [List.mem_filter] at hj
        exact himm₁ j hj.1 (by nofun) mp' lay'

/-- Extract `StructMemPlaceRel` directly from any `StateRelLM2_2`-related state
for an initialized `.Memory`-ABI aggregate local `idx`. -/
theorem StateRelLM2_2.extract_structMemPlaceRel
    {body : CapturedMir} {env : StructTypeEnv} {stEnv : LM2_2StaticEnv} {k_bud : Nat}
    {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_2 body env stEnv k_bud s m)
    {idx : Local} {decl : LocalDecl}
    {fields : List StructFieldDesc} {paths : List (List ProjectionElem)}
    {rootVal : Value}
    (hdecl : get? body.localDecls idx = some decl)
    (henv : env decl.ty = some (fields, paths))
    (hmem : (translateTy decl.ty body.layouts).layout.backendRepr = .Memory (sized := true))
    (hslot : get? s.frame.locals idx = some (.init rootVal)) :
    ∃ mp tf lay,
      m.stack.frames = #[tf] ∧
      tf.locals[idx]? = some ⟨.live (.indirect mp), lay⟩ ∧
      StructMemPlaceRel m.machine decl.ty body.layouts fields paths rootVal mp := by
  rcases hstate with ⟨tf, hframes, _, _, hframe, _, _, _, _, _, _, _, _, _⟩
  obtain ⟨slot, mls, _, _, hslot', hmls, _, hloc⟩ := hframe.lookup_local hdecl
  rw [hslot] at hslot'
  injection hslot' with hsl; subst hsl
  cases hloc with
  | base _ _ henv_none _ => rw [henv] at henv_none; cases henv_none
  | structImm _ _ _ _ _ _ _ himm =>
    cases himm with
    | scalarWrapper _ _ _ _ _ _ _ hrepr _ _ _ _ _ _ _ _ _ _ =>
      rw [hmem] at hrepr; cases hrepr
    | scalarPair _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hrepr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      rw [hmem] at hrepr; cases hrepr
  | structInd fs' ps' _ mp lay henv' _ hsmpr =>
    have hfp := henv.symm.trans henv'
    injection hfp with hp; injection hp with h1 h2; subst h1 h2
    exact ⟨mp, tf, lay, hframes, hmls, hsmpr⟩

/-- 100% syntactic (state-independent) typing predicate for a whole-value
copy or move `_dst = Rvalue.Use(copy _src)` / `_dst = Rvalue.Use(move _src)` of
a `.Memory`-ABI aggregate (`srcIdx ≠ dstIdx`), routed through
`annealStructMemCopyOp` (`forceAllocation` + whole-allocation `mem_copy`
preserving raw bytes, leaf values, and uninitialized padding bytes). -/
inductive WellTypedLM2_2UseAssignMemStruct
    (body : CapturedMir)
    (env : StructTypeEnv)
    (stEnv : LM2_2StaticEnv)
    (dstIdx : Local)
    (isMove : Bool)
    (srcIdx : Local) : Prop where
  | mk
      (decl srcDecl : LocalDecl)
      (fields : List StructFieldDesc)
      (paths : List (List ProjectionElem))
      (topOffsets : Array Miri.ABI.Size)
      (memoryIndex : Array Nat)
      (src_ne_dst : srcIdx ≠ dstIdx)
      (dst_lookup : get? body.localDecls dstIdx = some decl)
      (src_lookup : get? body.localDecls srcIdx = some srcDecl)
      (ty_eq : srcDecl.ty = decl.ty)
      (env_lookup : env decl.ty = some (fields, paths))
      (src_state : srcIdx ∈ stEnv.initLocals ∨ srcIdx ∈ stEnv.immLocals)
      (mem_repr : (translateTy decl.ty body.layouts).layout.backendRepr = .Memory (sized := true))
      (arb_fields : (translateTy decl.ty body.layouts).layout.fields =
        .Arbitrary topOffsets memoryIndex)
      (nz_size : (translateTy decl.ty body.layouts).layout.size ≠ Miri.ABI.Size.ZERO)
      (size_lt_4g : (translateTy decl.ty body.layouts).layout.size.bytes.toNat < 2 ^ 32)
      (is_sized : (translateTy decl.ty body.layouts).layout.isSized = true)
      (align_le : (translateTy decl.ty body.layouts).layout.align.abi.pow2 ≤ 29) :
      WellTypedLM2_2UseAssignMemStruct body env stEnv dstIdx isMove srcIdx

/-- Whole-value `.Memory` struct copy/move simulation
(`_dst = Rvalue.Use(copy _src)` and `_dst = Rvalue.Use(move _src)`):
* dead source, uninitialized/moved-from immediate source
  (`LocalRelLM2_2.structUninitImm`), or dead destination raises UB on both
  sides;
* uninitialized immediate destination (`LocalRelLM2_2.structUninitImm`) forces a
  fresh stack allocation via `Miri.Interpreter.forceAllocation` (`k_bud + 1 → k_bud`),
  copies raw bytes and `InitMask` via `annealStructMemCopyOp`, and establishes
  `StructMemPlaceRel` on `_dst` with every padding byte preserved as `.uninit`;
* indirect destination (`UninitStructMemPlaceRel` or `StructMemPlaceRel`) copies
  into `_dst`'s existing disjoint allocation (`srcId ≠ destId`), establishing
  `StructMemPlaceRel` on `_dst` with every padding byte preserved as `.uninit`;
* when `isMove = true`, `_src` becomes `.uninit` / `.live (.immediate .uninit)`. -/
theorem step_assign_use_memory_struct_lm2_2_simulation
    {body : CapturedMir} {env : StructTypeEnv} {stEnv : LM2_2StaticEnv} {k_bud : Nat}
    {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_2 body env stEnv (k_bud + 1) s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx : Local} {isMove : Bool} {srcIdx : Local} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.use (mkPlaceOperand isMove ⟨srcIdx, .nil⟩)), span⟩)
    (hwt : WellTypedLM2_2UseAssignMemStruct body env stEnv dstIdx isMove srcIdx) :
    StepRelLM2_2 body env
      (useStructPostStaticEnv stEnv dstIdx (mkPlaceOperand isMove ⟨srcIdx, .nil⟩))
      k_bud m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  cases hwt with
  | mk decl srcDecl fields paths topOffsets memoryIndex
      hne_sd hdecl hsrc_decl hty_eq henv hsrc_state hmem_repr harb hnz_sz
      hsz4g hsized halign_le =>
    rcases srcDecl with ⟨srcMut, srcTy, srcName⟩
    dsimp only at hty_eq
    subst hty_eq
    rcases hstate with
      ⟨topFrame, hframes, hretCont, ⟨retLay, hretPlace⟩, hframe,
        hinit_env, himm_env, hsupply, hcal, hstack, hbor, hprot, hcaller, hdisj⟩
    rw [stepMirFn_eq_of_not_other body s hcal hphase]
    simp only [hbb, hstmt]
    let wholeLay := translateTy decl.ty body.layouts
    let op := mkPlaceOperand isMove ⟨srcIdx, .nil⟩
    have huses_mem :
        usesStructMemCopyDest ⟨.local 0 dstIdx none topFrame.localsIdentity, wholeLay⟩ = true := by
      unfold usesStructMemCopyDest
      dsimp only [wholeLay]
      rw [hmem_repr, harb]
      exact bne_iff_ne.mpr hnz_sz
    obtain ⟨slot_dst, mls_dst0, hlt_dst0, _, hslot_dst, _, hmls_dst_eq0, hloc_dst0⟩ :=
      hframe.lookup_local hdecl
    have hcache_dst0 : ∀ l, (topFrame.locals[dstIdx]'hlt_dst0).layout = some l →
        l = wholeLay := by
      rw [hmls_dst_eq0]; exact hloc_dst0.layout_eq
    have hevalPlace := annealEvalPlace_unprojected hframes hlt_dst0 hdecl hcache_dst0
    have hm_eval := evalStatement_assign_use_mem_eq (dst := ⟨dstIdx, .nil⟩)
      (op := op) (span := span) hevalPlace huses_mem
    let tf₀ := cacheFrameLocalLayout topFrame dstIdx hlt_dst0 wholeLay
    have hfr₀ : FrameRelLM2_2 body env m.machine s.frame tf₀ :=
      hframe.cache_local_layout hdecl hlt_dst0
    have hdisj₀ : MemoryAllocDisjoint tf₀ :=
      MemoryAllocDisjoint_cacheFrameLocalLayout hdisj hlt_dst0 wholeLay
    have himm_env₀ : ∀ j ∈ stEnv.immLocals, ∀ mp l,
        tf₀.locals[j]? ≠ some ⟨.live (.indirect mp), l⟩ := by
      intro j hj mp l
      dsimp only [tf₀, cacheFrameLocalLayout]
      by_cases hij : dstIdx = j
      · subst hij
        rw [Array.getElem?_set_self hlt_dst0, hmls_dst_eq0]
        intro heq; injection heq with hls
        rcases mls_dst0 with ⟨val0, lay0⟩
        injection hls with hv_eq _; subst hv_eq
        exact himm_env dstIdx hj mp lay0
          (by rw [Array.getElem?_eq_getElem hlt_dst0, hmls_dst_eq0])
      · rw [Array.getElem?_set_ne _ hij]; exact himm_env j hj mp l
    obtain ⟨slot_s, mls_s, hlt_src0, hlt_src_af, hslot_s, hmls_s?, hmls_s_eq, hloc_s⟩ :=
      hfr₀.lookup_local hsrc_decl
    have hcache_s : ∀ l, mls_s.layout = some l → l = wholeLay :=
      hloc_s.layout_eq
    cases hloc_s with
    | base _ _ henv_none _ =>
      rw [henv] at henv_none; cases henv_none
    | structUninitInd _ _ srcMp_u c_s _ _ _ =>
      rcases hsrc_state with hsrc_init | hsrc_imm
      · exact False.elim (hinit_env srcIdx hsrc_init hslot_s)
      · exact False.elim (himm_env₀ srcIdx hsrc_imm srcMp_u c_s hmls_s?)
    | structUninitImm _ _ c_s _ _ =>
      have ha_ub : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.use op), span⟩
          body.localDecls body.layouts = MirStepNode.fail .ub := by
        unfold evalStmt; dsimp only
        rw [evalRvalue_use_nil_borrows _ _ _ hbor, hcaller]
        cases isMove <;> simp [op, mkPlaceOperand, evalOperand, hslot_s]
      obtain ⟨m_err, hm_op_ok⟩ :
          ∃ m_err,
            annealEvalOperand body.localDecls body.layouts (translateOperand op) (some wholeLay)
              { m with stack := ⟨#[tf₀]⟩ } =
            .ok ⟨.immediate .uninit, wholeLay⟩ m_err := by
        cases isMove with
        | false =>
          exact ⟨_, annealEvalOperand_copy_live (decl := ⟨srcMut, decl.ty, srcName⟩)
            rfl hlt_src0 hsrc_decl hmls_s_eq hcache_s⟩
        | true =>
          exact ⟨_, annealEvalOperand_move_live (decl := ⟨srcMut, decl.ty, srcName⟩)
            rfl hlt_src0 hsrc_decl hmls_s_eq hcache_s⟩
      have hm_ub :
          Miri.Interpreter.Step.evalStatement (annealStepHooks body.localDecls body.layouts) ()
            (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.use op), span⟩) m =
          (m_err, .error (.undefinedBehavior "read of uninitialized local")) := by
        dsimp only [wholeLay, tf₀] at hm_op_ok
        rw [hm_eval]; unfold Miri.Interpreter.runRvalue
        rw [EStateM.bind_eq_ok hm_op_ok]
        rfl
      rw [ha_ub, miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq hbb hstmt hm_ub]
      exact .ub _ _
    | structImm _ _ _ _ _ _ _ himm_s =>
      cases himm_s with
      | scalarWrapper _ _ _ _ _ _ _ hrepr _ _ _ _ _ _ _ _ _ _ =>
        rw [hmem_repr] at hrepr; cases hrepr
      | scalarPair _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hrepr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
        rw [hmem_repr] at hrepr; cases hrepr
    | structDead _ _ c_s _ _ =>
      have ha_ub : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.use op), span⟩
          body.localDecls body.layouts = MirStepNode.fail .ub := by
        unfold evalStmt; dsimp only
        rw [evalRvalue_use_nil_borrows _ _ _ hbor, hcaller]
        cases isMove <;> simp [op, mkPlaceOperand, evalOperand, hslot_s]
      obtain ⟨m_err, hm_op_err⟩ :
          ∃ m_err,
            annealEvalOperand body.localDecls body.layouts (translateOperand op) (some wholeLay)
              { m with stack := ⟨#[tf₀]⟩ } =
            .error (.undefinedBehavior "read of dead local") m_err := by
        cases isMove with
        | false =>
          exact ⟨_, annealEvalOperand_copy_dead rfl hlt_src0 hsrc_decl hmls_s_eq hcache_s⟩
        | true =>
          exact ⟨_, annealEvalOperand_move_dead rfl hlt_src0 hsrc_decl hmls_s_eq hcache_s⟩
      have hm_ub :
          Miri.Interpreter.Step.evalStatement (annealStepHooks body.localDecls body.layouts) ()
            (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.use op), span⟩) m =
          (m_err, .error (.undefinedBehavior "read of dead local")) := by
        dsimp only [wholeLay, tf₀] at hm_op_err
        rw [hm_eval]; unfold Miri.Interpreter.runRvalue
        rw [EStateM.bind_eq_error hm_op_err]
      rw [ha_ub, miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq hbb hstmt hm_ub]
      exact .ub _ _
    | structInd fs_s ps_s rootVal srcMp c_s henv_s _ hsmpr_d =>
      have hfp_s := henv.symm.trans henv_s
      injection hfp_s with hfp_s'; injection hfp_s' with hfs_s hps_s; subst hfs_s hps_s
      rcases hsmpr_d with
        ⟨srcId, _, srcBase, srcLocal, words_s, hvalid_s, hplen_s, hagg_s, hleaf_s,
          hprov_s, _, _, hlive_s, hbase_s, hptr_s, _, _, _, hbs_s,
          hlen_s, hpmap_s, hmask_s, hbits_s, hfields_s, hpad_s⟩
      have htf₀_dst : tf₀.locals[dstIdx]? = some ⟨mls_dst0.value, some wholeLay⟩ := by
        dsimp only [tf₀, cacheFrameLocalLayout]
        rw [Array.getElem?_set_self hlt_dst0, hmls_dst_eq0]
      have hsrc_ne_destId :
          ∀ (destMp : Miri.Interpreter.MemPlace AnnealProv) (destId : Miri.Memory.AllocId),
            mls_dst0.value = .live (.indirect destMp) →
            ∀ tag, destMp.ptr.provenance = some (.concrete destId tag) →
            srcId ≠ destId := by
        intro destMp destId hv_d tag_d hprov_d
        have hd_get : tf₀.locals[dstIdx]? = some ⟨.live (.indirect destMp), some wholeLay⟩ := by
          rw [htf₀_dst, hv_d]
        have hne_prov := hdisj₀ srcIdx dstIdx srcMp destMp c_s (some wholeLay)
          hne_sd hmls_s? hd_get
        rw [hprov_s, hprov_d] at hne_prov
        intro heq; subst heq; exact hne_prov rfl
      -- Evaluate `op` (`copy _src` or `move _src`) uniformly into `(locals₁, tf₁)`.
      obtain ⟨locals₁, tf₁, hev_op, hm_op, hfr₁, hdisj₁, hid₁, hrc₁, hrp₁, hsz₁,
          hdst_loc₁, hdst_tf₁?, hinit₁, himm₁⟩ :
          ∃ (locals₁ : List LocalSlot)
            (tf₁ : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit),
            evalOperand s.frame.locals op .nil s.memory.globals body.layouts .nil =
              .ok rootVal locals₁ ∧
            annealEvalOperand body.localDecls body.layouts (translateOperand op) (some wholeLay)
              { m with stack := ⟨#[tf₀]⟩ } =
              .ok ⟨.indirect srcMp, wholeLay⟩ { m with stack := ⟨#[tf₁]⟩ } ∧
            FrameRelLM2_2 body env m.machine { s.frame with locals := locals₁ } tf₁ ∧
            MemoryAllocDisjoint tf₁ ∧
            tf₁.localsIdentity = topFrame.localsIdentity ∧
            tf₁.returnContinuation = topFrame.returnContinuation ∧
            tf₁.returnPlace = topFrame.returnPlace ∧
            tf₁.locals.size = topFrame.locals.size ∧
            get? locals₁ dstIdx = some slot_dst ∧
            tf₁.locals[dstIdx]? = some ⟨mls_dst0.value, some wholeLay⟩ ∧
            (∀ j ∈ (operandPostStaticEnv stEnv op).initLocals, get? locals₁ j ≠ some .uninit) ∧
            (∀ j ∈ (operandPostStaticEnv stEnv op).immLocals, ∀ mp lay,
              tf₁.locals[j]? ≠ some ⟨.live (.indirect mp), lay⟩) := by
        cases isMove with
        | false =>
          let tf₁ := cacheFrameLocalLayout tf₀ srcIdx hlt_src0 wholeLay
          have hm_c := annealEvalOperand_copy_live (known := some wholeLay)
            (m := { m with stack := ⟨#[tf₀]⟩ }) rfl hlt_src0 hsrc_decl hmls_s_eq hcache_s
          refine ⟨s.frame.locals, tf₁,
            by change evalOperand s.frame.locals (.copy ⟨srcIdx, .nil⟩) .nil s.memory.globals body.layouts .nil = _
               simp [evalOperand, readProjectedValue, hslot_s],
            hm_c, hfr₀.cache_local_layout hsrc_decl hlt_src0,
            MemoryAllocDisjoint_cacheFrameLocalLayout hdisj₀ hlt_src0 _,
            rfl, rfl, rfl,
            by dsimp [tf₁, tf₀]; rw [cacheFrameLocalLayout_size, cacheFrameLocalLayout_size],
            hslot_dst,
            by dsimp only [tf₁, cacheFrameLocalLayout]; rw [Array.getElem?_set_ne _ hne_sd]; exact htf₀_dst,
            hinit_env, ?_⟩
          intro j hj mp l
          change j ∈ (operandPostStaticEnv stEnv (.copy ⟨srcIdx, .nil⟩)).immLocals at hj
          dsimp [operandPostStaticEnv] at hj
          dsimp only [tf₁, cacheFrameLocalLayout]
          by_cases hij : srcIdx = j
          · subst hij
            rw [Array.getElem?_set_self hlt_src0]
            intro heq; injection heq with hls; injection hls with hv_eq _
            exact himm_env₀ srcIdx hj srcMp c_s hmls_s?
          · rw [Array.getElem?_set_ne _ hij]; exact himm_env₀ j hj mp l
        | true =>
          let tf_c := cacheFrameLocalLayout tf₀ srcIdx hlt_src0 wholeLay
          have hlt_c : srcIdx < tf_c.locals.size := by
            dsimp [tf_c]; rw [cacheFrameLocalLayout_size]; exact hlt_src0
          let tf₁ := deinitFrameLocal tf_c srcIdx hlt_c
          have hm_m := annealEvalOperand_move_live (known := some wholeLay)
            (m := { m with stack := ⟨#[tf₀]⟩ }) rfl hlt_src0 hsrc_decl hmls_s_eq hcache_s
          have hc_some : ∀ l ∈ (tf_c.locals[srcIdx]'hlt_c).layout,
              l = wholeLay := by
            intro l hl
            have hget_c : tf_c.locals[srcIdx]? = some (tf_c.locals[srcIdx]'hlt_c) :=
              Array.getElem?_eq_getElem hlt_c
            have hc_eq : tf_c.locals[srcIdx]? =
                some ⟨.live (.indirect srcMp), some wholeLay⟩ := by
              dsimp only [tf_c, cacheFrameLocalLayout]
              rw [Array.getElem?_set_self hlt_src0, hmls_s_eq]
            rw [hget_c] at hc_eq; injection hc_eq with heq_ls
            rw [heq_ls] at hl
            exact (Option.some.inj (Option.mem_def.mp hl)).symm
          have hfr₁_exc := (FrameRelLM2_2Except.of_frameRel none
            (hfr₀.cache_local_layout hsrc_decl hlt_src0)).update_local
            hsrc_decl .uninit (.live (.immediate .uninit))
            (fun _ => .structUninitImm fields paths _ henv hc_some)
          refine ⟨s.frame.locals.set srcIdx .uninit, tf₁,
            by change evalOperand s.frame.locals (.move ⟨srcIdx, .nil⟩) .nil s.memory.globals body.layouts .nil = _
               unfold evalOperand; dsimp only; rw [hslot_s]; dsimp only; rw [set?_eq_some_set hlt_src_af],
            hm_m, hfr₁_exc.toFrameRel,
            MemoryAllocDisjoint_deinitFrameLocal
              (MemoryAllocDisjoint_cacheFrameLocalLayout hdisj₀ hlt_src0 _) hlt_c,
            rfl, rfl, rfl,
            by dsimp [tf₁, deinitFrameLocal, tf_c, tf₀]; rw [Array.size_set, cacheFrameLocalLayout_size, cacheFrameLocalLayout_size],
            by dsimp [get?]; rw [List.getElem?_set_ne hne_sd, ← get?_eq_getElem?]; exact hslot_dst,
            by dsimp only [tf₁, deinitFrameLocal]; rw [Array.getElem?_set_ne _ hne_sd]
               dsimp only [tf_c, cacheFrameLocalLayout]; rw [Array.getElem?_set_ne _ hne_sd]; exact htf₀_dst,
            ?_, ?_⟩
          · intro j hj
            change j ∈ (operandPostStaticEnv stEnv (.move ⟨srcIdx, .nil⟩)).initLocals at hj
            dsimp [operandPostStaticEnv] at hj
            rw [List.mem_filter] at hj
            have hij : srcIdx ≠ j := fun h => by subst h; simp at hj
            dsimp [get?]
            rw [List.getElem?_set_ne hij, ← get?_eq_getElem?]
            exact hinit_env j hj.1
          · intro j hj mp l
            change j ∈ (operandPostStaticEnv stEnv (.move ⟨srcIdx, .nil⟩)).immLocals at hj
            dsimp [operandPostStaticEnv] at hj
            by_cases hij : srcIdx = j
            · subst hij
              dsimp only [tf₁, deinitFrameLocal]
              rw [Array.getElem?_set_self hlt_c]; nofun
            · dsimp only [tf₁, deinitFrameLocal]; rw [Array.getElem?_set_ne _ hij]
              dsimp only [tf_c, cacheFrameLocalLayout]; rw [Array.getElem?_set_ne _ hij]
              rcases List.mem_cons.mp hj with rfl | hj_old
              · exact False.elim (hij rfl)
              · exact himm_env₀ j hj_old mp l
      have hlt_dst1 : dstIdx < tf₁.locals.size := by rw [hsz₁]; exact hlt_dst0
      have hdst_tf₁ : tf₁.locals[dstIdx]'hlt_dst1 = ⟨mls_dst0.value, some wholeLay⟩ := by
        rw [Array.getElem?_eq_getElem hlt_dst1] at hdst_tf₁?
        exact Option.some.inj hdst_tf₁?
      obtain ⟨hlt_af₁, _⟩ := List.getElem?_eq_some_iff.mp (get?_eq_getElem? locals₁ dstIdx ▸ hdst_loc₁)
      have hfr₁_excl : FrameRelLM2_2Except body env (some dstIdx) m.machine
          { s.frame with locals := locals₁ } tf₁ :=
        ⟨hfr₁.body_eq, hfr₁.location_eq, hfr₁.af_locals_len, hfr₁.mf_locals_size,
          fun i d sl ml _ hd hs hm => hfr₁.locals_rel i d sl ml hd hs hm⟩
      have ha_ok_of : slot_dst ≠ .dead →
          evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.use op), span⟩
            body.localDecls body.layouts =
          MirStepNode.step (advanceStmt s (locals₁.set dstIdx (.init rootVal)) s.memory) := by
        intro hnot_dead
        unfold evalStmt; dsimp only
        rw [evalRvalue_use_nil_borrows _ _ _ hbor, hcaller, hev_op]; dsimp only
        rw [hprot, hbor, hdst_loc₁]
        cases slot_dst with
        | dead => exact absurd rfl hnot_dead
        | uninit | init _ =>
          dsimp only; rw [set?_eq_some_set hlt_af₁]
          apply congrArg (fun mem =>
            MirStepNode.step (advanceStmt s (locals₁.set dstIdx (.init rootVal)) mem))
          revert hbor hprot; generalize s.memory = mem; rintro hbor hprot
          cases mem; dsimp only at hbor hprot ⊢; subst hbor hprot; rfl
      have hinit_post : ∀ j ∈ (useStructPostStaticEnv stEnv dstIdx op).initLocals,
          get? (locals₁.set dstIdx (.init rootVal)) j ≠ some .uninit := by
        intro j hj
        dsimp only [useStructPostStaticEnv] at hj
        dsimp only [get?]
        by_cases hjd : dstIdx = j
        · subst hjd; rw [List.getElem?_set_self hlt_af₁]; nofun
        · rw [List.getElem?_set_ne hjd, ← get?_eq_getElem?]
          rcases List.mem_cons.mp hj with rfl | hj_old
          · exact False.elim (hjd rfl)
          · exact hinit₁ j hj_old
      -- Case split on the destination local state before the copy.
      have hdst_cases :
          (slot_dst = .dead ∧ mls_dst0.value = .dead) ∨
          (slot_dst = .uninit ∧ mls_dst0.value = .live (.immediate .uninit)) ∨
          (slot_dst ≠ .dead ∧ ∃ (tag : Miri.Memory.BorTag) (destMp : Miri.Interpreter.MemPlace AnnealProv)
            (destId : Miri.Memory.AllocId) (destBase : UInt64)
            (destLocal : AnnealLocalAlloc) (u : Nat)
            (hu_lt : u < m.machine.memory.live.size),
            mls_dst0.value = .live (.indirect destMp) ∧
            destMp.ptr.provenance = some (.concrete destId tag) ∧
            destMp.misaligned = none ∧
            destMp.metadata = .none ∧
            LiveAllocEntry m.machine.memory.live destId destLocal ∧
            m.machine.memory.live.findIdx? (fun (k, _) => k == destId) = some u ∧
            m.machine.memory.live[u]'hu_lt = (destId, destLocal) ∧
            m.machine.lookupBaseAddr destId = some destBase ∧
            destMp.ptr.offset = Miri.ABI.Size.ofBytes destBase ∧
            destBase.toNat + wholeLay.layout.size.bytes.toNat < 2 ^ 64 ∧
            destLocal.allocation.mutability = .Mut ∧
            destLocal.allocation.byteSize = wholeLay.layout.size ∧
            destMp.ptr.offset.isAligned wholeLay.layout.align.abi = .ok true) := by
        cases hloc_dst0 with
        | base _ _ henv_none _ => rw [henv] at henv_none; cases henv_none
        | structImm _ _ _ _ _ _ _ himm_d =>
          cases himm_d with
          | scalarWrapper _ _ _ _ _ _ _ hrepr _ _ _ _ _ _ _ _ _ _ =>
            rw [hmem_repr] at hrepr; cases hrepr
          | scalarPair _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hrepr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
            rw [hmem_repr] at hrepr; cases hrepr
        | structDead _ _ _ _ _ => exact Or.inl ⟨rfl, rfl⟩
        | structUninitImm _ _ _ _ _ => exact Or.inr (Or.inl ⟨rfl, rfl⟩)
        | structUninitInd _ _ destMp _ _ _ humpr =>
          rcases humpr with ⟨destId, tag_d, destBase, destLocal, _, hprov_d, hmis_d, hmeta_d,
            hlive_d, hbase_d, hptr_d, hovf_d, hmut_d, halign_d, hbs_d, _, _, _⟩
          obtain ⟨hfind_d, u, hu_lt, hfidx_d, hget_d⟩ := hlive_d
          exact Or.inr (Or.inr ⟨by nofun, tag_d, destMp, destId, destBase, destLocal, u, hu_lt,
            rfl, hprov_d, hmis_d, hmeta_d, ⟨hfind_d, u, hu_lt, hfidx_d, hget_d⟩,
            hfidx_d, hget_d, hbase_d, hptr_d, hovf_d, hmut_d, hbs_d, halign_d⟩)
        | structInd _ _ _ destMp _ _ _ hsmpr_old =>
          rcases hsmpr_old with ⟨destId, tag_d, destBase, destLocal, _, _, _, _, _,
            hprov_d, hmis_d, hmeta_d, hlive_d, hbase_d, hptr_d, hovf_d,
            hmut_d, halign_d, hbs_d, _, _, _, _, _, _⟩
          obtain ⟨hfind_d, u, hu_lt, hfidx_d, hget_d⟩ := hlive_d
          exact Or.inr (Or.inr ⟨by nofun, tag_d, destMp, destId, destBase, destLocal, u, hu_lt,
            rfl, hprov_d, hmis_d, hmeta_d, ⟨hfind_d, u, hu_lt, hfidx_d, hget_d⟩,
            hfidx_d, hget_d, hbase_d, hptr_d, hovf_d, hmut_d, hbs_d, halign_d⟩)
      rcases hdst_cases with ⟨hslot_dead, hv_dead⟩ | ⟨hslot_uninit, hv_uninit⟩ |
          ⟨hnot_dead, tag_d, destMp, destId, destBase, destLocal, u, hu_lt,
            hv_ind, hprov_d, hmis_d, hmeta_d, hlive_d, hfidx_d, hget_d,
            hbase_d, hptr_d, hovf_d, hmut_d, hbs_d, halign_d⟩
      · -- Dead destination: both sides raise UB.
        have ha_ub : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.use op), span⟩
            body.localDecls body.layouts = MirStepNode.fail .ub := by
          unfold evalStmt; dsimp only
          rw [evalRvalue_use_nil_borrows _ _ _ hbor, hcaller, hev_op]; dsimp only
          rw [hprot, hbor, hdst_loc₁, hslot_dead]
        rw [hv_dead] at hdst_tf₁
        have hcp_dead := annealStructMemCopyOp_dead_ub (ld := body.localDecls) (ly := body.layouts)
          (srcMp := srcMp) (srcLay := wholeLay) (wholeLay := wholeLay)
          (iden := topFrame.localsIdentity)
          (m := { m with stack := ⟨#[tf₁]⟩ }) rfl hlt_dst1 hdst_tf₁
        have hm_ub :
            Miri.Interpreter.Step.evalStatement (annealStepHooks body.localDecls body.layouts) ()
              (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.use op), span⟩) m =
            ({ m with stack := ⟨#[tf₁]⟩ }, .error (.undefinedBehavior "write to dead local")) := by
          have hm_op' := hm_op; have hcp_dead' := hcp_dead
          dsimp only [wholeLay, tf₀] at hm_op' hcp_dead'
          rw [hm_eval]; unfold Miri.Interpreter.runRvalue
          rw [EStateM.bind_eq_ok hm_op']; simp only [hcp_dead']
        rw [ha_ub, miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq hbb hstmt hm_ub]
        exact .ub _ _
      · -- Uninitialized immediate destination: force fresh stack allocation and copy.
        rw [hv_uninit] at hdst_tf₁
        obtain ⟨rawAlloc, htry, hbs0, _, hmut0, _, _⟩ :=
          tryNew_uninit_of_pow2_le_29 wholeLay.layout.size wholeLay.layout.align.abi halign_le
        obtain ⟨mem', newId, hres, _, hlive_eq, hfresh_old, hwm_next, hovf_all⟩ :=
          (hsupply.of_succ).reserve_step
        have hfresh : mem'.live.any (fun entry => entry.1 == newId) = false := by
          rw [hlive_eq]; exact hfresh_old
        have hcp_ok := annealStructMemCopyOp_uninitImm_ok
          (ld := body.localDecls) (ly := body.layouts)
          (srcLay := wholeLay) (iden := topFrame.localsIdentity)
          (m := { m with stack := ⟨#[tf₁]⟩ })
          rfl hlt_dst1 hdst_tf₁ hsized htry hbs0 hmut0 hres hfresh
          hprov_s hbase_s hptr_s hlive_s hbs_s
        have hsmpr_new := StructMemPlaceRel.of_copy_fresh
          (mach := m.machine) (mem' := mem') (id := newId)
          hvalid_s hplen_s hagg_s hleaf_s hbs_s hlen_s hpmap_s hmask_s
          hbits_s hfields_s hpad_s hfresh (hovf_all _ hsz4g) halign_le
        have hm_ok :
            Miri.Interpreter.Step.evalStatement (annealStepHooks body.localDecls body.layouts) ()
              (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.use op), span⟩) m =
            (⟨⟨#[{ tf₁ with
                locals := tf₁.locals.set dstIdx
                  ⟨.live (.indirect (stackAllocPlace newId)), some wholeLay⟩ hlt_dst1 }]⟩,
              stackAllocMachine m.machine mem' newId
                (copyWholeStructAllocation srcLocal.allocation none)⟩, .ok ()) := by
          have hm_op' := hm_op; have hcp_ok' := hcp_ok
          dsimp only [wholeLay, tf₀] at hm_op' hcp_ok' ⊢
          rw [hm_eval]; unfold Miri.Interpreter.runRvalue
          rw [EStateM.bind_eq_ok hm_op']; simp only [hcp_ok']
        have hfr_end : FrameRelLM2_2 body env
            (stackAllocMachine m.machine mem' newId
              (copyWholeStructAllocation srcLocal.allocation none))
            { s.frame with locals := locals₁.set dstIdx (.init rootVal) }
            { tf₁ with
              locals := tf₁.locals.set dstIdx
                ⟨.live (.indirect (stackAllocPlace newId)), some wholeLay⟩ hlt_dst1 } := by
          have hex := hfr₁_excl.of_stackAlloc_set_excl
            (alloc := copyWholeStructAllocation srcLocal.allocation none)
            (hlt := hlt_dst1) hres
            ⟨.live (.indirect (stackAllocPlace newId)), some wholeLay⟩
          exact hex.fill_excluded hdecl hlt_af₁
            (by dsimp only; rw [Array.size_set]; exact hlt_dst1)
            (by dsimp only; exact Array.getElem_set_self hlt_dst1)
            (.structInd fields paths rootVal (stackAllocPlace newId) (some wholeLay) henv
              (fun _ hl => (Option.some.inj (Option.mem_def.mp hl)).symm) hsmpr_new)
        rw [ha_ok_of (by rw [hslot_uninit]; nofun),
          miri_step_at_statement_ok _ hframes hframe.body_eq hframe.location_eq hbb hstmt
            hm_ok rfl hfr_end.location_eq]
        refine .step _ _ ?_
        refine .mk _ rfl (hrc₁.trans hretCont)
          ⟨retLay, by dsimp; rw [hrp₁, hretPlace, hid₁]⟩
          hfr_end.step_pc hinit_post ?_
          (Or.inr (hwm_next _))
          hcal hstack hbor hprot hcaller
          (MemoryAllocDisjoint_set_fresh_stackAlloc hfr₁_excl hdisj₁ hfresh_old hlt_dst1)
        intro j hj mp' lay'
        dsimp only [useStructPostStaticEnv] at hj
        rw [List.mem_filter] at hj
        have hjd : dstIdx ≠ j := fun h => by subst h; simp at hj
        dsimp only
        rw [Array.getElem?_set_ne _ hjd]
        exact himm₁ j hj.1 mp' lay'
      · -- Indirect destination: copy into existing disjoint stack allocation.
        rw [hv_ind] at hdst_tf₁
        have hne_id := hsrc_ne_destId destMp destId hv_ind tag_d hprov_d
        have hcp_ok := annealStructMemCopyOp_indirect_ok
          (ld := body.localDecls) (ly := body.layouts)
          (srcLay := wholeLay) (iden := topFrame.localsIdentity)
          (m := { m with stack := ⟨#[tf₁]⟩ })
          rfl hlt_dst1 hdst_tf₁ hne_id
          hprov_s hbase_s hptr_s hlive_s hbs_s
          hprov_d hbase_d hptr_d hu_lt hfidx_d hget_d hbs_d hmut_d
        have hsmpr_new := StructMemPlaceRel.of_copy_overwrite
          (mach := m.machine)
          hvalid_s hplen_s hagg_s hleaf_s hbs_s hlen_s hpmap_s hmask_s
          hbits_s hfields_s hpad_s
          hprov_d hmis_d hmeta_d hlive_d hu_lt hfidx_d hbase_d hptr_d hovf_d halign_d
        have hm_ok :
            Miri.Interpreter.Step.evalStatement (annealStepHooks body.localDecls body.layouts) ()
              (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.use op), span⟩) m =
            (⟨⟨#[tf₁]⟩,
              updateAllocMachine m.machine u destId destLocal.kind
                (copyWholeStructAllocation srcLocal.allocation destLocal.allocation.extra)⟩,
             .ok ()) := by
          have hm_op' := hm_op; have hcp_ok' := hcp_ok
          dsimp only [wholeLay, tf₀] at hm_op' hcp_ok' ⊢
          rw [hm_eval]; unfold Miri.Interpreter.runRvalue
          rw [EStateM.bind_eq_ok hm_op']; simp only [hcp_ok']
        have hfr_end : FrameRelLM2_2 body env
            (updateAllocMachine m.machine u destId destLocal.kind
              (copyWholeStructAllocation srcLocal.allocation destLocal.allocation.extra))
            { s.frame with locals := locals₁.set dstIdx (.init rootVal) } tf₁ := by
          have hex := hfr₁_excl.of_updateAlloc_excl (kind := destLocal.kind)
            (alloc' := copyWholeStructAllocation srcLocal.allocation destLocal.allocation.extra)
            hdisj₁ hdst_tf₁ hprov_d hu_lt hget_d
          exact hex.fill_excluded hdecl hlt_af₁ hlt_dst1 hdst_tf₁
            (.structInd fields paths rootVal destMp (some wholeLay) henv
              (fun _ hl => (Option.some.inj (Option.mem_def.mp hl)).symm) hsmpr_new)
        rw [ha_ok_of hnot_dead,
          miri_step_at_statement_ok _ hframes hframe.body_eq hframe.location_eq hbb hstmt
            hm_ok rfl hfr_end.location_eq]
        refine .step _ _ ?_
        refine .mk _ rfl (hrc₁.trans hretCont)
          ⟨retLay, by dsimp; rw [hrp₁, hretPlace, hid₁]⟩
          hfr_end.step_pc hinit_post ?_
          ((hsupply.mono (Nat.le_succ k_bud)).of_updateAlloc hu_lt hget_d)
          hcal hstack hbor hprot hcaller hdisj₁
        intro j hj mp' lay'
        dsimp only [useStructPostStaticEnv] at hj
        rw [List.mem_filter] at hj
        exact himm₁ j hj.1 mp' lay'

/-- 100% syntactic typing predicate for self-move `_idx = Rvalue.Use(move _idx)`
on a `.Memory`-ABI aggregate local. Unlike self-copy (`_idx = copy _idx`), which
raises `copyRangesOverlap` UB in Miri because `src` and `dest` alias the same
live stack allocation, self-move first deinitializes `_idx` to
`.live (.immediate .uninit)` during `evalOperand`, after which `forceAllocation`
allocates a fresh stack allocation `newId ≠ srcId` and copies `srcId → newId`
in lockstep with Anneal. -/
inductive WellTypedLM2_2SelfMoveMemStruct
    (body : CapturedMir)
    (env : StructTypeEnv)
    (stEnv : LM2_2StaticEnv)
    (idx : Local) : Prop where
  | mk
      (decl : LocalDecl)
      (fields : List StructFieldDesc)
      (paths : List (List ProjectionElem))
      (topOffsets : Array Miri.ABI.Size)
      (memoryIndex : Array Nat)
      (decl_lookup : get? body.localDecls idx = some decl)
      (env_lookup : env decl.ty = some (fields, paths))
      (src_state : idx ∈ stEnv.initLocals ∨ idx ∈ stEnv.immLocals)
      (mem_repr : (translateTy decl.ty body.layouts).layout.backendRepr = .Memory (sized := true))
      (arb_fields : (translateTy decl.ty body.layouts).layout.fields =
        .Arbitrary topOffsets memoryIndex)
      (nz_size : (translateTy decl.ty body.layouts).layout.size ≠ Miri.ABI.Size.ZERO)
      (size_lt_4g : (translateTy decl.ty body.layouts).layout.size.bytes.toNat < 2 ^ 32)
      (is_sized : (translateTy decl.ty body.layouts).layout.isSized = true)
      (align_le : (translateTy decl.ty body.layouts).layout.align.abi.pow2 ≤ 29) :
      WellTypedLM2_2SelfMoveMemStruct body env stEnv idx

/-- Lockstep simulation of self-move `_idx = Rvalue.Use(move _idx)` on a
`.Memory`-ABI aggregate local:
* dead or uninitialized/moved-from immediate `_idx` raises UB on both sides;
* initialized indirect `_idx` (`StructMemPlaceRel` at `srcId`) deinitializes
  `_idx` on `.Move`, allocates a fresh stack allocation `newId ≠ srcId` via
  `forceAllocation`, copies raw bytes and `InitMask` via `annealStructMemCopyOp`,
  and re-establishes `StructMemPlaceRel` with all alignment padding bytes `.uninit`. -/
theorem step_assign_self_move_memory_struct_lm2_2_simulation
    {body : CapturedMir} {env : StructTypeEnv} {stEnv : LM2_2StaticEnv} {k_bud : Nat}
    {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_2 body env stEnv (k_bud + 1) s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {idx : Local} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨idx, .nil⟩ (.use (.move ⟨idx, .nil⟩)), span⟩)
    (hwt : WellTypedLM2_2SelfMoveMemStruct body env stEnv idx) :
    StepRelLM2_2 body env
      (useStructPostStaticEnv stEnv idx (.move ⟨idx, .nil⟩))
      k_bud m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  cases hwt with
  | mk decl fields paths topOffsets memoryIndex
      hdecl henv hsrc_state hmem_repr harb hnz_sz hsz4g hsized halign_le =>
    rcases hstate with
      ⟨topFrame, hframes, hretCont, ⟨retLay, hretPlace⟩, hframe,
        hinit_env, himm_env, hsupply, hcal, hstack, hbor, hprot, hcaller, hdisj⟩
    rw [stepMirFn_eq_of_not_other body s hcal hphase]
    simp only [hbb, hstmt]
    let wholeLay := translateTy decl.ty body.layouts
    let op : MirAst.Operand := .move ⟨idx, .nil⟩
    have huses_mem :
        usesStructMemCopyDest ⟨.local 0 idx none topFrame.localsIdentity, wholeLay⟩ = true := by
      unfold usesStructMemCopyDest
      dsimp only [wholeLay]
      rw [hmem_repr, harb]
      exact bne_iff_ne.mpr hnz_sz
    obtain ⟨slot0, mls0, hlt0, hlt_af0, hslot0, _, hmls_eq0, hloc0⟩ :=
      hframe.lookup_local hdecl
    have hcache0 : ∀ l, (topFrame.locals[idx]'hlt0).layout = some l → l = wholeLay := by
      rw [hmls_eq0]; exact hloc0.layout_eq
    have hevalPlace := annealEvalPlace_unprojected hframes hlt0 hdecl hcache0
    have hm_eval := evalStatement_assign_use_mem_eq (dst := ⟨idx, .nil⟩)
      (op := op) (span := span) hevalPlace huses_mem
    let tf₀ := cacheFrameLocalLayout topFrame idx hlt0 wholeLay
    have hfr₀ : FrameRelLM2_2 body env m.machine s.frame tf₀ :=
      hframe.cache_local_layout hdecl hlt0
    have hdisj₀ : MemoryAllocDisjoint tf₀ :=
      MemoryAllocDisjoint_cacheFrameLocalLayout hdisj hlt0 wholeLay
    have hlt_tf₀ : idx < tf₀.locals.size := by
      dsimp [tf₀]; rw [cacheFrameLocalLayout_size]; exact hlt0
    have htf₀_self : tf₀.locals[idx]'hlt_tf₀ = ⟨mls0.value, some wholeLay⟩ := by
      have h? : tf₀.locals[idx]? = some ⟨mls0.value, some wholeLay⟩ := by
        dsimp only [tf₀, cacheFrameLocalLayout]
        rw [Array.getElem?_set_self hlt0, hmls_eq0]
      rw [Array.getElem?_eq_getElem hlt_tf₀] at h?
      exact Option.some.inj h?
    have hcache_tf₀ : ∀ l, (⟨mls0.value, some wholeLay⟩ :
        Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout).layout = some l →
        l = wholeLay := fun _ h => (Option.some.inj h).symm
    cases hloc0 with
    | base _ _ henv_none _ =>
      rw [henv] at henv_none; cases henv_none
    | structUninitInd _ _ srcMp_u c_s _ _ _ =>
      rcases hsrc_state with hsrc_init | hsrc_imm
      · exact False.elim (hinit_env idx hsrc_init hslot0)
      · exact False.elim (himm_env idx hsrc_imm srcMp_u c_s
          (by rw [Array.getElem?_eq_getElem hlt0, hmls_eq0]))
    | structImm _ _ _ _ _ _ _ himm_s =>
      cases himm_s with
      | scalarWrapper _ _ _ _ _ _ _ hrepr _ _ _ _ _ _ _ _ _ _ =>
        rw [hmem_repr] at hrepr; cases hrepr
      | scalarPair _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hrepr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
        rw [hmem_repr] at hrepr; cases hrepr
    | structUninitImm _ _ _ _ _ =>
      have ha_ub : evalStmt s ⟨.assign ⟨idx, .nil⟩ (.use op), span⟩
          body.localDecls body.layouts = MirStepNode.fail .ub := by
        unfold evalStmt; dsimp only
        rw [evalRvalue_use_nil_borrows _ _ _ hbor, hcaller]
        simp [op, evalOperand, hslot0]
      obtain ⟨m_err, hm_op_ok⟩ :
          ∃ m_err,
            annealEvalOperand body.localDecls body.layouts (translateOperand op) (some wholeLay)
              { m with stack := ⟨#[tf₀]⟩ } =
            .ok ⟨.immediate .uninit, wholeLay⟩ m_err :=
        ⟨_, annealEvalOperand_move_live (known := some wholeLay)
          (m := { m with stack := ⟨#[tf₀]⟩ }) rfl hlt_tf₀ hdecl htf₀_self hcache_tf₀⟩
      have hm_ub :
          Miri.Interpreter.Step.evalStatement (annealStepHooks body.localDecls body.layouts) ()
            (translateStmt ⟨.assign ⟨idx, .nil⟩ (.use op), span⟩) m =
          (m_err, .error (.undefinedBehavior "read of uninitialized local")) := by
        dsimp only [wholeLay, tf₀] at hm_op_ok
        rw [hm_eval]; unfold Miri.Interpreter.runRvalue
        rw [EStateM.bind_eq_ok hm_op_ok]; rfl
      rw [ha_ub, miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq hbb hstmt hm_ub]
      exact .ub _ _
    | structDead _ _ _ _ _ =>
      have ha_ub : evalStmt s ⟨.assign ⟨idx, .nil⟩ (.use op), span⟩
          body.localDecls body.layouts = MirStepNode.fail .ub := by
        unfold evalStmt; dsimp only
        rw [evalRvalue_use_nil_borrows _ _ _ hbor, hcaller]
        simp [op, evalOperand, hslot0]
      obtain ⟨m_err, hm_op_err⟩ :
          ∃ m_err,
            annealEvalOperand body.localDecls body.layouts (translateOperand op) (some wholeLay)
              { m with stack := ⟨#[tf₀]⟩ } =
            .error (.undefinedBehavior "read of dead local") m_err :=
        ⟨_, annealEvalOperand_move_dead (known := some wholeLay)
          (m := { m with stack := ⟨#[tf₀]⟩ }) rfl hlt_tf₀ hdecl htf₀_self hcache_tf₀⟩
      have hm_ub :
          Miri.Interpreter.Step.evalStatement (annealStepHooks body.localDecls body.layouts) ()
            (translateStmt ⟨.assign ⟨idx, .nil⟩ (.use op), span⟩) m =
          (m_err, .error (.undefinedBehavior "read of dead local")) := by
        dsimp only [wholeLay, tf₀] at hm_op_err
        rw [hm_eval]; unfold Miri.Interpreter.runRvalue
        rw [EStateM.bind_eq_error hm_op_err]
      rw [ha_ub, miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq hbb hstmt hm_ub]
      exact .ub _ _
    | structInd fs_s ps_s rootVal srcMp c_s henv_s _ hsmpr_s =>
      have hfp_s := henv.symm.trans henv_s
      injection hfp_s with hfp_s'; injection hfp_s' with hfs_s hps_s; subst hfs_s hps_s
      rcases hsmpr_s with
        ⟨srcId, _, srcBase, srcLocal, words_s, hvalid_s, hplen_s, hagg_s, hleaf_s,
          hprov_s, _, _, hlive_s, hbase_s, hptr_s, _, _, _, hbs_s,
          hlen_s, hpmap_s, hmask_s, hbits_s, hfields_s, hpad_s⟩
      let tf_c := cacheFrameLocalLayout tf₀ idx hlt_tf₀ wholeLay
      have hlt_c : idx < tf_c.locals.size := by
        dsimp [tf_c]; rw [cacheFrameLocalLayout_size]; exact hlt_tf₀
      let tf₁ := deinitFrameLocal tf_c idx hlt_c
      have hm_op := annealEvalOperand_move_live (known := some wholeLay)
        (m := { m with stack := ⟨#[tf₀]⟩ }) rfl hlt_tf₀ hdecl htf₀_self hcache_tf₀
      have hc_some : ∀ l ∈ (tf_c.locals[idx]'hlt_c).layout, l = wholeLay := by
        intro l hl
        have hget_c : tf_c.locals[idx]? = some (tf_c.locals[idx]'hlt_c) :=
          Array.getElem?_eq_getElem hlt_c
        have hc_eq : tf_c.locals[idx]? =
            some ⟨.live (.indirect srcMp), some wholeLay⟩ := by
          dsimp only [tf_c, cacheFrameLocalLayout]
          rw [Array.getElem?_set_self hlt_tf₀, htf₀_self]
        rw [hget_c] at hc_eq; injection hc_eq with heq_ls
        rw [heq_ls] at hl
        exact (Option.some.inj (Option.mem_def.mp hl)).symm
      have hfr₁ : FrameRelLM2_2 body env m.machine
          { s.frame with locals := s.frame.locals.set idx .uninit } tf₁ :=
        ((FrameRelLM2_2Except.of_frameRel none
          (hfr₀.cache_local_layout hdecl hlt_tf₀)).update_local
          hdecl .uninit (.live (.immediate .uninit))
          (fun _ => .structUninitImm fields paths _ henv hc_some)).toFrameRel
      have hdisj₁ : MemoryAllocDisjoint tf₁ :=
        MemoryAllocDisjoint_deinitFrameLocal
          (MemoryAllocDisjoint_cacheFrameLocalLayout hdisj₀ hlt_tf₀ _) hlt_c
      have hlt_dst1 : idx < tf₁.locals.size := by
        dsimp [tf₁, deinitFrameLocal]; rw [Array.size_set]; exact hlt_c
      have hdst_tf₁ : tf₁.locals[idx]'hlt_dst1 = ⟨.live (.immediate .uninit), some wholeLay⟩ := by
        have h? : tf₁.locals[idx]? = some ⟨.live (.immediate .uninit), some wholeLay⟩ := by
          dsimp only [tf₁, deinitFrameLocal]
          rw [Array.getElem?_set_self hlt_c]
          have hc_eq : tf_c.locals[idx]? = some ⟨.live (.indirect srcMp), some wholeLay⟩ := by
            dsimp only [tf_c, cacheFrameLocalLayout]
            rw [Array.getElem?_set_self hlt_tf₀, htf₀_self]
          rw [Array.getElem?_eq_getElem hlt_c] at hc_eq
          rw [Option.some.inj hc_eq]
        rw [Array.getElem?_eq_getElem hlt_dst1] at h?
        exact Option.some.inj h?
      let locals₁ := s.frame.locals.set idx .uninit
      have hlt_af₁ : idx < locals₁.length := by
        dsimp [locals₁]; rw [List.length_set]; exact hlt_af0
      have hfr₁_excl : FrameRelLM2_2Except body env (some idx) m.machine
          { s.frame with locals := locals₁ } tf₁ :=
        ⟨hfr₁.body_eq, hfr₁.location_eq, hfr₁.af_locals_len, hfr₁.mf_locals_size,
          fun i d sl ml _ hd hs hm => hfr₁.locals_rel i d sl ml hd hs hm⟩
      obtain ⟨rawAlloc, htry, hbs0, _, hmut0, _, _⟩ :=
        tryNew_uninit_of_pow2_le_29 wholeLay.layout.size wholeLay.layout.align.abi halign_le
      obtain ⟨mem', newId, hres, _, hlive_eq, hfresh_old, hwm_next, hovf_all⟩ :=
        (hsupply.of_succ).reserve_step
      have hfresh : mem'.live.any (fun entry => entry.1 == newId) = false := by
        rw [hlive_eq]; exact hfresh_old
      have hcp_ok := annealStructMemCopyOp_uninitImm_ok
        (ld := body.localDecls) (ly := body.layouts)
        (srcLay := wholeLay) (iden := topFrame.localsIdentity)
        (m := { m with stack := ⟨#[tf₁]⟩ })
        rfl hlt_dst1 hdst_tf₁ hsized htry hbs0 hmut0 hres hfresh
        hprov_s hbase_s hptr_s hlive_s hbs_s
      have hsmpr_new := StructMemPlaceRel.of_copy_fresh
        (mach := m.machine) (mem' := mem') (id := newId)
        hvalid_s hplen_s hagg_s hleaf_s hbs_s hlen_s hpmap_s hmask_s
        hbits_s hfields_s hpad_s hfresh (hovf_all _ hsz4g) halign_le
      have hm_ok :
          Miri.Interpreter.Step.evalStatement (annealStepHooks body.localDecls body.layouts) ()
            (translateStmt ⟨.assign ⟨idx, .nil⟩ (.use op), span⟩) m =
          (⟨⟨#[{ tf₁ with
              locals := tf₁.locals.set idx
                ⟨.live (.indirect (stackAllocPlace newId)), some wholeLay⟩ hlt_dst1 }]⟩,
            stackAllocMachine m.machine mem' newId
              (copyWholeStructAllocation srcLocal.allocation none)⟩, .ok ()) := by
        have hm_op' := hm_op; have hcp_ok' := hcp_ok
        have htr : translateOperand op = .Move { localId := idx, projection := #[] } := rfl
        dsimp only [tf₁, tf_c, tf₀, wholeLay] at hm_op' hcp_ok'
        rw [hm_eval, htr]; unfold Miri.Interpreter.runRvalue
        dsimp only [tf₁, tf_c, tf₀, wholeLay]
        rw [EStateM.bind_eq_ok hm_op']; simp only [hcp_ok']
      have ha_ok :
          evalStmt s ⟨.assign ⟨idx, .nil⟩ (.use op), span⟩ body.localDecls body.layouts =
          MirStepNode.step (advanceStmt s (locals₁.set idx (.init rootVal)) s.memory) := by
        unfold evalStmt; dsimp only
        rw [evalRvalue_use_nil_borrows _ _ _ hbor, hcaller]
        have hev_op : evalOperand s.frame.locals op .nil s.memory.globals body.layouts .nil =
            .ok rootVal locals₁ := by
          unfold evalOperand; dsimp only [op]; rw [hslot0]; dsimp only
          rw [set?_eq_some_set hlt_af0]
        rw [hev_op]; dsimp only
        have hloc₁_get : get? locals₁ idx = some .uninit := by
          dsimp [get?, locals₁]; exact List.getElem?_set_self hlt_af0
        rw [hprot, hbor, hloc₁_get]; dsimp only
        rw [set?_eq_some_set hlt_af₁]
        apply congrArg (fun mem =>
          MirStepNode.step (advanceStmt s (locals₁.set idx (.init rootVal)) mem))
        revert hbor hprot; generalize s.memory = mem; rintro hbor hprot
        cases mem; dsimp only at hbor hprot ⊢; subst hbor hprot; rfl
      have hfr_end : FrameRelLM2_2 body env
          (stackAllocMachine m.machine mem' newId
            (copyWholeStructAllocation srcLocal.allocation none))
          { s.frame with locals := locals₁.set idx (.init rootVal) }
          { tf₁ with
            locals := tf₁.locals.set idx
              ⟨.live (.indirect (stackAllocPlace newId)), some wholeLay⟩ hlt_dst1 } := by
        have hex := hfr₁_excl.of_stackAlloc_set_excl
          (alloc := copyWholeStructAllocation srcLocal.allocation none)
          (hlt := hlt_dst1) hres
          ⟨.live (.indirect (stackAllocPlace newId)), some wholeLay⟩
        exact hex.fill_excluded hdecl hlt_af₁
          (by dsimp only; rw [Array.size_set]; exact hlt_dst1)
          (by dsimp only; exact Array.getElem_set_self hlt_dst1)
          (.structInd fields paths rootVal (stackAllocPlace newId) (some wholeLay) henv
            (fun _ hl => (Option.some.inj (Option.mem_def.mp hl)).symm) hsmpr_new)
      rw [ha_ok,
        miri_step_at_statement_ok _ hframes hframe.body_eq hframe.location_eq hbb hstmt
          hm_ok rfl hfr_end.location_eq]
      refine .step _ _ ?_
      refine .mk _ rfl hretCont ⟨retLay, hretPlace⟩
        hfr_end.step_pc ?_ ?_
        (Or.inr (hwm_next _))
        hcal hstack hbor hprot hcaller
        (MemoryAllocDisjoint_set_fresh_stackAlloc hfr₁_excl hdisj₁ hfresh_old hlt_dst1)
      · intro j hj
        dsimp only [useStructPostStaticEnv, operandPostStaticEnv, op] at hj
        dsimp only [advanceStmt, get?]
        by_cases hjd : idx = j
        · subst hjd; rw [List.getElem?_set_self hlt_af₁]; nofun
        · rw [List.getElem?_set_ne hjd]
          dsimp [locals₁]; rw [List.getElem?_set_ne hjd, ← get?_eq_getElem?]
          rcases List.mem_cons.mp hj with rfl | hj_f
          · exact False.elim (hjd rfl)
          · rw [List.mem_filter] at hj_f
            exact hinit_env j hj_f.1
      · intro j hj mp' lay'
        dsimp only [useStructPostStaticEnv, operandPostStaticEnv, op] at hj
        rw [List.mem_filter] at hj
        have hjd : idx ≠ j := fun h => by subst h; simp at hj
        dsimp only
        rw [Array.getElem?_set_ne _ hjd]
        dsimp only [tf₁, deinitFrameLocal]; rw [Array.getElem?_set_ne _ hjd]
        dsimp only [tf_c, cacheFrameLocalLayout]; rw [Array.getElem?_set_ne _ hjd]
        dsimp only [tf₀, cacheFrameLocalLayout]; rw [Array.getElem?_set_ne _ hjd]
        rcases List.mem_cons.mp hj.1 with rfl | hj_old
        · exact False.elim (hjd rfl)
        · exact himm_env j hj_old mp' lay'

/-- Boundary characterization for self-copy `_idx = Rvalue.Use(copy _idx)` on a
live initialized `.Memory` struct (`isMove = false`, `srcIdx = dstIdx`):
* Anneal's value-tree `MirSemantics` evaluates `copy _idx` by value and steps
  `.step` (no-op rewrite of `rootVal`);
* `lean-miri`'s `annealStructMemCopyOp` follows rustc/Miri's `copy_op_no_validate`
  (`mem_copy(..., nonoverlapping = true)` on `srcId = destId`) and raises
  `.error (.undefinedBehavior "whole-value copy between overlapping ranges")`,
  establishing that `srcIdx ≠ dstIdx` in `WellTypedLM2_2UseAssignMemStruct` is
  sharp for `isMove = false`. -/
theorem step_assign_self_copy_memory_struct_divergence
    {body : CapturedMir} {env : StructTypeEnv} {stEnv : LM2_2StaticEnv} {k_bud : Nat}
    {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_2 body env stEnv k_bud s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {idx : Local} {decl : LocalDecl}
    {fields : List StructFieldDesc} {paths : List (List ProjectionElem)}
    {topOffsets : Array Miri.ABI.Size} {memoryIndex : Array Nat}
    {rootVal : Value} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨idx, .nil⟩ (.use (.copy ⟨idx, .nil⟩)), span⟩)
    (hdecl : get? body.localDecls idx = some decl)
    (henv : env decl.ty = some (fields, paths))
    (hmem_repr : (translateTy decl.ty body.layouts).layout.backendRepr = .Memory (sized := true))
    (harb : (translateTy decl.ty body.layouts).layout.fields =
      .Arbitrary topOffsets memoryIndex)
    (hnz_sz : (translateTy decl.ty body.layouts).layout.size ≠ Miri.ABI.Size.ZERO)
    (hslot : get? s.frame.locals idx = some (.init rootVal))
    (hcopy_err : ∀ (allocId : Miri.Memory.AllocId) (localAlloc : AnnealLocalAlloc),
      LiveAllocEntry m.machine.memory.live allocId localAlloc →
      localAlloc.allocation.byteSize = (translateTy decl.ty body.layouts).layout.size →
      ∃ alloc',
        Miri.Memory.Allocation.copy localAlloc.allocation
          (Miri.Memory.allocRange Miri.ABI.Size.ZERO
            (translateTy decl.ty body.layouts).layout.size)
          Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8) true true
          localAlloc.allocation = .error .copyRangesOverlap alloc') :
    stepMirFn body s =
      MirStepNode.step (advanceStmt s (s.frame.locals.set idx (.init rootVal)) s.memory) ∧
    ∃ m_err,
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m_err, .error (.undefinedBehavior "whole-value copy between overlapping ranges")) := by
  rcases hstate with
    ⟨topFrame, hframes, _, _, hframe, _, _, _, hcal, _, hbor, hprot, hcaller, _⟩
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  simp only [hbb, hstmt]
  let wholeLay := translateTy decl.ty body.layouts
  obtain ⟨slot0, mls0, hlt0, hlt_af0, hslot0, _, hmls_eq0, hloc0⟩ :=
    hframe.lookup_local hdecl
  rw [hslot] at hslot0
  injection hslot0 with hsl; subst hsl
  have ha_ok :
      evalStmt s ⟨.assign ⟨idx, .nil⟩ (.use (.copy ⟨idx, .nil⟩)), span⟩
        body.localDecls body.layouts =
      MirStepNode.step (advanceStmt s (s.frame.locals.set idx (.init rootVal)) s.memory) := by
    unfold evalStmt; dsimp only
    rw [evalRvalue_use_nil_borrows _ _ _ hbor, hcaller]
    have hev : evalOperand s.frame.locals (.copy ⟨idx, .nil⟩) .nil s.memory.globals
        body.layouts .nil = .ok rootVal s.frame.locals := by
      simp [evalOperand, readProjectedValue, hslot]
    rw [hev]; dsimp only
    rw [hprot, hbor, hslot]; dsimp only
    rw [set?_eq_some_set hlt_af0]
    apply congrArg (fun mem =>
      MirStepNode.step (advanceStmt s (s.frame.locals.set idx (.init rootVal)) mem))
    revert hbor hprot; generalize s.memory = mem; rintro hbor hprot
    cases mem; dsimp only at hbor hprot ⊢; subst hbor hprot; rfl
  refine ⟨ha_ok, ?_⟩
  cases hloc0 with
  | base _ _ henv_none _ => rw [henv] at henv_none; cases henv_none
  | structImm _ _ _ _ _ _ _ himm_s =>
    cases himm_s with
    | scalarWrapper _ _ _ _ _ _ _ hrepr _ _ _ _ _ _ _ _ _ _ =>
      rw [hmem_repr] at hrepr; cases hrepr
    | scalarPair _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hrepr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      rw [hmem_repr] at hrepr; cases hrepr
  | structInd fs_s ps_s _ mp c_s henv_s hlay_s hsmpr =>
    rcases hsmpr with
      ⟨allocId, _, baseAddr, localAlloc, _, _, _, _, _,
        hprov, _, _, hlive, hbase, hptr, _, _, _, hbs, _, _, _, _, _, _⟩
    have ⟨_, u, hu_lt, hfidx, hget⟩ := hlive
    obtain ⟨alloc', herr⟩ := hcopy_err allocId localAlloc hlive hbs
    have hcache0 : ∀ l, (topFrame.locals[idx]'hlt0).layout = some l → l = wholeLay := by
      rw [hmls_eq0]; exact hlay_s
    have huses_mem :
        usesStructMemCopyDest ⟨.local 0 idx none topFrame.localsIdentity, wholeLay⟩ = true := by
      unfold usesStructMemCopyDest
      dsimp only [wholeLay]
      rw [hmem_repr, harb]
      exact bne_iff_ne.mpr hnz_sz
    have hevalPlace := annealEvalPlace_unprojected hframes hlt0 hdecl hcache0
    have hm_eval := evalStatement_assign_use_mem_eq (dst := ⟨idx, .nil⟩)
      (op := .copy ⟨idx, .nil⟩) (span := span) hevalPlace huses_mem
    let tf₀ := cacheFrameLocalLayout topFrame idx hlt0 wholeLay
    have hlt_tf₀ : idx < tf₀.locals.size := by
      dsimp [tf₀]; rw [cacheFrameLocalLayout_size]; exact hlt0
    have htf₀_self : tf₀.locals[idx]'hlt_tf₀ = ⟨.live (.indirect mp), some wholeLay⟩ := by
      have h? : tf₀.locals[idx]? = some ⟨.live (.indirect mp), some wholeLay⟩ := by
        dsimp only [tf₀, cacheFrameLocalLayout]
        rw [Array.getElem?_set_self hlt0, hmls_eq0]
      rw [Array.getElem?_eq_getElem hlt_tf₀] at h?
      exact Option.some.inj h?
    have hm_op := annealEvalOperand_copy_live (known := some wholeLay)
      (m := { m with stack := ⟨#[tf₀]⟩ }) rfl hlt_tf₀ hdecl htf₀_self
      (fun _ h => (Option.some.inj h).symm)
    let tf₁ := cacheFrameLocalLayout tf₀ idx hlt_tf₀ wholeLay
    have hlt_tf₁ : idx < tf₁.locals.size := by
      dsimp [tf₁]; rw [cacheFrameLocalLayout_size]; exact hlt_tf₀
    have htf₁_self : tf₁.locals[idx]'hlt_tf₁ = ⟨.live (.indirect mp), some wholeLay⟩ := by
      have h? : tf₁.locals[idx]? = some ⟨.live (.indirect mp), some wholeLay⟩ := by
        dsimp only [tf₁, cacheFrameLocalLayout]
        rw [Array.getElem?_set_self hlt_tf₀, htf₀_self]
      rw [Array.getElem?_eq_getElem hlt_tf₁] at h?
      exact Option.some.inj h?
    have hcp_err := annealStructMemCopyOp_overlap_ub
      (ld := body.localDecls) (ly := body.layouts)
      (srcLay := wholeLay) (wholeLay := wholeLay) (iden := topFrame.localsIdentity)
      (m := { m with stack := ⟨#[tf₁]⟩ })
      rfl hlt_tf₁ htf₁_self hprov hbase hptr hlive hu_lt hfidx hget herr
    have hm_ub :
        Miri.Interpreter.Step.evalStatement (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨idx, .nil⟩ (.use (.copy ⟨idx, .nil⟩)), span⟩) m =
        ({ m with stack := ⟨#[tf₁]⟩ },
          .error (.undefinedBehavior "whole-value copy between overlapping ranges")) := by
      have hm_op' := hm_op; have hcp_err' := hcp_err
      have htr : translateOperand (.copy ⟨idx, .nil⟩) =
          .Copy { localId := idx, projection := #[] } := rfl
      dsimp only [wholeLay, tf₀, tf₁] at hm_op' hcp_err'
      rw [hm_eval, htr]; unfold Miri.Interpreter.runRvalue
      dsimp only [tf₁, tf₀, wholeLay]
      rw [EStateM.bind_eq_ok hm_op']; simp only [hcp_err']
    exact ⟨_, miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq
      hbb hstmt hm_ub⟩

/-- **100% syntactic (state-independent)** statement typing relation for `LM-2.2`:
depends **only** on `body`, `env : StructTypeEnv`, pre/post `LM2_2StaticEnv`,
pre/post `Nat` allocation budgets, and `stmt : Statement` — never inspecting
runtime `MachineState` or `AnnealStepState`. -/
inductive WellTypedLM2_2Stmt
    (body : CapturedMir)
    (env : StructTypeEnv) :
    LM2_2StaticEnv → Nat → Statement → LM2_2StaticEnv → Nat → Prop where
  | nop (stEnv : LM2_2StaticEnv) (k_bud : Nat) (span : String) :
      WellTypedLM2_2Stmt body env stEnv k_bud ⟨.nop, span⟩ stEnv k_bud
  | storageLive (stEnv : LM2_2StaticEnv) (k_bud : Nat)
      (loc : Local) (decl : LocalDecl) (span : String) :
      get? body.localDecls loc = some decl →
      WellTypedLM2_2Stmt body env stEnv k_bud ⟨.storageLive loc, span⟩
        (storageLivePostStaticEnv stEnv loc) k_bud
  | storageDead (stEnv : LM2_2StaticEnv) (k_bud : Nat)
      (loc : Local) (decl : LocalDecl) (span : String) :
      get? body.localDecls loc = some decl →
      loc ≠ 0 →
      WellTypedLM2_2Stmt body env stEnv k_bud ⟨.storageDead loc, span⟩
        (storageDeadPostStaticEnv stEnv loc) k_bud
  | assignUse (stEnv : LM2_2StaticEnv) (k_bud : Nat)
      (dstIdx : Local) (op : MirAst.Operand) (span : String) :
      WellTypedLM2_2UseAssign body env stEnv dstIdx op →
      WellTypedLM2_2Stmt body env stEnv k_bud
        ⟨.assign ⟨dstIdx, .nil⟩ (.use op), span⟩
        (usePostStaticEnv stEnv dstIdx op) k_bud
  | assignUseStruct (stEnv : LM2_2StaticEnv) (k_bud : Nat)
      (dstIdx : Local) (op : MirAst.Operand) (span : String) :
      WellTypedLM2_2UseAssignStruct body env stEnv dstIdx op →
      WellTypedLM2_2Stmt body env stEnv k_bud
        ⟨.assign ⟨dstIdx, .nil⟩ (.use op), span⟩
        (useStructPostStaticEnv stEnv dstIdx op) k_bud
  | assignUseMemStruct (stEnv : LM2_2StaticEnv) (k_bud : Nat)
      (dstIdx : Local) (isMove : Bool) (srcIdx : Local) (span : String) :
      WellTypedLM2_2UseAssignMemStruct body env stEnv dstIdx isMove srcIdx →
      WellTypedLM2_2Stmt body env stEnv (k_bud + 1)
        ⟨.assign ⟨dstIdx, .nil⟩ (.use (mkPlaceOperand isMove ⟨srcIdx, .nil⟩)), span⟩
        (useStructPostStaticEnv stEnv dstIdx (mkPlaceOperand isMove ⟨srcIdx, .nil⟩)) k_bud
  | assignAggregate (stEnv : LM2_2StaticEnv) (k_bud : Nat)
      (dstIdx : Local) (kind : MirAst.AggregateKind)
      (ops : List MirAst.Operand) (span : String) :
      WellTypedLM2_2Aggregate body env stEnv dstIdx kind ops →
      WellTypedLM2_2Stmt body env stEnv (k_bud + 1)
        ⟨.assign ⟨dstIdx, .nil⟩ (.aggregate kind ops), span⟩
        (aggPostStaticEnv stEnv dstIdx ops) k_bud
  | assignFieldWrite (stEnv : LM2_2StaticEnv) (k_bud : Nat)
      (dstIdx : Local) (projs : List ProjectionElem)
      (op : MirAst.Operand) (span : String) :
      WellTypedLM2_2FieldWrite body env stEnv dstIdx projs op →
      WellTypedLM2_2Stmt body env stEnv (k_bud + 1)
        ⟨.assign ⟨dstIdx, projs⟩ (.use op), span⟩
        (fieldWritePostStaticEnv stEnv dstIdx op) k_bud
  | assignSubStructWrite (stEnv : LM2_2StaticEnv) (k_bud : Nat)
      (dstIdx : Local) (projs : List ProjectionElem)
      (op : MirAst.Operand) (span : String) :
      WellTypedLM2_2SubStructWrite body env stEnv dstIdx projs op →
      WellTypedLM2_2Stmt body env stEnv k_bud
        ⟨.assign ⟨dstIdx, projs⟩ (.use op), span⟩
        (fieldWritePostStaticEnv stEnv dstIdx op) k_bud
  | assignScalarWrapWrite (stEnv : LM2_2StaticEnv) (k_bud : Nat)
      (dstIdx : Local) (projs : List ProjectionElem)
      (op : MirAst.Operand) (span : String) :
      WellTypedLM2_2ScalarWrapWrite body env stEnv dstIdx projs op →
      WellTypedLM2_2Stmt body env stEnv (k_bud + 1)
        ⟨.assign ⟨dstIdx, projs⟩ (.use op), span⟩
        (fieldWritePostStaticEnv stEnv dstIdx op) k_bud
  | assignSelfMoveMemStruct (stEnv : LM2_2StaticEnv) (k_bud : Nat)
      (idx : Local) (span : String) :
      WellTypedLM2_2SelfMoveMemStruct body env stEnv idx →
      WellTypedLM2_2Stmt body env stEnv (k_bud + 1)
        ⟨.assign ⟨idx, .nil⟩ (.use (.move ⟨idx, .nil⟩)), span⟩
        (useStructPostStaticEnv stEnv idx (.move ⟨idx, .nil⟩)) k_bud

/-- Unified single-step statement simulation for `LM-2.2`, parameterized solely
by `StateRelLM2_2` and syntactic `WellTypedLM2_2Stmt`. -/
theorem step_stmt_lm2_2_simulation
    {body : CapturedMir} {env : StructTypeEnv}
    {stEnv stEnv' : LM2_2StaticEnv} {k_bud k_bud' : Nat}
    {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_2 body env stEnv k_bud s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {stmt : Statement}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some stmt)
    (hwt : WellTypedLM2_2Stmt body env stEnv k_bud stmt stEnv' k_bud') :
    StepRelLM2_2 body env stEnv' k_bud' m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  cases hwt with
  | nop _ _ =>
    exact step_nop_lm2_2_simulation hstate hphase hbb hstmt
  | storageLive _ _ _ _ hdecl =>
    exact step_storageLive_lm2_2_simulation hstate hphase hbb hstmt hdecl
  | storageDead _ _ _ _ hdecl hne =>
    exact step_storageDead_lm2_2_simulation hstate hphase hbb hstmt hdecl hne
  | assignUse _ _ _ _ huse =>
    exact step_assign_use_lm2_2_simulation hstate hphase hbb hstmt huse
  | assignUseStruct _ _ _ _ huse =>
    exact step_assign_use_struct_lm2_2_simulation hstate hphase hbb hstmt huse
  | assignUseMemStruct _ _ _ _ _ huse =>
    exact step_assign_use_memory_struct_lm2_2_simulation hstate hphase hbb hstmt huse
  | assignAggregate _ _ _ _ _ hagg =>
    exact evalRvalue_aggregate_tuple_struct_simulation hstate hphase hbb hstmt hagg
  | assignFieldWrite _ _ _ _ _ hfw =>
    exact step_assign_nested_field_write_simulation hstate hphase hbb hstmt hfw
  | assignSubStructWrite _ _ _ _ _ hsw =>
    exact step_assign_nested_substruct_write_simulation hstate hphase hbb hstmt hsw
  | assignScalarWrapWrite _ _ _ _ _ hsw =>
    exact step_assign_nested_scalar_wrap_write_simulation hstate hphase hbb hstmt hsw
  | assignSelfMoveMemStruct _ _ _ hsm =>
    exact step_assign_self_move_memory_struct_lm2_2_simulation hstate hphase hbb hstmt hsm

private theorem evalStmt_assign_projected_step_location
    {body : CapturedMir} {s s' : MachineState}
    {dstIdx : Local} {idx₀ : Nat} {fty₀ : Ty} {ps : List ProjectionElem}
    {op : MirAst.Operand} {span : String}
    (hstep : evalStmt s ⟨.assign ⟨dstIdx, .field idx₀ fty₀ :: ps⟩ (.use op), span⟩
      body.localDecls body.layouts = .step s') :
    s'.frame.blockIdx = s.frame.blockIdx ∧ s'.frame.stmtIdx = s.frame.stmtIdx + 1 := by
  unfold evalStmt at hstep; dsimp only at hstep
  revert hstep
  cases evalRvalue s.frame.locals (.use op) s.memory body.localDecls body.layouts with
  | ub | unsupported => intro h; cases h
  | ok val locals₁ mem₁ =>
    dsimp only
    cases get? locals₁ dstIdx with
    | none => intro h; cases h
    | some sl =>
      cases sl with
      | dead | uninit => intro h; cases h
      | init rootVal =>
        dsimp only
        cases writeProjectedValue locals₁ rootVal (.field idx₀ fty₀ :: ps) val with
        | ub | unsupported => intro h; cases h
        | ok rootVal' =>
          dsimp only
          cases set? locals₁ dstIdx (.init rootVal') with
          | none => intro h; cases h
          | some _ =>
            dsimp only
            cases mem₁.activeProtectors with
            | nil =>
              intro h; injection h with heq1; injection heq1 with heq2; subst heq2
              exact ⟨rfl, rfl⟩
            | cons protHead protTail =>
              dsimp only
              cases hasProtectedWriteConflict mem₁.borrows (protHead :: protTail)
                  dstIdx none (.field idx₀ fty₀ :: ps) with
              | true => intro h; cases h
              | false =>
                intro h; injection h with heq1; injection heq1 with heq2; subst heq2
                exact ⟨rfl, rfl⟩

private theorem evalStmt_step_location_lm2_2
    {body : CapturedMir} {env : StructTypeEnv}
    {stEnv stEnv' : LM2_2StaticEnv} {k_bud k_bud' : Nat}
    {s s' : MachineState} {stmt : Statement}
    (hwt : WellTypedLM2_2Stmt body env stEnv k_bud stmt stEnv' k_bud')
    (hstep : evalStmt s stmt body.localDecls body.layouts = .step s') :
    s'.frame.blockIdx = s.frame.blockIdx ∧ s'.frame.stmtIdx = s.frame.stmtIdx + 1 := by
  cases hwt with
  | nop _ _ =>
    exact evalStmt_step_location (Or.inl rfl) hstep
  | storageLive _ loc _ _ _ =>
    exact evalStmt_step_location (Or.inr (Or.inl ⟨loc, rfl⟩)) hstep
  | storageDead _ loc _ _ _ _ =>
    exact evalStmt_step_location (Or.inr (Or.inr (Or.inl ⟨loc, rfl⟩))) hstep
  | assignUse _ dstIdx op _ _ =>
    exact evalStmt_step_location (Or.inr (Or.inr (Or.inr ⟨dstIdx, .use op, rfl⟩))) hstep
  | assignUseStruct _ dstIdx op _ _ =>
    exact evalStmt_step_location (Or.inr (Or.inr (Or.inr ⟨dstIdx, .use op, rfl⟩))) hstep
  | assignUseMemStruct _ dstIdx isMove srcIdx _ _ =>
    exact evalStmt_step_location
      (Or.inr (Or.inr (Or.inr ⟨dstIdx, .use (mkPlaceOperand isMove ⟨srcIdx, .nil⟩), rfl⟩))) hstep
  | assignAggregate _ dstIdx kind ops _ _ =>
    exact evalStmt_step_location (Or.inr (Or.inr (Or.inr ⟨dstIdx, .aggregate kind ops, rfl⟩))) hstep
  | assignFieldWrite _ dstIdx projs op _ hfw =>
    cases hfw with
    | mk _ _ _ _ _ _ _ _ _ _ _ _ hchain _ _ _ _ _ =>
      obtain ⟨idx₀, fty₀, ps, rfl⟩ : ∃ idx₀ fty₀ ps, projs = .field idx₀ fty₀ :: ps := by
        cases hpr : projs with
        | nil => exact False.elim (hchain.ne_nil hpr)
        | cons p₀ ps =>
          obtain ⟨i, t, rfl⟩ := hchain.only_fields p₀ (by rw [hpr]; exact List.mem_cons_self)
          exact ⟨i, t, ps, rfl⟩
      exact evalStmt_assign_projected_step_location hstep
  | assignSubStructWrite _ dstIdx projs op _ hsw =>
    cases hsw with
    | mk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hchain _ _ _ _ _ _ _ _ _ _ =>
      obtain ⟨idx₀, fty₀, ps, rfl⟩ : ∃ idx₀ fty₀ ps, projs = .field idx₀ fty₀ :: ps := by
        cases hpr : projs with
        | nil => exact False.elim (hchain.ne_nil hpr)
        | cons p₀ ps =>
          obtain ⟨i, t, rfl⟩ := hchain.only_fields p₀ (by rw [hpr]; exact List.mem_cons_self)
          exact ⟨i, t, ps, rfl⟩
      exact evalStmt_assign_projected_step_location hstep
  | assignScalarWrapWrite _ dstIdx projs op _ hsw =>
    cases hsw with
    | mk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hchain _ _ _ _ _ _ _ =>
      obtain ⟨idx₀, fty₀, ps, rfl⟩ : ∃ idx₀ fty₀ ps, projs = .field idx₀ fty₀ :: ps := by
        cases hpr : projs with
        | nil => exact False.elim (hchain.ne_nil hpr)
        | cons p₀ ps =>
          obtain ⟨i, t, rfl⟩ := hchain.only_fields p₀ (by rw [hpr]; exact List.mem_cons_self)
          exact ⟨i, t, ps, rfl⟩
      exact evalStmt_assign_projected_step_location hstep
  | assignSelfMoveMemStruct _ idx _ _ =>
    exact evalStmt_step_location
      (Or.inr (Or.inr (Or.inr ⟨idx, .use (.move ⟨idx, .nil⟩), rfl⟩))) hstep

/-- Abstract two-statement composition theorem for `LM-2.2`: any two consecutive
syntactically well-typed statements `stmt₁` and `stmt₂` in basic block `bb`
compose cleanly across `StateRelLM2_2` without manual per-local state surgery
(constructing an aggregate in `stmt₁` and reading/writing its nested fields in
`stmt₂`, or chaining two field writes / aggregate constructions). -/
theorem step_two_stmts_lm2_2_simulation
    {body : CapturedMir} {env : StructTypeEnv}
    {stEnv₀ stEnv₁ stEnv₂ : LM2_2StaticEnv} {k₀ k₁ k₂ : Nat}
    {s₀ : MachineState} {m₀ : AnnealStepState}
    (hstate₀ : StateRelLM2_2 body env stEnv₀ k₀ s₀ m₀)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {stmt₁ stmt₂ : Statement}
    (hbb : get? body.basicBlocks s₀.frame.blockIdx = some bb)
    (hstmt₁ : get? bb.statements s₀.frame.stmtIdx = some stmt₁)
    (hstmt₂ : get? bb.statements (s₀.frame.stmtIdx + 1) = some stmt₂)
    (hwt₁ : WellTypedLM2_2Stmt body env stEnv₀ k₀ stmt₁ stEnv₁ k₁)
    (hwt₂ : WellTypedLM2_2Stmt body env stEnv₁ k₁ stmt₂ stEnv₂ k₂) :
    (stepMirFn body s₀ = .fail .ub ∧
      ∃ m_err msg,
        Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m₀ =
          (m_err, .error (.undefinedBehavior msg))) ∨
    (∃ s₁ m₁,
      stepMirFn body s₀ = .step s₁ ∧
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m₀ =
        (m₁, .ok true) ∧
      StateRelLM2_2 body env stEnv₁ k₁ s₁ m₁ ∧
      StepRelLM2_2 body env stEnv₂ k₂ m₁
        (stepMirFn body s₁)
        (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m₁)) := by
  have hcal₀ : s₀.memory.activeCallee = none := by
    rcases hstate₀ with ⟨_, _, _, _, _, _, _, _, hcal, _, _, _, _, _⟩; exact hcal
  have hsim₁ := step_stmt_lm2_2_simulation hstate₀ hphase hbb hstmt₁ hwt₁
  generalize ha₁ : stepMirFn body s₀ = r_a₁ at hsim₁ ⊢
  generalize hm₁ :
    Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m₀ = r_m₁ at hsim₁ ⊢
  cases hsim₁ with
  | ub m_err msg =>
    exact Or.inl ⟨rfl, m_err, msg, rfl⟩
  | step s₁ m₁ hstate₁ =>
    have hev₁ : evalStmt s₀ stmt₁ body.localDecls body.layouts = .step s₁ := by
      rw [stepMirFn_eq_of_not_other body s₀ hcal₀ hphase] at ha₁
      simpa only [hbb, hstmt₁] using ha₁
    obtain ⟨hblk₁, hidx₁⟩ := evalStmt_step_location_lm2_2 hwt₁ hev₁
    have hbb₁ : get? body.basicBlocks s₁.frame.blockIdx = some bb := by rw [hblk₁]; exact hbb
    have hstmt₂' : get? bb.statements s₁.frame.stmtIdx = some stmt₂ := by rw [hidx₁]; exact hstmt₂
    exact Or.inr ⟨s₁, m₁, rfl, rfl, hstate₁,
      step_stmt_lm2_2_simulation hstate₁ hphase hbb₁ hstmt₂' hwt₂⟩

/-- Syntactic typing of a run of consecutive statements, threading the static
environment and the allocation budget through `WellTypedLM2_2Stmt`. -/
inductive WellTypedLM2_2Stmts (body : CapturedMir) (env : StructTypeEnv) :
    LM2_2StaticEnv → Nat → List Statement → LM2_2StaticEnv → Nat → Prop where
  | nil (stEnv : LM2_2StaticEnv) (k_bud : Nat) :
      WellTypedLM2_2Stmts body env stEnv k_bud [] stEnv k_bud
  | cons {stEnv₀ stEnv₁ stEnv₂ : LM2_2StaticEnv} {k₀ k₁ k₂ : Nat}
      {stmt : Statement} {rest : List Statement} :
      WellTypedLM2_2Stmt body env stEnv₀ k₀ stmt stEnv₁ k₁ →
      WellTypedLM2_2Stmts body env stEnv₁ k₁ rest stEnv₂ k₂ →
      WellTypedLM2_2Stmts body env stEnv₀ k₀ (stmt :: rest) stEnv₂ k₂

/-- Composition of `step_stmt_lm2_2_simulation` over any number of consecutive
syntactically well-typed statements of one basic block. Running both machines
for `stmts.length` steps (`runAnnealBounded` / `runMiriBounded`) either raises UB
on both sides at the same statement, or reaches `StateRelLM2_2`-related states at
the statement just after the run. -/
theorem step_stmts_lm2_2_simulation
    {body : CapturedMir} {env : StructTypeEnv}
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData}
    {stEnv stEnv' : LM2_2StaticEnv} {k_bud k_bud' : Nat} {stmts : List Statement}
    (hwt : WellTypedLM2_2Stmts body env stEnv k_bud stmts stEnv' k_bud') :
    ∀ {s : MachineState} {m : AnnealStepState},
      StateRelLM2_2 body env stEnv k_bud s m →
      get? body.basicBlocks s.frame.blockIdx = some bb →
      (∀ i (hi : i < stmts.length),
        get? bb.statements (s.frame.stmtIdx + i) = some (stmts[i]'hi)) →
      (runAnnealBounded body stmts.length s = .faulted .ub ∧
        ∃ m_err msg,
          runMiriBounded body stmts.length m = .error m_err (.undefinedBehavior msg)) ∨
      (∃ s' m',
        runAnnealBounded body stmts.length s = .running s' ∧
        runMiriBounded body stmts.length m = .running m' ∧
        StateRelLM2_2 body env stEnv' k_bud' s' m' ∧
        s'.frame.blockIdx = s.frame.blockIdx ∧
        s'.frame.stmtIdx = s.frame.stmtIdx + stmts.length) := by
  induction hwt with
  | nil stEnv k_bud =>
    intro s m hstate _ _
    exact Or.inr ⟨s, m, rfl, rfl, hstate, rfl, rfl⟩
  | @cons stEnv₀ stEnv₁ stEnv₂ k₀ k₁ k₂ stmt rest hwt₁ _ ih =>
    intro s m hstate hbb hstmts
    rw [List.length_cons]
    have hcal : s.memory.activeCallee = none := by
      rcases hstate with ⟨_, _, _, _, _, _, _, _, hcal, _, _, _, _, _⟩; exact hcal
    have hstmt₀ : get? bb.statements s.frame.stmtIdx = some stmt := by
      simpa using hstmts 0 (Nat.zero_lt_succ _)
    have hsim := step_stmt_lm2_2_simulation hstate hphase hbb hstmt₀ hwt₁
    generalize ha₁ : stepMirFn body s = r_a at hsim
    generalize hm₁ :
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m = r_m at hsim
    cases hsim with
    | ub m_err msg =>
      left
      refine ⟨?_, m_err, msg, ?_⟩
      · rw [runAnnealBounded.eq_2, ha₁]; rfl
      · rw [runMiriBounded.eq_2, hm₁]
    | step s₁ m₁ hstate₁ =>
      have hev₁ : evalStmt s stmt body.localDecls body.layouts = .step s₁ := by
        rw [stepMirFn_eq_of_not_other body s hcal hphase] at ha₁
        simpa only [hbb, hstmt₀] using ha₁
      obtain ⟨hblk₁, hidx₁⟩ := evalStmt_step_location_lm2_2 hwt₁ hev₁
      have hbb₁ : get? body.basicBlocks s₁.frame.blockIdx = some bb := by rw [hblk₁]; exact hbb
      have hstmts₁ : ∀ i (hi : i < rest.length),
          get? bb.statements (s₁.frame.stmtIdx + i) = some (rest[i]'hi) := by
        intro i hi
        have h := hstmts (i + 1) (Nat.succ_lt_succ hi)
        rw [hidx₁, Nat.add_assoc, Nat.add_comm 1 i]
        simpa using h
      have hnonempty : m₁.stack.frames.isEmpty = false := by
        rcases hstate₁ with ⟨tf, hf, _⟩
        rw [hf]; rfl
      have hrunA : runAnnealBounded body (rest.length + 1) s =
          runAnnealBounded body rest.length s₁ := by
        rw [runAnnealBounded.eq_2, ha₁]; rfl
      have hrunM : runMiriBounded body (rest.length + 1) m =
          runMiriBounded body rest.length m₁ := by
        rw [runMiriBounded.eq_2, hm₁]; dsimp only; rw [hnonempty]; rfl
      rw [hrunA, hrunM]
      rcases ih hstate₁ hbb₁ hstmts₁ with hub | ⟨s', m', hra, hrm, hst', hblk', hidx'⟩
      · exact Or.inl hub
      · refine Or.inr ⟨s', m', hra, hrm, hst', hblk'.trans hblk₁, ?_⟩
        rw [hidx', hidx₁]; omega

/-! ## 9. Terminators under `StateRelLM2_2`

The root-frame `Return` only reads `_0` and pops the frame, so its simulation
needs nothing about the other locals. Stating it under `StateRelLM2_2` lets a
function return while a padded struct is still live in memory, a state that
the base `StateRel` cannot express. -/

/-- `Goto` keeps `StateRelLM2_2` (only the location changes); `Unreachable`
raises UB on both sides. -/
theorem step_terminator_goto_lm2_2_simulation
    {body : CapturedMir} {env : StructTypeEnv} {stEnv : LM2_2StaticEnv} {k_bud : Nat}
    {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_2 body env stEnv k_bud s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    (hstmt_len : s.frame.stmtIdx = length bb.statements)
    (hterm : (∃ target, bb.terminator.kind = .goto target) ∨
      bb.terminator.kind = .unreachable) :
    StepRelLM2_2 body env stEnv k_bud m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  rcases hstate with
    ⟨topFrame, hframes, hretCont, ⟨retLay, hretPlace⟩, hframe,
      hinit_env, himm_env, hsupply, hcal, hstack, hbor, hprot, hcaller, hdisj⟩
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  have hbeq_len : (s.frame.stmtIdx == length bb.statements) = true := by
    simp [hstmt_len]
  simp only [hbb, hstmt_none, hbeq_len, ↓reduceIte]
  rw [miri_step_at_terminator hframes hframe.body_eq hframe.location_eq hbb hstmt_none]
  rcases hterm with ⟨target, hgoto⟩ | hunreach
  · unfold evalTerminator translateTerminator
      Miri.Interpreter.ControlFlow.evalTerminator
      Miri.Interpreter.ControlFlow.goToBlock
      Miri.Interpreter.ControlFlow.setLocation
    rw [hgoto, stack_currentFrame?_singleton m.stack topFrame hframes, hframes]
    dsimp only [translateTerminatorKind, Except.map, Id.run]
    apply StepRelLM2_2.step
    exact .mk { topFrame with location := .mir ⟨target, 0⟩ }
      rfl hretCont ⟨retLay, hretPlace⟩
      ⟨hframe.body_eq, rfl, hframe.af_locals_len, hframe.mf_locals_size, hframe.locals_rel⟩
      hinit_env himm_env hsupply hcal hstack hbor hprot hcaller hdisj
  · unfold evalTerminator translateTerminator Miri.Interpreter.ControlFlow.evalTerminator
    rw [hunreach]
    dsimp only [translateTerminatorKind, Except.map, Id.run]
    exact .ub _ _

/-- Root-frame `Return` from any `StateRelLM2_2`-related state whose return
local `_0` is a non-struct, non-ZST local that is not held in memory
(`0 ∈ stEnv.immLocals`): both machines either raise UB (dead or uninitialized
`_0`) or return `ImmediateRel`-related values (`StepRel.retRoot`). Struct locals,
including padded ones still live in memory, impose no condition. -/
theorem step_terminator_return_lm2_2_simulation
    {body : CapturedMir} {env : StructTypeEnv} {stEnv : LM2_2StaticEnv} {k_bud : Nat}
    {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_2 body env stEnv k_bud s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    (hstmt_len : s.frame.stmtIdx = length bb.statements)
    (hcleanup : bb.isCleanup = false)
    (hret : bb.terminator.kind = .return_)
    {decl0 : LocalDecl}
    (hdecl0 : get? body.localDecls 0 = some decl0)
    (henv0 : env decl0.ty = none)
    (hsz0 : (translateTy decl0.ty body.layouts).layout.size ≠ Miri.ABI.Size.ZERO)
    (himm0 : 0 ∈ stEnv.immLocals) :
    StepRel body m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  rcases hstate with
    ⟨topFrame, hframes, hretCont, ⟨retLay, hretPlace⟩, hframe,
      _, himm_env, _, hcal, hstack, hbor, hprot, hcaller, _⟩
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  have hbeq_len : (s.frame.stmtIdx == length bb.statements) = true := by
    simp [hstmt_len]
  simp only [hbb, hstmt_none, hbeq_len, ↓reduceIte]
  rw [miri_step_at_terminator hframes hframe.body_eq hframe.location_eq hbb hstmt_none]
  obtain ⟨slot0, mls0, _, _, hslot0, hmls0, _, hloc0⟩ := hframe.lookup_local hdecl0
  have hget0 := frame_getLocal_of_getElem? topFrame 0 mls0 hmls0
  have himm0' : ∀ mp, mls0.value ≠ .live (.indirect mp) := by
    intro mp hv
    rcases mls0 with ⟨val0, lay0⟩
    dsimp only at hv; subst hv
    exact himm_env 0 himm0 mp lay0 hmls0
  unfold evalTerminator translateTerminator
    Miri.Interpreter.ControlFlow.evalTerminator
  rw [hret, hstack, annealTerminatorHooks_toControlHooks, hslot0]
  dsimp only [translateTerminatorKind, Id.run, Pure.pure]
  cases hloc0 with
  | structDead _ _ _ henv _ | structUninitImm _ _ _ henv _ | structUninitInd _ _ _ _ henv _ _
  | structImm _ _ _ _ _ henv _ _ | structInd _ _ _ _ _ henv _ _ =>
    rw [henv0] at henv; cases henv
  | base _ _ _ hb =>
    cases hb with
    | dead cachedLayout _ =>
      rw [returnFromCurrentFrame_of_error annealControlHooks hframes hframe.body_eq
        hframe.location_eq hbb hcleanup (annealControlHooks_returnOperand_dead hframes hget0)]
      exact StepRel.ub _ _
    | indirect _ mp _ _ _ _ =>
      exact False.elim (himm0' mp rfl)
    | immediate _ imm cachedLayout _ hval =>
      rcases hval with ⟨rfl, rfl⟩ | ⟨retVal, rfl, himmRel⟩
      · rw [returnFromCurrentFrame_of_error annealControlHooks hframes hframe.body_eq
          hframe.location_eq hbb hcleanup (annealControlHooks_returnOperand_uninit hframes hget0)]
        exact StepRel.ub _ _
      · cases himmRel with
        | unit hzero =>
          exact False.elim (hsz0 hzero)
        | scalar sc msc hsc hsz_sc hbool_sc hchar_sc =>
          have hop0 := annealControlHooks_returnOperand_scalar hframes hget0
          rw [returnFromCurrentFrame_of_ok annealControlHooks hframes hframe.body_eq
            hframe.location_eq hbb hcleanup hretCont hop0
            (annealControlHooks_popFrame_singleton hframes)
            (annealControlHooks_copyReturn_empty _ hretPlace)
            (annealControlHooks_cleanupFrame_eq false topFrame _)]
          exact StepRel.retRoot decl0 _ _ s.memory _ hdecl0 hop0
            (.scalar sc msc hsc hsz_sc hbool_sc hchar_sc) rfl
        | scalarPair sc₁ sc₂ msc₁ msc₂ hsc₁ hsc₂ hagg hpair =>
          have hop0 := annealControlHooks_returnOperand_scalarPair hframes hget0
          rw [returnFromCurrentFrame_of_ok annealControlHooks hframes hframe.body_eq
            hframe.location_eq hbb hcleanup hretCont hop0
            (annealControlHooks_popFrame_singleton hframes)
            (annealControlHooks_copyReturn_empty _ hretPlace)
            (annealControlHooks_cleanupFrame_eq false topFrame _)]
          exact StepRel.retRoot decl0 _ _ s.memory _ hdecl0 hop0
            (.scalarPair sc₁ sc₂ msc₁ msc₂ hsc₁ hsc₂ hagg hpair) rfl

/-- `annealControlHooks.returnOperand` extracts `.ok (.indirect mp)` when root
return local `_0` holds `.live (.indirect mp)`. -/
theorem annealControlHooks_returnOperand_indirect
    {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    {lay : Option Miri.Interpreter.LocalLayout}
    (hframes : m.stack.frames = #[topFrame])
    (hget0 : topFrame.getLocal 0 = .ok ⟨.live (.indirect mp), lay⟩) :
    annealControlHooks.returnOperand () m = (m, .ok (.indirect mp)) := by
  unfold annealControlHooks
  dsimp only
  rw [stack_currentFrame?_singleton m.stack topFrame hframes]
  dsimp only
  rw [hget0]

/-- Root-frame return correspondence for functions whose return local `_0` has
a tuple or struct type registered in `env decl0.ty = some (fields, paths)`:
* `retRootImm`: immediate `.Scalar` wrapper or `.ScalarPair` tuple/struct return
  related by `ImmediateStructRel`;
* `retRootMem`: `.Memory`-ABI tuple/struct return at indirect `MemPlace` `mp0`,
  preserving `StructMemPlaceRel m'.machine decl0.ty body.layouts fields paths retVal mp0`
  (including all leaf fields and `.uninit` alignment padding bytes) in the popped
  post-return machine `m' = { m with stack := ⟨#[]⟩ }`;
* `ub`: dead or uninitialized `_0` raises undefined behavior on both sides. -/
inductive StepRelStructReturnLM2_2
    (body : CapturedMir)
    (fields : List StructFieldDesc)
    (paths : List (List ProjectionElem))
    (m : AnnealStepState) :
    MirStepNode →
    Miri.Interpreter.StepResult AnnealStepState Bool →
    Prop where
  | retRootImm (decl0 : LocalDecl) (retVal : Value)
      (imm0 : Miri.Interpreter.Immediate AnnealProv)
      (mem' : Memory) (m' : AnnealStepState) :
      get? body.localDecls 0 = some decl0 →
      annealControlHooks.returnOperand () m = (m, .ok (.immediate imm0)) →
      ImmediateStructRel decl0.ty body.layouts fields paths retVal imm0 →
      m' = { m with stack := ⟨#[]⟩ } →
      StepRelStructReturnLM2_2 body fields paths m
        (MirStepNode.retNormal retVal mem') (m', .ok true)
  | retRootMem (decl0 : LocalDecl) (retVal : Value)
      (mp0 : Miri.Interpreter.MemPlace AnnealProv)
      (mem' : Memory) (m' : AnnealStepState) :
      get? body.localDecls 0 = some decl0 →
      annealControlHooks.returnOperand () m = (m, .ok (.indirect mp0)) →
      StructMemPlaceRel m'.machine decl0.ty body.layouts fields paths retVal mp0 →
      m' = { m with stack := ⟨#[]⟩ } →
      StepRelStructReturnLM2_2 body fields paths m
        (MirStepNode.retNormal retVal mem') (m', .ok true)
  | ub (m' : AnnealStepState) (msg : String) :
      StepRelStructReturnLM2_2 body fields paths m
        (MirStepNode.fail .ub) (m', .error (.undefinedBehavior msg))

/-- Lockstep simulation of root-frame `Return` for tuple- and struct-returning
functions (`env decl0.ty = some (fields, paths)`, `0 ∈ stEnv.initLocals ∨ 0 ∈ stEnv.immLocals`),
covering `.Scalar` newtypes, `.ScalarPair` tuples/structs, and padded `.Memory`
tuples/structs as well as uninitialized/dead `_0` UB. -/
theorem step_terminator_return_struct_lm2_2_simulation
    {body : CapturedMir} {env : StructTypeEnv} {stEnv : LM2_2StaticEnv} {k_bud : Nat}
    {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_2 body env stEnv k_bud s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    (hstmt_len : s.frame.stmtIdx = length bb.statements)
    (hcleanup : bb.isCleanup = false)
    (hret : bb.terminator.kind = .return_)
    {decl0 : LocalDecl}
    {fields : List StructFieldDesc}
    {paths : List (List ProjectionElem)}
    (hdecl0 : get? body.localDecls 0 = some decl0)
    (henv0 : env decl0.ty = some (fields, paths))
    (h0_state : 0 ∈ stEnv.initLocals ∨ 0 ∈ stEnv.immLocals) :
    StepRelStructReturnLM2_2 body fields paths m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  rcases hstate with
    ⟨topFrame, hframes, hretCont, ⟨retLay, hretPlace⟩, hframe,
      hinit_env, himm_env, _, hcal, hstack, _, _, _, _⟩
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  have hbeq_len : (s.frame.stmtIdx == length bb.statements) = true := by
    simp [hstmt_len]
  simp only [hbb, hstmt_none, hbeq_len, ↓reduceIte]
  rw [miri_step_at_terminator hframes hframe.body_eq hframe.location_eq hbb hstmt_none]
  obtain ⟨slot0, mls0, _, _, hslot0, hmls0, _, hloc0⟩ := hframe.lookup_local hdecl0
  have hget0 := frame_getLocal_of_getElem? topFrame 0 mls0 hmls0
  unfold evalTerminator translateTerminator
    Miri.Interpreter.ControlFlow.evalTerminator
  rw [hret, hstack, annealTerminatorHooks_toControlHooks, hslot0]
  dsimp only [translateTerminatorKind, Id.run, Pure.pure]
  cases hloc0 with
  | base _ _ henv_none _ =>
    rw [henv0] at henv_none; cases henv_none
  | structDead _ _ _ _ _ =>
    rw [returnFromCurrentFrame_of_error annealControlHooks hframes hframe.body_eq
      hframe.location_eq hbb hcleanup (annealControlHooks_returnOperand_dead hframes hget0)]
    exact .ub _ _
  | structUninitImm _ _ _ _ _ =>
    rw [returnFromCurrentFrame_of_error annealControlHooks hframes hframe.body_eq
      hframe.location_eq hbb hcleanup (annealControlHooks_returnOperand_uninit hframes hget0)]
    exact .ub _ _
  | structUninitInd _ _ mp0 c0 _ _ _ =>
    rcases h0_state with h0_init | h0_imm
    · exact False.elim (hinit_env 0 h0_init hslot0)
    · exact False.elim (himm_env 0 h0_imm mp0 c0 hmls0)
  | structImm fs ps retVal imm0 _ henv _ himmRel =>
    have hfp := henv0.symm.trans henv
    injection hfp with hfp'; injection hfp' with hfs hps; subst hfs hps
    have hop0 : annealControlHooks.returnOperand () m = (m, .ok (.immediate imm0)) := by
      cases himmRel with
      | scalarWrapper _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
        exact annealControlHooks_returnOperand_scalar hframes hget0
      | scalarPair _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
        exact annealControlHooks_returnOperand_scalarPair hframes hget0
    rw [returnFromCurrentFrame_of_ok annealControlHooks hframes hframe.body_eq
      hframe.location_eq hbb hcleanup hretCont hop0
      (annealControlHooks_popFrame_singleton hframes)
      (annealControlHooks_copyReturn_empty _ hretPlace)
      (annealControlHooks_cleanupFrame_eq false topFrame _)]
    exact .retRootImm decl0 retVal imm0 s.memory _ hdecl0 hop0 himmRel rfl
  | structInd fs ps retVal mp0 _ henv _ hsmpr =>
    have hfp := henv0.symm.trans henv
    injection hfp with hfp'; injection hfp' with hfs hps; subst hfs hps
    have hop0 := annealControlHooks_returnOperand_indirect hframes hget0
    rw [returnFromCurrentFrame_of_ok annealControlHooks hframes hframe.body_eq
      hframe.location_eq hbb hcleanup hretCont hop0
      (annealControlHooks_popFrame_singleton hframes)
      (annealControlHooks_copyReturn_empty _ hretPlace)
      (annealControlHooks_cleanupFrame_eq false topFrame _)]
    exact .retRootMem decl0 retVal mp0 s.memory _ hdecl0 hop0 hsmpr rfl

end LeanMiriSpec.Correspondence
