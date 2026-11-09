/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import LeanMiriSpec.Correspondence.SimLM3_2

/-!
# Intrinsic Hooks for `LM-4.2`

Exact characterizations of the `LM-4.2` hooks of `Translate.lean`
(`annealIntrinsicHooks`, `annealCallHooks`) on the vendored
`Miri.Interpreter.Intrinsics` and `Miri.Interpreter.Call` entry points, which
`SimLM4_2.lean` uses to relate one real step of each machine.

* `NonDivergingIntrinsic.Assume`: `evalNondiverging_assume_eq` unfolds
  `Intrinsics.evalNondiverging` on `Assume`, and `scalar_toBool_of_scalarRel`
  evaluates `Scalar.toBool` on a one-byte scalar.
-/

namespace LeanMiriSpec.Correspondence

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

/-! ## 1. `NonDivergingIntrinsic.Assume` -/

/-- `Step.evalStatement` runs a translated `StatementKind.intrinsic` statement
through `annealStepHooks.intrinsic`, that is, through the vendored
`Intrinsics.evalNondiverging` under `annealIntrinsicHooks`. -/
theorem evalStatement_intrinsic_eq (localDecls : List LocalDecl) (layouts : LayoutTable)
    (intrinsic : Miri.MIR.NonDivergingIntrinsic) (m : AnnealStepState) :
    Miri.Interpreter.Step.evalStatement (annealStepHooks localDecls layouts) ()
        { sourceInfo := defaultSourceInfo, kind := .Intrinsic intrinsic } m =
      Miri.Interpreter.runRvalue
        (Miri.Interpreter.Intrinsics.evalNondiverging (annealIntrinsicHooks localDecls layouts)
          () intrinsic) m := rfl

/-- `Intrinsics.evalNondiverging` on `Assume condition` under
`annealIntrinsicHooks`: evaluate the operand with `annealEvalOperand`, read it
with `annealReadImmediate`, convert it with `Scalar.toBool`, and report
undefined behavior for `false`. -/
theorem evalNondiverging_assume_eq (localDecls : List LocalDecl) (layouts : LayoutTable)
    (condition : Miri.MIR.Operand) :
    Miri.Interpreter.Intrinsics.evalNondiverging (annealIntrinsicHooks localDecls layouts) ()
        (.Assume condition) =
      (do
        let op ← annealEvalOperand localDecls layouts condition none
        let value ← annealReadImmediate op
        let scalar ← liftScalarResult
          (value.imm.toScalar |>.mapError Miri.Interpreter.ScalarOps.immediateError)
        let cond ← liftScalarResult
          (scalar.toBool |>.mapError Miri.Interpreter.ScalarOps.scalarError)
        if !cond then throw (.undefinedBehavior "assume called with false") else pure ()) :=
  rfl

/-- `Scalar.toBool` on the `lean-miri` scalar of a one-byte Anneal scalar `sc`:
`false` for bit pattern `0`, `true` for `1`, and `invalidBool` otherwise. -/
theorem scalar_toBool_of_scalarRel {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    (hrel : ScalarRel sc msc) (hsz1 : sc.sizeBytes = 1) :
    (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) msc).toBool =
      if sc.bits = 0 then .ok false
      else if sc.bits = 1 then .ok true
      else .error (.scalarInt (.invalidBool (UInt8.ofNat sc.bits))) := by
  have htb : msc.toBits (Miri.ABI.Size.ofBytes 1) = .ok (BitVec.ofNat 128 sc.bits) := by
    have hb := hrel.toBits_eq
    rw [hsz1] at hb
    exact hb
  have hcan := hrel.canonical
  rw [hsz1] at hcan
  have hlt : sc.bits < 256 := by
    have : scalarModulus 1 = 256 := by decide
    omega
  have hnat : (BitVec.ofNat 128 sc.bits).toNat = sc.bits := by
    rw [BitVec.toNat_ofNat]; omega
  have hu8 : (UInt8.ofNat sc.bits).toNat = sc.bits := UInt8.toNat_ofNat_of_lt (by omega)
  have heq : (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) msc).toBool =
      (if UInt8.ofNat (BitVec.ofNat 128 sc.bits).toNat == 0 then .ok false
       else if UInt8.ofNat (BitVec.ofNat 128 sc.bits).toNat == 1 then .ok true
       else .error (.scalarInt (.invalidBool (UInt8.ofNat (BitVec.ofNat 128 sc.bits).toNat)))) := by
    unfold Miri.Memory.Scalar.toBool Miri.Memory.Scalar.toUInt8
      Miri.Memory.Scalar.toUInt
      Miri.Memory.Scalar.toBits Miri.Memory.Scalar.toScalarInt
      Miri.Memory.Scalar.tryToScalarInt Miri.Memory.Scalar.fromScalarInt
    dsimp only [bind, Except.bind, Except.mapError, pure, Except.pure]
    rw [htb]
    rfl
  rw [heq, hnat]
  by_cases h0 : sc.bits = 0
  · rw [h0]; rfl
  · have hn0 : (UInt8.ofNat sc.bits == 0) = false := by
      cases h : (UInt8.ofNat sc.bits == 0) with
      | false => rfl
      | true =>
        have := congrArg UInt8.toNat (beq_iff_eq.mp h)
        rw [hu8] at this
        exact absurd this h0
    by_cases h1 : sc.bits = 1
    · rw [h1]; rfl
    · have hn1 : (UInt8.ofNat sc.bits == 1) = false := by
        cases h : (UInt8.ofNat sc.bits == 1) with
        | false => rfl
        | true =>
          have := congrArg UInt8.toNat (beq_iff_eq.mp h)
          rw [hu8] at this
          exact absurd this h1
      rw [hn0, hn1]
      simp only [h0, h1, ↓reduceIte, Bool.false_eq_true]

/-! ## 2. Callee identity -/

/-- The zero-sized constant that `translateCalleeOperand` produces for a call of
intrinsic `k` at the type encoded by `argTy`. -/
def annealFnItemConst (k : AnnealIntrinsic) (argTy : Miri.MIR.TyId) : Miri.MIR.ConstOperand :=
  { span := defaultSpanRef
    userType := none
    value := .Val .ZeroSized (annealFnItemTyId k argTy) }

theorem AnnealIntrinsic.defId_lt (k : AnnealIntrinsic) : k.defId < 64 := by
  cases k <;> decide

theorem AnnealIntrinsic.ofDefId?_defId (k : AnnealIntrinsic) :
    AnnealIntrinsic.ofDefId? k.defId = some k := by
  cases k <;> simp only [AnnealIntrinsic.defId, AnnealIntrinsic.ofDefId?]

/-- Nat arithmetic behind `annealDecodeFnItemTyId_fnItemTyId`. -/
private theorem fnItemTyId_arith (b d a : Nat) (hd : d < 64) :
    b ≤ b + d + 64 * a ∧ (b + d + 64 * a - b) % 64 = d ∧ (b + d + 64 * a - b) / 64 = a := by
  have hsub : b + d + 64 * a - b = d + 64 * a := by
    rw [Nat.add_assoc, Nat.add_sub_cancel_left]
  refine ⟨?_, ?_, ?_⟩
  · rw [Nat.add_assoc]; exact Nat.le_add_right b (d + 64 * a)
  · rw [hsub, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hd]
  · rw [hsub, Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt hd, Nat.zero_add]

/-- `annealDecodeFnItemTyId` inverts `annealFnItemTyId`. -/
theorem annealDecodeFnItemTyId_fnItemTyId (k : AnnealIntrinsic) (argTy : Miri.MIR.TyId) :
    annealDecodeFnItemTyId (annealFnItemTyId k argTy) = some (k, argTy) := by
  obtain ⟨hle, hmod, hdiv⟩ := fnItemTyId_arith annealFnItemTyIdBase k.defId argTy k.defId_lt
  unfold annealDecodeFnItemTyId annealFnItemTyId
  simp only [hle, ↓reduceIte, hmod, hdiv, k.ofDefId?_defId]

/-- Every encoded layout keeps its `TyId`. -/
theorem layoutOfEncodedTyId_ty (tyId : Miri.MIR.TyId) (layouts : LayoutTable) :
    (layoutOfEncodedTyId tyId layouts).ty = tyId := by
  unfold layoutOfEncodedTyId
  split <;> (try rfl) <;> (dsimp only; split <;> rfl)

/-! ## 3. The vendored call pipeline on an intrinsic call -/

/-- A call argument that is not a `Move` is evaluated by the hooks'
`evalOperandAt` and passed by copy (`call.rs::eval_fn_call_argument`). -/
theorem evalFnCallArgumentAt_nonMove {P S C E Other Extern FnABI ArgABI : Type}
    (h : Miri.Interpreter.CallHooks P S C E Other Extern FnABI ArgABI) (choice : C)
    (op : Miri.MIR.Operand) (hop : ∀ p, op ≠ .Move p) (disjoint : Bool)
    (path : Miri.Interpreter.OperandPath) :
    Miri.Interpreter.Call.evalFnCallArgumentAt h choice op disjoint path =
      (do
        let v ← h.evalOperandAt choice path op
        pure (.Copy v)) := by
  cases op with
  | Copy _ => rfl
  | Constant _ => rfl
  | RuntimeChecks _ => rfl
  | Move p => exact absurd rfl (hop p)

/-- `annealEvalOperand` on the callee constant `annealFnItemConst k argTy`:
check that a frame exists and return an uninitialized immediate of the callee's
function item layout. -/
theorem annealEvalOperand_fnItemConst (ld : List LocalDecl) (ly : LayoutTable)
    (k : AnnealIntrinsic) (argTy : Miri.MIR.TyId) :
    annealEvalOperand ld ly (.Constant (annealFnItemConst k argTy)) none =
      (do
        let st ← get
        if st.stack.currentFrame?.isNone then
          throw (.stack .emptyStack)
        pure ⟨.immediate .uninit, layoutOfEncodedTyId (annealFnItemTyId k argTy) ly⟩) :=
  rfl

/-- A failing `annealUnsupportedLeaf` ignores its continuation. -/
theorem annealUnsupportedLeaf_bind {S A B : Type} (leaf : String)
    (f : A → EStateM Miri.Interpreter.StepError S B) :
    (annealUnsupportedLeaf leaf >>= f) = annealUnsupportedLeaf leaf := rfl

/-- A `throw` ignores its continuation. -/
theorem estate_throw_bind {ε S A B : Type} (e : ε) (f : A → EStateM ε S B) :
    ((throw e : EStateM ε S A) >>= f) = throw e := rfl

/-- Bind distributes over `if`. -/
theorem ite_bind_distrib {m : Type → Type} [Monad m] {A B : Type} (c : Prop) [Decidable c]
    (x y : m A) (f : A → m B) :
    ((if c then x else y) >>= f) = if c then x >>= f else y >>= f := by
  split <;> rfl

/-- The generic type arguments `#[T]` of a translated intrinsic callee. -/
theorem genericTypes_single (f : Miri.MIR.GenericArg → Option Miri.MIR.TyId)
    (a : Miri.MIR.GenericArg) :
    Array.filterMap f #[a] 0 1 = (match f a with | some b => #[b] | none => #[]) := by
  cases h : f a <;> simp [h]

/-- **The vendored call pipeline on a two-argument intrinsic call.**
`Call.evalCallTerminator` under `annealCallHooks` evaluates a translated call
of intrinsic `k` (callee `annealFnItemConst k argTy`) whose arguments are not
moves as follows: record the frame index and location, evaluate the
destination place, the callee, and the two arguments (`annealEvalPlace`,
`annealEvalOperand`), run `Intrinsics.eval` on the intrinsic's name, generic
type argument, and argument operands, fail closed (`findMirOrEvalFn`) when
`Intrinsics.eval` leaves the intrinsic to its MIR fallback body, and finally
reject a call with a target that made no progress. -/
theorem evalCallTerminator_intrinsic_two
    (ld : List LocalDecl) (ly : LayoutTable) (k : AnnealIntrinsic) (argTy : Miri.MIR.TyId)
    (hk : k.arity = 2)
    (o₁ o₂ : Miri.MIR.Operand) (hno₁ : ∀ p, o₁ ≠ .Move p) (hno₂ : ∀ p, o₂ ≠ .Move p)
    (dest : Miri.MIR.Place) (target : Option Miri.MIR.BasicBlockId)
    (unwind : Miri.MIR.UnwindAction) :
    Miri.Interpreter.Call.evalCallTerminator (annealCallHooks ld ly) () annealCallBudget
      { sourceInfo := defaultSourceInfo
        kind := .Call (.Constant (annealFnItemConst k argTy))
          #[⟨defaultSpanRef, o₁⟩, ⟨defaultSpanRef, o₂⟩] dest target unwind .Normal
          defaultSpanRef } =
    (do
      let oldIndex ← (annealPlaceHooks ld ly).frameIndex
      let oldFrame ← (annealPlaceHooks ld ly).getFrame
      let destPlace ← annealEvalPlace ld ly dest
      let _ ← annealEvalOperand ld ly (.Constant (annealFnItemConst k argTy)) none
      let v₁ ← annealEvalOperand ld ly o₁ none
      let v₂ ← annealEvalOperand ld ly o₂ none
      let handled ← Miri.Interpreter.Intrinsics.eval (annealIntrinsicHooks ld ly) () k.name
        #[argTy] #[v₁, v₂] destPlace target
      if handled then pure ()
      else (annealUnsupportedLeaf
        "call.findMirOrEvalFn (MIR bodies, including intrinsic fallback bodies)")
      if target.isSome then
        if (← (annealPlaceHooks ld ly).frameIndex) == oldIndex then
          if (← (annealPlaceHooks ld ly).getFrame).location == oldFrame.location then
            throw (.invalidProgram "evaluating this call made no progress")) := by
  simp only [Miri.Interpreter.Call.evalCallTerminator, Miri.Interpreter.Call.evalCalleeAndArgs,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Array.size, List.length_cons,
    List.length_nil, Nat.reduceAdd, Nat.reduceSub, Nat.reduceDiv, List.range'_succ,
    List.range'_zero, List.forIn_cons, List.forIn_nil, List.getElem?_toArray,
    List.getElem?_cons_zero, List.getElem?_cons_succ,
    evalFnCallArgumentAt_nonMove _ _ o₁ hno₁, evalFnCallArgumentAt_nonMove _ _ o₂ hno₂,
    annealCallHooks, annealEvalOperand_fnItemConst, bind_assoc, pure_bind,
    layoutOfEncodedTyId_ty, annealDecodeFnItemTyId_fnItemTyId, hk,
    Miri.Interpreter.Call.initFnCall, Miri.Interpreter.Call.initFnCallStep, annealCallBudget,
    annealCallIntrinsic, Miri.Interpreter.CallInstance.defId,
    Miri.Interpreter.CallInstanceKind.defId, k.ofDefId?_defId,
    Miri.Interpreter.RuntimePlace.stackView_toRuntimePlace,
    Miri.Interpreter.FnArg.copyFnArg, List.map_toArray, List.map_cons, List.map_nil,
    genericTypes_single, List.push_toArray, List.nil_append, List.cons_append,
    ite_bind_distrib, annealUnsupportedLeaf_bind, estate_throw_bind,
    Option.any_some, Bool.not_false, ↓reduceIte, Nat.le_refl, decide_true]
  rfl

/-- **The vendored call pipeline on a one-argument intrinsic call**, as
`evalCallTerminator_intrinsic_two`. -/
theorem evalCallTerminator_intrinsic_one
    (ld : List LocalDecl) (ly : LayoutTable) (k : AnnealIntrinsic) (argTy : Miri.MIR.TyId)
    (hk : k.arity = 1)
    (o₁ : Miri.MIR.Operand) (hno₁ : ∀ p, o₁ ≠ .Move p)
    (dest : Miri.MIR.Place) (target : Option Miri.MIR.BasicBlockId)
    (unwind : Miri.MIR.UnwindAction) :
    Miri.Interpreter.Call.evalCallTerminator (annealCallHooks ld ly) () annealCallBudget
      { sourceInfo := defaultSourceInfo
        kind := .Call (.Constant (annealFnItemConst k argTy))
          #[⟨defaultSpanRef, o₁⟩] dest target unwind .Normal defaultSpanRef } =
    (do
      let oldIndex ← (annealPlaceHooks ld ly).frameIndex
      let oldFrame ← (annealPlaceHooks ld ly).getFrame
      let destPlace ← annealEvalPlace ld ly dest
      let _ ← annealEvalOperand ld ly (.Constant (annealFnItemConst k argTy)) none
      let v₁ ← annealEvalOperand ld ly o₁ none
      let handled ← Miri.Interpreter.Intrinsics.eval (annealIntrinsicHooks ld ly) () k.name
        #[argTy] #[v₁] destPlace target
      if handled then pure ()
      else (annealUnsupportedLeaf
        "call.findMirOrEvalFn (MIR bodies, including intrinsic fallback bodies)")
      if target.isSome then
        if (← (annealPlaceHooks ld ly).frameIndex) == oldIndex then
          if (← (annealPlaceHooks ld ly).getFrame).location == oldFrame.location then
            throw (.invalidProgram "evaluating this call made no progress")) := by
  simp only [Miri.Interpreter.Call.evalCallTerminator, Miri.Interpreter.Call.evalCalleeAndArgs,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Array.size, List.length_cons,
    List.length_nil, Nat.reduceAdd, Nat.reduceSub, Nat.reduceDiv, List.range'_succ,
    List.range'_zero, List.forIn_cons, List.forIn_nil, List.getElem?_toArray,
    List.getElem?_cons_zero,
    evalFnCallArgumentAt_nonMove _ _ o₁ hno₁,
    annealCallHooks, annealEvalOperand_fnItemConst, bind_assoc, pure_bind,
    layoutOfEncodedTyId_ty, annealDecodeFnItemTyId_fnItemTyId, hk,
    Miri.Interpreter.Call.initFnCall, Miri.Interpreter.Call.initFnCallStep, annealCallBudget,
    annealCallIntrinsic, Miri.Interpreter.CallInstance.defId,
    Miri.Interpreter.CallInstanceKind.defId, k.ofDefId?_defId,
    Miri.Interpreter.RuntimePlace.stackView_toRuntimePlace,
    Miri.Interpreter.FnArg.copyFnArg, List.map_toArray, List.map_cons, List.map_nil,
    genericTypes_single, List.push_toArray, List.nil_append,
    ite_bind_distrib, annealUnsupportedLeaf_bind, estate_throw_bind,
    Option.any_some, Bool.not_false, ↓reduceIte, Nat.le_refl, decide_true]
  rfl

/-- **The vendored call pipeline on a three-argument intrinsic call**, as
`evalCallTerminator_intrinsic_two`. -/
theorem evalCallTerminator_intrinsic_three
    (ld : List LocalDecl) (ly : LayoutTable) (k : AnnealIntrinsic) (argTy : Miri.MIR.TyId)
    (hk : k.arity = 3)
    (o₁ o₂ o₃ : Miri.MIR.Operand) (hno₁ : ∀ p, o₁ ≠ .Move p) (hno₂ : ∀ p, o₂ ≠ .Move p)
    (hno₃ : ∀ p, o₃ ≠ .Move p)
    (dest : Miri.MIR.Place) (target : Option Miri.MIR.BasicBlockId)
    (unwind : Miri.MIR.UnwindAction) :
    Miri.Interpreter.Call.evalCallTerminator (annealCallHooks ld ly) () annealCallBudget
      { sourceInfo := defaultSourceInfo
        kind := .Call (.Constant (annealFnItemConst k argTy))
          #[⟨defaultSpanRef, o₁⟩, ⟨defaultSpanRef, o₂⟩, ⟨defaultSpanRef, o₃⟩] dest target unwind
          .Normal defaultSpanRef } =
    (do
      let oldIndex ← (annealPlaceHooks ld ly).frameIndex
      let oldFrame ← (annealPlaceHooks ld ly).getFrame
      let destPlace ← annealEvalPlace ld ly dest
      let _ ← annealEvalOperand ld ly (.Constant (annealFnItemConst k argTy)) none
      let v₁ ← annealEvalOperand ld ly o₁ none
      let v₂ ← annealEvalOperand ld ly o₂ none
      let v₃ ← annealEvalOperand ld ly o₃ none
      let handled ← Miri.Interpreter.Intrinsics.eval (annealIntrinsicHooks ld ly) () k.name
        #[argTy] #[v₁, v₂, v₃] destPlace target
      if handled then pure ()
      else (annealUnsupportedLeaf
        "call.findMirOrEvalFn (MIR bodies, including intrinsic fallback bodies)")
      if target.isSome then
        if (← (annealPlaceHooks ld ly).frameIndex) == oldIndex then
          if (← (annealPlaceHooks ld ly).getFrame).location == oldFrame.location then
            throw (.invalidProgram "evaluating this call made no progress")) := by
  simp only [Miri.Interpreter.Call.evalCallTerminator, Miri.Interpreter.Call.evalCalleeAndArgs,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Array.size, List.length_cons,
    List.length_nil, Nat.reduceAdd, Nat.reduceSub, Nat.reduceDiv, List.range'_succ,
    List.range'_zero, List.forIn_cons, List.forIn_nil, List.getElem?_toArray,
    List.getElem?_cons_zero, List.getElem?_cons_succ,
    evalFnCallArgumentAt_nonMove _ _ o₁ hno₁, evalFnCallArgumentAt_nonMove _ _ o₂ hno₂,
    evalFnCallArgumentAt_nonMove _ _ o₃ hno₃,
    annealCallHooks, annealEvalOperand_fnItemConst, bind_assoc, pure_bind,
    layoutOfEncodedTyId_ty, annealDecodeFnItemTyId_fnItemTyId, hk,
    Miri.Interpreter.Call.initFnCall, Miri.Interpreter.Call.initFnCallStep, annealCallBudget,
    annealCallIntrinsic, Miri.Interpreter.CallInstance.defId,
    Miri.Interpreter.CallInstanceKind.defId, k.ofDefId?_defId,
    Miri.Interpreter.RuntimePlace.stackView_toRuntimePlace,
    List.map_toArray, genericTypes_single, List.push_toArray, List.nil_append,
    ite_bind_distrib, annealUnsupportedLeaf_bind, estate_throw_bind,
    Option.any_some, Bool.not_false, ↓reduceIte]
  rfl

/-- `ControlFlow.evalTerminator` on a `Call` terminator under
`annealTerminatorHooks`: run the vendored call pipeline (`Call.run` of
`Call.evalCallTerminator` under `annealCallHooks`), then reject a call with a
target that left the frame count and the current location unchanged. -/
theorem controlFlow_evalTerminator_call (ld : List LocalDecl) (ly : LayoutTable)
    (term : Miri.MIR.Terminator) {func : Miri.MIR.Operand}
    {args : Array Miri.MIR.SpannedOperand} {dest : Miri.MIR.Place}
    {target : Option Miri.MIR.BasicBlockId} {unwind : Miri.MIR.UnwindAction}
    {cs : Miri.MIR.CallSource} {fs : Miri.MIR.SpanRef}
    (hterm : term.kind = .Call func args dest target unwind cs fs) (m : AnnealStepState) :
    Miri.Interpreter.ControlFlow.evalTerminator (annealTerminatorHooks ld ly) () term m =
      match Miri.Interpreter.Call.evalCallTerminator (annealCallHooks ld ly) () annealCallBudget
          term m with
      | .ok () m' =>
        if target.isSome && m'.stack.frames.size == m.stack.frames.size &&
            m'.stack.currentFrame?.map (·.location) == m.stack.currentFrame?.map (·.location) then
          (m', .error (.invalidProgram "evaluating this call made no progress"))
        else (m', .ok ())
      | .error e m' => (m', .error e) := by
  unfold Miri.Interpreter.ControlFlow.evalTerminator
  rw [hterm]
  dsimp only [Id.run, annealTerminatorHooks, Miri.Interpreter.Call.run]
  cases Miri.Interpreter.Call.evalCallTerminator (annealCallHooks ld ly) () annealCallBudget term m <;>
    rfl

/-! ## 4. `Intrinsics.eval` on each `AnnealIntrinsic` -/

theorem AnnealIntrinsic.name_startsWith_atomic (k : AnnealIntrinsic) :
    k.name.startsWith "atomic_" = false := by
  cases k <;> simp [AnnealIntrinsic.name]

theorem AnnealIntrinsic.name_startsWith_simd (k : AnnealIntrinsic) :
    k.name.startsWith "simd_" = false := by
  cases k <;> simp [AnnealIntrinsic.name]

/-- Public mirror of the private `Intrinsics.scalar`: read an operand as a
scalar. -/
def intrinsicScalar (v : Miri.Interpreter.OpTy AnnealProv) :
    Miri.Interpreter.RvalueM AnnealStepState (Miri.Memory.Scalar AnnealProv) := do
  let immediate ← annealReadImmediate v
  liftScalarResult (immediate.imm.toScalar |>.mapError Miri.Interpreter.ScalarOps.immediateError)

/-- Public mirror of the private `Intrinsics.pointer`. -/
def intrinsicPointer (v : Miri.Interpreter.OpTy AnnealProv) :
    Miri.Interpreter.RvalueM AnnealStepState (Miri.Memory.Pointer (Option AnnealProv)) := do
  let scalar ← intrinsicScalar v
  liftScalarResult (scalar.toPointer annealTargetDataLayout |>.mapError
    Miri.Interpreter.ScalarOps.scalarError)

/-- Public mirror of the private `Intrinsics.usize`. -/
def intrinsicUsize (v : Miri.Interpreter.OpTy AnnealProv) :
    Miri.Interpreter.RvalueM AnnealStepState UInt64 := do
  let scalar ← intrinsicScalar v
  liftScalarResult (scalar.toTargetUsize
    (Miri.ABI.Size.fromBits annealTargetDataLayout.pointerWidth.bits) |>.mapError
      Miri.Interpreter.ScalarOps.scalarError)

/-- Public mirror of the private `Intrinsics.isize`. -/
def intrinsicIsize (v : Miri.Interpreter.OpTy AnnealProv) :
    Miri.Interpreter.RvalueM AnnealStepState Int64 := do
  let scalar ← intrinsicScalar v
  liftScalarResult (scalar.toTargetIsize
    (Miri.ABI.Size.fromBits annealTargetDataLayout.pointerWidth.bits) |>.mapError
      Miri.Interpreter.ScalarOps.scalarError)

/-- The `exact_div` arm of `Intrinsics.eval` under `annealIntrinsicHooks`. -/
def annealExactDivEval (ld : List LocalDecl) (ly : LayoutTable)
    (v₁ v₂ : Miri.Interpreter.OpTy AnnealProv) (dest : Miri.Interpreter.RuntimePlace AnnealProv)
    (target : Option Miri.MIR.BasicBlockId) : Miri.Interpreter.RvalueM AnnealStepState Bool := do
  let left ← annealReadImmediate v₁
  let right ← annealReadImmediate v₂
  if left.layout.ty != right.layout.ty then
    throw (.invalidProgram "integer intrinsic operand types differ")
  let _ ← annealIntegerKindOf left.layout.ty
  let rem ← Miri.Interpreter.ScalarOps.binary (annealScalarOpsHooks ld ly) () .Rem left right
  let rem ← liftScalarResult
    (rem.imm.toScalar |>.mapError Miri.Interpreter.ScalarOps.immediateError)
  let rem ← liftScalarResult
    (rem.toBits left.layout.layout.size |>.mapError Miri.Interpreter.ScalarOps.scalarError)
  if rem != 0 then throw (.undefinedBehavior "exact_div has nonzero remainder")
  let result ← Miri.Interpreter.ScalarOps.binary (annealScalarOpsHooks ld ly) () .Div left right
  annealWriteImmediate result.imm dest
  annealReturnToBlock target
  pure true

theorem intrinsics_eval_exactDiv (ld : List LocalDecl) (ly : LayoutTable)
    (types : Array Miri.MIR.TyId) (v₁ v₂ : Miri.Interpreter.OpTy AnnealProv)
    (dest : Miri.Interpreter.RuntimePlace AnnealProv) (target : Option Miri.MIR.BasicBlockId) :
    Miri.Interpreter.Intrinsics.eval (annealIntrinsicHooks ld ly) () AnnealIntrinsic.exactDiv.name
        types #[v₁, v₂] dest target = annealExactDivEval ld ly v₁ v₂ dest target := by
  unfold Miri.Interpreter.Intrinsics.eval
  simp only [AnnealIntrinsic.name_startsWith_atomic, AnnealIntrinsic.name_startsWith_simd,
    Bool.false_eq_true, ↓reduceIte]
  rfl

/-- The `saturating_add` / `saturating_sub` arm of `Intrinsics.eval` under
`annealIntrinsicHooks`. -/
def annealSaturatingEval (ld : List LocalDecl) (ly : LayoutTable) (isAdd : Bool)
    (v₁ v₂ : Miri.Interpreter.OpTy AnnealProv) (dest : Miri.Interpreter.RuntimePlace AnnealProv)
    (target : Option Miri.MIR.BasicBlockId) : Miri.Interpreter.RvalueM AnnealStepState Bool := do
  let left ← annealReadImmediate v₁
  let right ← annealReadImmediate v₂
  if left.layout.ty != right.layout.ty then
    throw (.invalidProgram "integer intrinsic operand types differ")
  let _ ← annealIntegerKindOf left.layout.ty
  let result ← Miri.Interpreter.ScalarOps.binary (annealScalarOpsHooks ld ly) ()
    (if isAdd then .AddWithOverflow else .SubWithOverflow) left right
  let (value, overflow) ← liftScalarResult
    (result.imm.toScalarPair |>.mapError Miri.Interpreter.ScalarOps.immediateError)
  let overflow ← liftScalarResult
    (overflow.toBool |>.mapError Miri.Interpreter.ScalarOps.scalarError)
  let value ← if !overflow then pure value else do
    let signed ← match left.layout.layout.backendRepr.isSigned with
      | .ok value => pure value
      | .error _ => throw (.invalidProgram "saturating arithmetic needs scalar ABI")
    if signed then
      let first ← liftScalarResult
        (left.imm.toScalar |>.mapError Miri.Interpreter.ScalarOps.immediateError)
      let first ← liftScalarResult
        (first.toInt left.layout.layout.size |>.mapError Miri.Interpreter.ScalarOps.scalarError)
      let bound ← liftScalarResult ((if first >= 0 then left.layout.layout.size.signedIntMax
        else left.layout.layout.size.signedIntMin) |>.mapError fun e => .invalidProgram (toString e))
      liftScalarResult (Miri.Memory.Scalar.fromInt bound left.layout.layout.size |>.mapError
        Miri.Interpreter.ScalarOps.scalarError)
    else
      let bound ← if isAdd then
          liftScalarResult (left.layout.layout.size.unsignedIntMax |>.mapError
            fun e => .invalidProgram (toString e))
        else pure 0
      liftScalarResult (Miri.Memory.Scalar.fromUInt bound left.layout.layout.size |>.mapError
        Miri.Interpreter.ScalarOps.scalarError)
  annealWriteImmediate (.scalar value) dest
  annealReturnToBlock target
  pure true

theorem intrinsics_eval_saturatingAdd (ld : List LocalDecl) (ly : LayoutTable)
    (types : Array Miri.MIR.TyId) (v₁ v₂ : Miri.Interpreter.OpTy AnnealProv)
    (dest : Miri.Interpreter.RuntimePlace AnnealProv) (target : Option Miri.MIR.BasicBlockId) :
    Miri.Interpreter.Intrinsics.eval (annealIntrinsicHooks ld ly) ()
        AnnealIntrinsic.saturatingAdd.name types #[v₁, v₂] dest target =
      annealSaturatingEval ld ly true v₁ v₂ dest target := by
  unfold Miri.Interpreter.Intrinsics.eval
  simp only [AnnealIntrinsic.name_startsWith_atomic, AnnealIntrinsic.name_startsWith_simd,
    Bool.false_eq_true, ↓reduceIte]
  rfl

theorem intrinsics_eval_saturatingSub (ld : List LocalDecl) (ly : LayoutTable)
    (types : Array Miri.MIR.TyId) (v₁ v₂ : Miri.Interpreter.OpTy AnnealProv)
    (dest : Miri.Interpreter.RuntimePlace AnnealProv) (target : Option Miri.MIR.BasicBlockId) :
    Miri.Interpreter.Intrinsics.eval (annealIntrinsicHooks ld ly) ()
        AnnealIntrinsic.saturatingSub.name types #[v₁, v₂] dest target =
      annealSaturatingEval ld ly false v₁ v₂ dest target := by
  unfold Miri.Interpreter.Intrinsics.eval
  simp only [AnnealIntrinsic.name_startsWith_atomic, AnnealIntrinsic.name_startsWith_simd,
    Bool.false_eq_true, ↓reduceIte]
  rfl

/-- The numeric (`IntegerIntrinsic`) arm of `Intrinsics.eval` under
`annealIntrinsicHooks`, for the generic type argument `argTy`. -/
def annealNumericEval (ly : LayoutTable)
    (numeric : Miri.Interpreter.IntegerIntrinsic) (argTy : Miri.MIR.TyId)
    (v : Miri.Interpreter.OpTy AnnealProv) (dest : Miri.Interpreter.RuntimePlace AnnealProv)
    (target : Option Miri.MIR.BasicBlockId) : Miri.Interpreter.RvalueM AnnealStepState Bool := do
  let layout := layoutOfEncodedTyId argTy ly
  let value ← intrinsicScalar v
  let kind ← annealIntegerKindOf layout.ty
  let retKind ← annealIntegerKindOf dest.layout.ty
  let scalar ← liftScalarResult (value.toScalarInt |>.mapError Miri.Interpreter.ScalarOps.scalarError)
  let _ ← liftScalarResult
    (scalar.toBits layout.layout.size |>.mapError Miri.Interpreter.ScalarOps.scalarIntError)
  if (numeric == .bswap || numeric == .bitreverse) && layout != dest.layout then
    throw (.invalidProgram "numeric intrinsic layout mismatch")
  let result ← liftScalarResult (Miri.Interpreter.IntegerIntrinsic.run numeric scalar
    ⟨layout.layout.size, kind⟩ ⟨dest.layout.layout.size, retKind⟩ |>.mapError fun e =>
      match e with
      | .scalar e => Miri.Interpreter.ScalarOps.scalarIntError e
      | .undefinedBehaviorOnZero _ => .undefinedBehavior "nonzero count intrinsic called on zero"
      | .layoutMismatch _ _ => .invalidProgram "numeric intrinsic layout mismatch")
  annealWriteImmediate (.scalar (.fromScalarInt result)) dest
  annealReturnToBlock target
  pure true

/-- The `IntegerIntrinsic` of a one-operand bit intrinsic. -/
def AnnealIntrinsic.numeric? : AnnealIntrinsic → Option Miri.Interpreter.IntegerIntrinsic
  | .ctpop => some .ctpop
  | .ctlz => some .ctlz
  | .ctlzNonzero => some .ctlzNonzero
  | .cttz => some .cttz
  | .cttzNonzero => some .cttzNonzero
  | .bswap => some .bswap
  | .bitreverse => some .bitreverse
  | _ => none

theorem intrinsics_eval_numeric (ld : List LocalDecl) (ly : LayoutTable) (k : AnnealIntrinsic)
    {numeric : Miri.Interpreter.IntegerIntrinsic} (hk : k.numeric? = some numeric)
    (argTy : Miri.MIR.TyId) (v : Miri.Interpreter.OpTy AnnealProv)
    (dest : Miri.Interpreter.RuntimePlace AnnealProv) (target : Option Miri.MIR.BasicBlockId) :
    Miri.Interpreter.Intrinsics.eval (annealIntrinsicHooks ld ly) () k.name #[argTy] #[v] dest
        target = annealNumericEval ly numeric argTy v dest target := by
  cases k <;> simp only [AnnealIntrinsic.numeric?, Option.some.injEq, reduceCtorEq] at hk <;>
    subst hk <;>
    (unfold Miri.Interpreter.Intrinsics.eval
     simp only [AnnealIntrinsic.name_startsWith_atomic, AnnealIntrinsic.name_startsWith_simd,
       Bool.false_eq_true, ↓reduceIte]
     rfl)

/-- The `arith_offset` arm of `Intrinsics.eval` under `annealIntrinsicHooks`,
for the generic type argument `argTy`. -/
def annealArithOffsetEval (ly : LayoutTable) (argTy : Miri.MIR.TyId)
    (v₁ v₂ : Miri.Interpreter.OpTy AnnealProv) (dest : Miri.Interpreter.RuntimePlace AnnealProv)
    (target : Option Miri.MIR.BasicBlockId) : Miri.Interpreter.RvalueM AnnealStepState Bool := do
  let ptr ← intrinsicPointer v₁
  let count ← intrinsicIsize v₂
  let layout := layoutOfEncodedTyId argTy ly
  if layout.layout.size.bytes.toNat >= 2^63 then throw (.invalidProgram "pointee size exceeds i64")
  let offset := Int64.ofInt (count.toInt * Int.ofNat layout.layout.size.bytes.toNat)
  let result ← liftScalarResult (ptr.wrappingSignedOffset offset
    ⟨Miri.ABI.Size.fromBits annealTargetDataLayout.pointerWidth.bits⟩
      |>.mapError fun e => .invalidProgram s!"{repr e}")
  annealWritePointer result dest
  annealReturnToBlock target
  pure true

theorem intrinsics_eval_arithOffset (ld : List LocalDecl) (ly : LayoutTable)
    (argTy : Miri.MIR.TyId) (v₁ v₂ : Miri.Interpreter.OpTy AnnealProv)
    (dest : Miri.Interpreter.RuntimePlace AnnealProv) (target : Option Miri.MIR.BasicBlockId) :
    Miri.Interpreter.Intrinsics.eval (annealIntrinsicHooks ld ly) ()
        AnnealIntrinsic.arithOffset.name #[argTy] #[v₁, v₂] dest target =
      annealArithOffsetEval ly argTy v₁ v₂ dest target := by
  unfold Miri.Interpreter.Intrinsics.eval
  simp only [AnnealIntrinsic.name_startsWith_atomic, AnnealIntrinsic.name_startsWith_simd,
    Bool.false_eq_true, ↓reduceIte]
  rfl

theorem intrinsics_eval_wrappingOffset (ld : List LocalDecl) (ly : LayoutTable)
    (argTy : Miri.MIR.TyId) (v₁ v₂ : Miri.Interpreter.OpTy AnnealProv)
    (dest : Miri.Interpreter.RuntimePlace AnnealProv) (target : Option Miri.MIR.BasicBlockId) :
    Miri.Interpreter.Intrinsics.eval (annealIntrinsicHooks ld ly) ()
        AnnealIntrinsic.wrappingOffset.name #[argTy] #[v₁, v₂] dest target =
      annealArithOffsetEval ly argTy v₁ v₂ dest target :=
  intrinsics_eval_arithOffset ld ly argTy v₁ v₂ dest target

/-- `IntrinsicHooks.pointeeType` of `annealIntrinsicHooks`. -/
def annealPointeeTypeOf (tyId : Miri.MIR.TyId) :
    Miri.Interpreter.RvalueM AnnealStepState Miri.MIR.TyId :=
  match rawPtrPointeeEncodedTyId? tyId with
  | some pointee => pure pointee
  | none => throw (.unsupported s!"pointee of TyId {tyId} is not encoded")

/-- `Intrinsics.writeBytes` under `annealIntrinsicHooks`. -/
def annealWriteBytesEval (ly : LayoutTable)
    (dst byte count : Miri.Interpreter.OpTy AnnealProv) :
    Miri.Interpreter.RvalueM AnnealStepState Unit := do
  let ty ← annealPointeeTypeOf dst.layout.ty
  let layout := layoutOfEncodedTyId ty ly
  let dst ← intrinsicPointer dst
  let byte ← liftScalarResult ((← intrinsicScalar byte).toUInt8 |>.mapError
    Miri.Interpreter.ScalarOps.scalarError)
  let count ← intrinsicUsize count
  let some size := Miri.Interpreter.IntegerOps.computeSizeInBytes layout.layout.size count
      (Miri.ABI.Size.ofBytes 0x7fff_ffff_ffff_ffff)
    | throw (.undefinedBehavior "overflow computing total size of write_bytes")
  annealWriteRepeatedBytes dst byte size

theorem intrinsics_writeBytes_eq (ld : List LocalDecl) (ly : LayoutTable)
    (dst byte count : Miri.Interpreter.OpTy AnnealProv) :
    Miri.Interpreter.Intrinsics.writeBytes (annealIntrinsicHooks ld ly) () dst byte count =
      annealWriteBytesEval ly dst byte count := rfl

theorem intrinsics_eval_writeBytes (ld : List LocalDecl) (ly : LayoutTable)
    (types : Array Miri.MIR.TyId) (v₁ v₂ v₃ : Miri.Interpreter.OpTy AnnealProv)
    (dest : Miri.Interpreter.RuntimePlace AnnealProv) (target : Option Miri.MIR.BasicBlockId) :
    Miri.Interpreter.Intrinsics.eval (annealIntrinsicHooks ld ly) ()
        AnnealIntrinsic.writeBytes.name types #[v₁, v₂, v₃] dest target =
      (do
        annealWriteBytesEval ly v₁ v₂ v₃
        annealReturnToBlock target
        pure true) := by
  unfold Miri.Interpreter.Intrinsics.eval
  simp only [AnnealIntrinsic.name_startsWith_atomic, AnnealIntrinsic.name_startsWith_simd,
    Bool.false_eq_true, ↓reduceIte]
  rfl

end LeanMiriSpec.Correspondence
