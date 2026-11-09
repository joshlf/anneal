/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import LeanMiriSpec.Correspondence.CallLM4_2

/-!
# `arith_offset` Simulation for `LM-4.2`

One-step correspondence between Anneal's `stepMirFn` (`evalArithOffsetCall`) and
`lean-miri`'s `Miri.Interpreter.Step.step` (`Intrinsics.eval` under
`annealStepHooks`) for translated calls of
`core::intrinsics::arith_offset::<T>(ptr, count)` from `StateRelLM3_1`-related
states:

* `annealArithOffsetEval_ok` and `PtrRel.wrapping_offset`: two's-complement
  64-bit wrapping byte-offset arithmetic on positive and negative `isize`
  counts;
* `annealEvalOperand_rawPtr_copy_lm3_1`, `StateRelLM3_1.write_immediate_return`,
  `StateRelLM3_1.write_rawPtr_return`, and
  `StateRelLM3_1.write_rawPtrScalar_return`: raw-pointer operand evaluation and
  destination return-writes;
* `call_intrinsic_offset_simulation`: end-to-end one-step simulation covering
  provenance-tracked `PtrRel` pointers, provenance-free 8-byte scalars, and
  uninitialized or dead operand/destination undefined behavior.
-/

namespace LeanMiriSpec.Correspondence

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

/-! ## 1. `lean-miri` `arith_offset` evaluation and `PtrRel` wrapping offset -/

theorem intrinsicPointer_uninit (lay : Miri.Interpreter.LocalLayout) (m : AnnealStepState) :
    intrinsicPointer ⟨.immediate .uninit, lay⟩ m =
      .error (.undefinedBehavior "read of uninitialized local") m := rfl

theorem intrinsicIsize_uninit (lay : Miri.Interpreter.LocalLayout) (m : AnnealStepState) :
    intrinsicIsize ⟨.immediate .uninit, lay⟩ m =
      .error (.undefinedBehavior "read of uninitialized local") m := rfl

theorem intrinsicPointer_fromPointer (mptr : Miri.Memory.Pointer AnnealProv)
    (lay : Miri.Interpreter.LocalLayout) (m : AnnealStepState) :
    intrinsicPointer
        ⟨.immediate (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr)), lay⟩ m =
      .ok mptr.withOptionalProvenance m := rfl

theorem intrinsicPointer_fromScalarInt {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    (hrel : ScalarRel sc msc) (hsz8 : sc.sizeBytes = 8)
    (lay : Miri.Interpreter.LocalLayout) (m : AnnealStepState) :
    intrinsicPointer ⟨.immediate (.scalar (.fromScalarInt msc)), lay⟩ m =
      .ok (Miri.Memory.Pointer.withoutProvenance (UInt64.ofNat sc.bits)) m := by
  have h := scalar_fromScalarInt_toPointer_eq hrel hsz8
  have hs : intrinsicScalar ⟨.immediate (.scalar (.fromScalarInt msc)), lay⟩ m =
      .ok (.fromScalarInt msc) m := rfl
  unfold intrinsicPointer
  rw [EStateM.bind_eq_ok hs, h]
  rfl

theorem decodeBitsInt_true_8_bounds {b : Nat} (hb : b < 2 ^ 64) :
    -(2 ^ 63 : Int) ≤ decodeBitsInt true 8 b ∧ decodeBitsInt true 8 b < 2 ^ 63 := by
  unfold decodeBitsInt
  simp only [↓reduceIte]
  split <;> omega

theorem scalar_fromScalarInt_toTargetIsize {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    (hrel : ScalarRel sc msc) (hsz8 : sc.sizeBytes = 8) :
    (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) msc).toTargetIsize
        (Miri.ABI.Size.ofBytes 8) =
      .ok (Int64.ofInt (decodeBitsInt true 8 sc.bits)) := by
  have hv8 : ValidScalarBytes 8 := Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  have hsi : (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) msc).toScalarInt =
      .ok msc := rfl
  have hbz : ((Miri.ABI.Size.ofBytes 8).bytes == 0) = false := rfl
  have hsz8' : Miri.ABI.Size.ofBytes 8 = translateSizeBytes sc.sizeBytes := by rw [hsz8]; rfl
  have hlt64 : sc.bits < 2 ^ 64 := by
    have hcan := hrel.canonical
    rw [hsz8] at hcan
    simpa [scalarModulus] using hcan
  have htb : msc.toBits (Miri.ABI.Size.ofBytes 8) = .ok (BitVec.ofNat 128 sc.bits) := by
    rw [hsz8']; exact hrel.toBits_eq
  have hse : (Miri.ABI.Size.ofBytes 8).signExtend (BitVec.ofNat 128 sc.bits) =
      .ok (decodeBitsInt true 8 sc.bits) := by
    rw [show Miri.ABI.Size.ofBytes 8 = translateSizeBytes 8 from rfl,
      size_signExtend_translateSizeBytes hv8]
    have hbv : (BitVec.ofNat 128 sc.bits).toNat = sc.bits := by
      rw [BitVec.toNat_ofNat]; omega
    rw [hbv, Nat.mod_eq_of_lt (by simpa using hlt64)]
  obtain ⟨hlo, hhi⟩ := decodeBitsInt_true_8_bounds hlt64
  unfold Miri.Memory.Scalar.toTargetIsize Miri.Memory.Scalar.toInt Miri.Memory.Scalar.toBits
  simp only [hbz, Bool.false_eq_true, ↓reduceIte, hsi, htb, hse,
    Except.mapError, bind, Except.bind, pure, Except.pure]
  have hfit : ((decodeBitsInt true 8 sc.bits < -(2 ^ 63 : Int)) ||
      (decodeBitsInt true 8 sc.bits ≥ (2 ^ 63 : Int))) = false := by
    rw [Bool.or_eq_false_iff, decide_eq_false_iff_not, decide_eq_false_iff_not]
    exact ⟨by omega, by omega⟩
  rw [hfit]
  rfl

theorem intrinsicIsize_fromScalarInt {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    (hrel : ScalarRel sc msc) (hsz8 : sc.sizeBytes = 8)
    (lay : Miri.Interpreter.LocalLayout) (m : AnnealStepState) :
    intrinsicIsize ⟨.immediate (.scalar (.fromScalarInt msc)), lay⟩ m =
      .ok (Int64.ofInt (decodeBitsInt true 8 sc.bits)) m := by
  have hs : intrinsicScalar ⟨.immediate (.scalar (.fromScalarInt msc)), lay⟩ m =
      .ok (.fromScalarInt msc) m := rfl
  have hsz : Miri.ABI.Size.fromBits annealTargetDataLayout.pointerWidth.bits =
      Miri.ABI.Size.ofBytes 8 := rfl
  unfold intrinsicIsize
  rw [EStateM.bind_eq_ok hs, hsz, scalar_fromScalarInt_toTargetIsize hrel hsz8]
  rfl

/-- Two's-complement 64-bit byte delta for `count : isize` (`b < 2 ^ 64`) and
stride `n`: sign-extending `b` to `Int64`, multiplying by `n` in `Int`, and
converting back to `UInt64` agrees modulo `2 ^ 64` with `UInt64.ofNat (b * n)`,
covering both non-negative and negative `isize` counts. -/
theorem arithOffset_delta_eq {b : Nat} (hb : b < 2 ^ 64) (n : Nat) :
    (Int64.ofInt ((Int64.ofInt (decodeBitsInt true 8 b)).toInt * Int.ofNat n)).toUInt64 =
      UInt64.ofNat (b * n) := by
  obtain ⟨hlo, hhi⟩ := decodeBitsInt_true_8_bounds hb
  rw [Int64.toInt_ofInt_of_le hlo hhi]
  have h1 : ∀ X : Int, (Int64.ofInt X).toUInt64.toBitVec = BitVec.ofInt 64 X := fun _ => rfl
  have h2 : ∀ k : Nat, (UInt64.ofNat k).toBitVec = BitVec.ofNat 64 k := fun _ => rfl
  apply UInt64.toBitVec_inj.mp
  rw [h1, h2]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofInt, BitVec.toNat_ofNat]
  have key : decodeBitsInt true 8 b * Int.ofNat n % ((2 ^ 64 : Nat) : Int) =
      ((b * n % 2 ^ 64 : Nat) : Int) := by
    simp only [Int.ofNat_eq_natCast]
    unfold decodeBitsInt
    simp only [↓reduceIte]
    split
    · omega
    · rw [Int.sub_mul]
      omega
  rw [key, Int.toNat_natCast]

theorem wrappingSignedOffset_arithOffset {Prov : Type} (ptr : Miri.Memory.Pointer Prov)
    (off : Int64) :
    ptr.wrappingSignedOffset off
        ⟨Miri.ABI.Size.fromBits annealTargetDataLayout.pointerWidth.bits⟩ =
      .ok { ptr with offset := Miri.ABI.Size.ofBytes (ptr.offset.bytes + off.toUInt64) } := by
  unfold Miri.Memory.Pointer.wrappingSignedOffset
  exact wrappingOffset_annealPointerArithmetic_eq ptr (Miri.ABI.Size.ofBytes off.toUInt64)

theorem annealArithOffsetEval_ok (ly : LayoutTable) (argTy : Miri.MIR.TyId)
    {v₁ : Miri.Interpreter.OpTy AnnealProv} {ptr : Miri.Memory.Pointer (Option AnnealProv)}
    {countSc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    (lay₂ : Miri.Interpreter.LocalLayout)
    (dest : Miri.Interpreter.RuntimePlace AnnealProv) (target : Option Miri.MIR.BasicBlockId)
    (m : AnnealStepState)
    (hptr : intrinsicPointer v₁ m = .ok ptr m)
    (hrel : ScalarRel countSc msc) (hsz8 : countSc.sizeBytes = 8)
    (hsize : (layoutOfEncodedTyId argTy ly).layout.size.bytes.toNat < 2 ^ 63) :
    annealArithOffsetEval ly argTy v₁ ⟨.immediate (.scalar (.fromScalarInt msc)), lay₂⟩ dest
        target m =
      (do
        annealWritePointer
          { ptr with
            offset := Miri.ABI.Size.ofBytes (ptr.offset.bytes +
              UInt64.ofNat
                (countSc.bits * (layoutOfEncodedTyId argTy ly).layout.size.bytes.toNat)) }
          dest
        annealReturnToBlock target
        pure true) m := by
  have hlt64 : countSc.bits < 2 ^ 64 := by
    have hcan := hrel.canonical
    rw [hsz8] at hcan
    simpa [scalarModulus] using hcan
  have hge : ¬ ((layoutOfEncodedTyId argTy ly).layout.size.bytes.toNat ≥ 2 ^ 63) := by omega
  unfold annealArithOffsetEval
  rw [EStateM.bind_eq_ok hptr, EStateM.bind_eq_ok (intrinsicIsize_fromScalarInt hrel hsz8 lay₂ m)]
  simp only [hge, ↓reduceIte, wrappingSignedOffset_arithOffset, arithOffset_delta_eq hlt64]
  rfl

theorem annealWritePointer_some (off : Miri.ABI.Size) (prov : AnnealProv)
    (dest : Miri.Interpreter.RuntimePlace AnnealProv) :
    annealWritePointer ⟨off, some prov⟩ dest =
      annealWriteImmediate
        (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout ⟨off, prov⟩)) dest := rfl

theorem annealWritePointer_none (a : UInt64) (dest : Miri.Interpreter.RuntimePlace AnnealProv) :
    ∃ msc : Miri.Memory.ScalarInt, ScalarRel ⟨a.toNat, 8⟩ msc ∧
      annealWritePointer ⟨Miri.ABI.Size.ofBytes a, none⟩ dest =
        annealWriteImmediate (.scalar (.fromScalarInt msc)) dest := by
  have hv8 : ValidScalarBytes (⟨a.toNat, 8⟩ : MirAst.ScalarInt).sizeBytes :=
    Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  have hcan : (⟨a.toNat, 8⟩ : MirAst.ScalarInt).bits <
      scalarModulus (⟨a.toNat, 8⟩ : MirAst.ScalarInt).sizeBytes := by
    dsimp only [scalarModulus]
    exact a.toNat_lt_size
  obtain ⟨msc, htry, hrel⟩ := tryFromUInt_of_valid_canonical hv8 hcan
  refine ⟨msc, hrel, ?_⟩
  have hfm : Miri.Memory.Scalar.fromMaybePointer (Prov := AnnealProv) annealTargetDataLayout
      ⟨Miri.ABI.Size.ofBytes a, none⟩ = .ok (.fromScalarInt msc) := by
    with_unfolding_all
      unfold Miri.Memory.Scalar.fromMaybePointer
      change (do
        let scalar ← Miri.Memory.ScalarInt.tryFromUInt (BitVec.ofNat 128 a.toNat)
          (translateSizeBytes (⟨a.toNat, 8⟩ : MirAst.ScalarInt).sizeBytes) |>.mapError _
        match scalar with
        | some scalar => return Miri.Memory.Scalar.fromScalarInt scalar
        | none => throw _) = .ok (.fromScalarInt msc)
      rw [htry]
      rfl
  unfold annealWritePointer
  rw [hfm]

/-- Wrapping byte-offset preservation for `PtrRel`: adding `delta` modulo
`2 ^ 64` to `p.offsetBytes` matches adding `UInt64.ofNat delta` to
`mptr.offset.bytes` whenever the wrapped offset remains below `PtrRel`'s
`2 ^ 32` stack-slot bound. -/
theorem PtrRel.wrapping_offset {allocMap : List AllocMapEntry} {p : ProvenancePtr}
    {mptr : Miri.Memory.Pointer AnnealProv} (h : PtrRel allocMap p mptr) (delta : Nat)
    (hlt : (p.offsetBytes + delta) % 2 ^ 64 < 2 ^ 32) :
    PtrRel allocMap { p with offsetBytes := (p.offsetBytes + delta) % 2 ^ 64 }
      { mptr with offset := Miri.ABI.Size.ofBytes (mptr.offset.bytes + UInt64.ofNat delta) } := by
  cases h with
  | mk allocId borTag hprov hid hoff haddr htarget =>
    refine .mk allocId borTag hprov hid hlt ?_ htarget
    rw [haddr]
    show Miri.ABI.Size.ofBytes (annealStackBaseAddr allocId + UInt64.ofNat p.offsetBytes +
        UInt64.ofNat delta) =
      Miri.ABI.Size.ofBytes (annealStackBaseAddr allocId +
        UInt64.ofNat ((p.offsetBytes + delta) % 2 ^ 64))
    rw [UInt64.add_assoc]
    congr 2
    apply UInt64.toNat_inj.mp
    simp only [UInt64.toNat_add, UInt64.toNat_ofNat']
    have hsize : UInt64.size = 2 ^ 64 := rfl
    omega

/-! ## 2. Raw-pointer operand evaluation and return writes -/

/-- Pre-state scalar `sc` carried by a constant or copied root-local `Operand`
in `locals`, stated directly on operand syntax and `locals` without referencing
step or operand evaluation. -/
def ScalarOperandPreVal (locals : List LocalSlot) (op : MirAst.Operand)
    (sc : MirAst.ScalarInt) : Prop :=
  (∃ cc, op = .constant cc ∧ cc.val = .scalar (.int sc)) ∨
    (∃ idx, op = .copy ⟨idx, []⟩ ∧ get? locals idx = some (.init (.scalar sc)))

theorem WellTypedScalarOperand.prestate_of_evalOperand_ok {body : CapturedMir}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {op : MirAst.Operand} {ty : Ty} (hop : WellTypedScalarOperand body tf op ty)
    {locals : List LocalSlot} {borrows : List BorrowEntry} {globals : List CapturedAllocation}
    {callerLocals : List LocalSlot} {sc : MirAst.ScalarInt}
    (heval : evalOperand locals op borrows globals body.layouts callerLocals =
      .ok (.scalar sc) locals) :
    ScalarOperandPreVal locals op sc := by
  cases hop with
  | constScalar cc sc₀ hval _ _ _ _ _ _ =>
    have heval₀ : evalOperand locals (.constant cc) borrows globals body.layouts callerLocals =
        .ok (.scalar sc₀) locals := by
      unfold evalOperand
      dsimp only
      rw [hval]
      rfl
    rw [heval₀] at heval
    injection heval with hv _
    injection hv with hsc
    subst hsc
    exact Or.inl ⟨cc, rfl, hval⟩
  | copyLocal idx _ _ _ _ =>
    right
    refine ⟨idx, rfl, ?_⟩
    cases hslot : get? locals idx with
    | none => simp [evalOperand, hslot] at heval
    | some slot =>
      cases slot with
      | dead => simp [evalOperand, hslot] at heval
      | uninit => simp [evalOperand, hslot] at heval
      | init v =>
        simp only [evalOperand, readProjectedValue, hslot] at heval
        injection heval with hv _
        subst hv
        rfl

/-- Copy-operand evaluation without `annealReadImmediate` on an immediate
raw-pointer local `ptrIdx` from `StateRelLM3_1`-related states. -/
theorem annealEvalOperand_rawPtr_copy_lm3_1
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf])
    {ptrIdx : Local} {ptrDecl : LocalDecl} {ptrMut : Mutability} {pointeeKind : RigidTy}
    (hdecl : get? body.localDecls ptrIdx = some ptrDecl)
    (hty : ptrDecl.ty.kind = .rawPtr ptrMut pointeeKind)
    (himm : IsImmediateFrameLocal tf ptrIdx) :
    (∃ m' msg,
      evalOperand s.frame.locals (.copy ⟨ptrIdx, []⟩) s.memory.borrows s.memory.globals
        body.layouts s.memory.callerLocals = .ub ∧
      annealEvalOperand body.localDecls body.layouts (translateOperand (.copy ⟨ptrIdx, []⟩))
        none m = .error (.undefinedBehavior msg) m') ∨
    (∃ tf',
      evalOperand s.frame.locals (.copy ⟨ptrIdx, []⟩) s.memory.borrows s.memory.globals
        body.layouts s.memory.callerLocals = .ub ∧
      annealEvalOperand body.localDecls body.layouts (translateOperand (.copy ⟨ptrIdx, []⟩))
        none m = .ok ⟨.immediate .uninit, translateTy ptrDecl.ty body.layouts⟩
          { m with stack := ⟨#[tf']⟩ } ∧
      StateRelLM3_1 body s { m with stack := ⟨#[tf']⟩ } allocMap ∧
      (∀ k : Nat, (tf'.locals[k]?).map Miri.Interpreter.LocalState.value =
        (tf.locals[k]?).map Miri.Interpreter.LocalState.value)) ∨
    (∃ addr maddr tf',
      get? s.frame.locals ptrIdx = some (.init (.scalar addr)) ∧
      addr.sizeBytes = 8 ∧
      ScalarRel addr maddr ∧
      evalOperand s.frame.locals (.copy ⟨ptrIdx, []⟩) s.memory.borrows s.memory.globals
        body.layouts s.memory.callerLocals = .ok (.scalar addr) s.frame.locals ∧
      annealEvalOperand body.localDecls body.layouts (translateOperand (.copy ⟨ptrIdx, []⟩))
        none m = .ok ⟨.immediate (.scalar (.fromScalarInt maddr)),
          translateTy ptrDecl.ty body.layouts⟩ { m with stack := ⟨#[tf']⟩ } ∧
      StateRelLM3_1 body s { m with stack := ⟨#[tf']⟩ } allocMap ∧
      (∀ k : Nat, (tf'.locals[k]?).map Miri.Interpreter.LocalState.value =
        (tf.locals[k]?).map Miri.Interpreter.LocalState.value)) ∨
    (∃ p mptr tf',
      get? s.frame.locals ptrIdx = some (.init (.ptr p 8)) ∧
      PtrRel allocMap p mptr ∧
      evalOperand s.frame.locals (.copy ⟨ptrIdx, []⟩) s.memory.borrows s.memory.globals
        body.layouts s.memory.callerLocals = .ok (.ptr p 8) s.frame.locals ∧
      annealEvalOperand body.localDecls body.layouts (translateOperand (.copy ⟨ptrIdx, []⟩))
        none m = .ok ⟨.immediate (.scalar
          (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr)),
          translateTy ptrDecl.ty body.layouts⟩ { m with stack := ⟨#[tf']⟩ } ∧
      StateRelLM3_1 body s { m with stack := ⟨#[tf']⟩ } allocMap ∧
      (∀ k : Nat, (tf'.locals[k]?).map Miri.Interpreter.LocalState.value =
        (tf.locals[k]?).map Miri.Interpreter.LocalState.value)) := by
  rcases id hstate with ⟨tf₀, hframes₀, _, _, hfr, _, _, _, _, _, _, _⟩
  rw [hframes] at hframes₀
  injection hframes₀ with h₁
  injection h₁ with htf
  subst htf
  obtain ⟨slot, mls, _, hlt_mf, hslot, hmls, hmls_eq, hloc⟩ := hfr.lookup_local hdecl
  have hcache := hloc.layout_eq
  have htr : translateOperand (.copy ⟨ptrIdx, []⟩) = .Copy ⟨ptrIdx, #[]⟩ := rfl
  let tfc := cacheFrameLocalLayout tf ptrIdx hlt_mf (translateTy ptrDecl.ty body.layouts)
  have hstate' := hstate.cache_layout hframes hdecl hlt_mf
  have hvals : ∀ k : Nat,
      (tfc.locals[k]?).map Miri.Interpreter.LocalState.value =
        (tf.locals[k]?).map Miri.Interpreter.LocalState.value := by
    intro k
    simp only [tfc, cacheFrameLocalLayout]
    by_cases hki : ptrIdx = k
    · subst hki
      rw [Array.getElem?_set_self, Array.getElem?_eq_getElem hlt_mf]
      rfl
    · rw [Array.getElem?_set_ne _ hki]
  rcases hloc.rawPtr_immediate_cases hty (himm mls hmls) with
    ⟨hs_dead, hm_dead⟩ | ⟨hs_un, hm_un⟩ |
      ⟨addr, maddr, hs_sc, hsz8, hrel_sc, hm_sc⟩ | ⟨p, mptr, hs_ptr, hptrRel, hm_ptr⟩
  · have hmls' : tf.locals[ptrIdx]'hlt_mf = ⟨.dead, mls.layout⟩ := by
      rw [hmls_eq]; rcases mls with ⟨v0, l0⟩; dsimp only at hm_dead; subst hm_dead; rfl
    left
    refine ⟨{ m with stack := ⟨#[tfc]⟩ }, "read of dead local", ?_, ?_⟩
    · simp [evalOperand, hslot, hs_dead]
    · rw [htr]
      exact annealEvalOperand_copy_dead hframes hlt_mf hdecl hmls' hcache
  · have hmls' : tf.locals[ptrIdx]'hlt_mf = ⟨.live (.immediate .uninit), mls.layout⟩ := by
      rw [hmls_eq]; rcases mls with ⟨v0, l0⟩; dsimp only at hm_un; subst hm_un; rfl
    right; left
    refine ⟨tfc, ?_, ?_, hstate', hvals⟩
    · simp [evalOperand, hslot, hs_un]
    · rw [htr]
      exact annealEvalOperand_copy_live hframes hlt_mf hdecl hmls' hcache
  · have hmls' : tf.locals[ptrIdx]'hlt_mf =
        ⟨.live (.immediate (.scalar (.fromScalarInt maddr))), mls.layout⟩ := by
      rw [hmls_eq]; rcases mls with ⟨v0, l0⟩; dsimp only at hm_sc; subst hm_sc; rfl
    right; right; left
    refine ⟨addr, maddr, tfc, hslot.trans (congrArg some hs_sc), hsz8, hrel_sc, ?_, ?_,
      hstate', hvals⟩
    · simp [evalOperand, readProjectedValue, hslot, hs_sc]
    · rw [htr]
      exact annealEvalOperand_copy_live hframes hlt_mf hdecl hmls' hcache
  · have hmls' : tf.locals[ptrIdx]'hlt_mf =
        ⟨.live (.immediate (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))),
          mls.layout⟩ := by
      rw [hmls_eq]; rcases mls with ⟨v0, l0⟩; dsimp only at hm_ptr; subst hm_ptr; rfl
    right; right; right
    refine ⟨p, mptr, tfc, hslot.trans (congrArg some hs_ptr), hptrRel, ?_, ?_, hstate', hvals⟩
    · simp [evalOperand, readProjectedValue, hslot, hs_ptr]
    · rw [htr]
      exact annealEvalOperand_copy_live hframes hlt_mf hdecl hmls' hcache

/-- Write an immediate intrinsic return value (`retVal` / `newImm`) to an
immediate destination local `dstIdx` (including raw-pointer locals already
holding a `LocalRelLM3_1.rawPtr` value) and relocate to statement `0` of
`targetBb`. -/
theorem StateRelLM3_1.write_immediate_return
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf])
    {dstIdx : Local} {dstDecl : LocalDecl}
    (hdecl : get? body.localDecls dstIdx = some dstDecl)
    (himm : IsImmediateFrameLocal tf dstIdx)
    (retVal : Value) (newImm : Miri.Interpreter.Immediate AnnealProv)
    (hnew_rel : ∀ cachedLay,
      (∀ l ∈ cachedLay, l = translateTy dstDecl.ty body.layouts) →
      LocalRelLM3_1 m.machine allocMap dstDecl body.layouts (.init retVal)
        ⟨.live (.immediate newImm), cachedLay⟩)
    (id0 : Miri.Interpreter.LocalsIdentity) (dstLay : Miri.Interpreter.LocalLayout)
    (targetBb : Nat) :
    (∃ msg m', writePlaceValue s.frame.locals s.memory.borrows ⟨dstIdx, []⟩ retVal = .ub ∧
        (do
          annealWriteImmediate newImm ⟨.local 0 dstIdx none id0, dstLay⟩
          annealReturnToBlock (some targetBb)
          pure true) m = .error (.undefinedBehavior msg) m') ∨
    (∃ locals' tf',
        writePlaceValue s.frame.locals s.memory.borrows ⟨dstIdx, []⟩ retVal = .ok locals' ∧
        (do
          annealWriteImmediate newImm ⟨.local 0 dstIdx none id0, dstLay⟩
          annealReturnToBlock (some targetBb)
          pure true) m = .ok true { m with stack := ⟨#[tf']⟩ } ∧
        tf'.location = .mir ⟨targetBb, 0⟩ ∧
        StateRelLM3_1 body
          { frame := { s.frame with blockIdx := targetBb, stmtIdx := 0, locals := locals' }
            memory := s.memory }
          { m with stack := ⟨#[tf']⟩ } allocMap) := by
  obtain ⟨tf₀, hframes₀, _, _, hfr, hcal, hstack, hprot, hcaller, hbor, _, _⟩ := id hstate
  rw [hframes] at hframes₀
  injection hframes₀ with h₁
  injection h₁ with htf
  subst htf
  obtain ⟨slot, mls, hlt_af, hlt_mf, hslot, hmls, hmls_eq, hloc⟩ := hfr.lookup_local hdecl
  have himm' := himm mls hmls
  have hget : tf.getLocal dstIdx = .ok mls := frame_getLocal_of_getElem? tf dstIdx mls hmls
  have hextract : (slot = .dead ∧ mls.value = .dead) ∨
      (∃ oldImm, mls.value = .live (.immediate oldImm) ∧ slot ≠ .dead) := by
    cases hloc with
    | rawPtr _ mptr₀ _ _ _ _ _ _ =>
      exact Or.inr ⟨.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr₀),
        rfl, nofun⟩
    | base hb =>
      cases hb with
      | indirect _ mp _ _ _ _ => exact absurd rfl (himm' mp)
      | dead _ _ => exact Or.inl ⟨rfl, rfl⟩
      | immediate _ oldImm _ _ hval =>
        have hne_dead : slot ≠ .dead := by
          rcases hval with ⟨rfl, _⟩ | ⟨_, rfl, _⟩ <;> nofun
        exact Or.inr ⟨oldImm, rfl, hne_dead⟩
  rcases hextract with ⟨rfl, hm_dead⟩ | ⟨oldImm, hm_imm, hne_dead⟩
  · have hget_dead : tf.getLocal dstIdx = .ok ⟨.dead, mls.layout⟩ := by
      rcases mls with ⟨v0, l0⟩; dsimp only at hm_dead; subst hm_dead; exact hget
    left
    refine ⟨"write to dead local", m, ?_, ?_⟩
    · simp [writePlaceValue, hslot]
    · rw [EStateM.bind_eq_error (annealWriteImmediate_dead hframes hget_dead)]
  · have hnot_dst := StateRelLM3_1.immediate_not_in_allocMap hstate hframes hslot hne_dead himm
    have hwrite_a : writePlaceValue s.frame.locals s.memory.borrows ⟨dstIdx, []⟩ retVal =
        .ok (s.frame.locals.set dstIdx (.init retVal)) := by
      have hset : set? s.frame.locals dstIdx (.init retVal) =
          some (s.frame.locals.set dstIdx (.init retVal)) := set?_eq_some_set hlt_af _
      unfold writePlaceValue
      dsimp only
      rw [hslot, hset]
      cases slot with
      | dead => exact absurd rfl hne_dead
      | uninit => rfl
      | init _ => rfl
    have hget_live : tf.getLocal dstIdx = .ok ⟨.live (.immediate oldImm), mls.layout⟩ := by
      rcases mls with ⟨v0, l0⟩; dsimp only at hm_imm; subst hm_imm; exact hget
    let tfw : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
      { tf with
        locals := tf.locals.set dstIdx
          { tf.locals[dstIdx]'hlt_mf with value := .live (.immediate newImm) }
          hlt_mf }
    have hwrite_m := annealWriteImmediate_live (val := newImm)
      (id0 := id0) (dstLay := dstLay) hframes hlt_mf hget_live
    have hret := annealReturnToBlock_some (m := { m with stack := ⟨#[tfw]⟩ }) (tf := tfw) rfl
      targetBb
    right
    refine ⟨_, { tfw with location := .mir ⟨targetBb, 0⟩ }, hwrite_a, ?_, rfl, ?_⟩
    · rw [EStateM.bind_eq_ok hwrite_m, EStateM.bind_eq_ok hret]
      rfl
    · have hnew : LocalRelLM3_1 m.machine (allocMap.map id) dstDecl body.layouts
          (.init retVal)
          { tf.locals[dstIdx]'hlt_mf with value := .live (.immediate newImm) } := by
        rw [List.map_id, hmls_eq]
        exact hnew_rel mls.layout hloc.cachedLayout_eq
      have hadv := StateRelLM3_1.advance_write_immediate_perm_map hstate hframes id
        (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) hdecl hnot_dst
        (hlt_d := hlt_mf) (oldImm := oldImm) (by rw [hmls_eq, hm_imm]) hnew
        (mem' := s.memory) hcal hstack hprot hcaller (by rw [List.map_id]; exact hbor) rfl
      rw [List.map_id] at hadv
      exact hadv.relocate rfl targetBb 0

/-- **Write an intrinsic's raw-pointer result and return to the call's target**
(pointer analogue of `StateRelLM3_1.write_scalar_return`). -/
theorem StateRelLM3_1.write_rawPtr_return
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf])
    {dstIdx : Local} {dstDecl : LocalDecl} {dstMut : Mutability} {pointeeKind : RigidTy}
    (hdecl : get? body.localDecls dstIdx = some dstDecl)
    (hty : dstDecl.ty.kind = .rawPtr dstMut pointeeKind)
    (himm : IsImmediateFrameLocal tf dstIdx)
    {r : ProvenancePtr} {mr : Miri.Memory.Pointer AnnealProv}
    (hptr : PtrRel allocMap r mr)
    (id0 : Miri.Interpreter.LocalsIdentity) (dstLay : Miri.Interpreter.LocalLayout)
    (targetBb : Nat) :
    (∃ msg m', writePlaceValue s.frame.locals s.memory.borrows ⟨dstIdx, []⟩ (.ptr r 8) = .ub ∧
        (do
          annealWritePointer mr.withOptionalProvenance ⟨.local 0 dstIdx none id0, dstLay⟩
          annealReturnToBlock (some targetBb)
          pure true) m = .error (.undefinedBehavior msg) m') ∨
    (∃ locals' tf',
        writePlaceValue s.frame.locals s.memory.borrows ⟨dstIdx, []⟩ (.ptr r 8) = .ok locals' ∧
        (do
          annealWritePointer mr.withOptionalProvenance ⟨.local 0 dstIdx none id0, dstLay⟩
          annealReturnToBlock (some targetBb)
          pure true) m = .ok true { m with stack := ⟨#[tf']⟩ } ∧
        tf'.location = .mir ⟨targetBb, 0⟩ ∧
        StateRelLM3_1 body
          { frame := { s.frame with blockIdx := targetBb, stmtIdx := 0, locals := locals' }
            memory := s.memory }
          { m with stack := ⟨#[tf']⟩ } allocMap) := by
  have hw : annealWritePointer mr.withOptionalProvenance ⟨.local 0 dstIdx none id0, dstLay⟩ =
      annealWriteImmediate (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mr))
        ⟨.local 0 dstIdx none id0, dstLay⟩ := rfl
  rw [hw]
  exact hstate.write_immediate_return hframes hdecl himm (.ptr r 8)
    (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mr))
    (fun cachedLay hc => .rawPtr r mr cachedLay dstMut pointeeKind hc hty hptr)
    id0 dstLay targetBb

/-- Write a provenance-free 8-byte address `a` to an immediate raw-pointer
destination local `dstIdx` and return to `targetBb`. -/
theorem StateRelLM3_1.write_rawPtrScalar_return
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf])
    {dstIdx : Local} {dstDecl : LocalDecl} {dstMut : Mutability} {pointeeKind : RigidTy}
    (hdecl : get? body.localDecls dstIdx = some dstDecl)
    (hty : dstDecl.ty.kind = .rawPtr dstMut pointeeKind)
    (himm : IsImmediateFrameLocal tf dstIdx)
    (a : UInt64)
    (id0 : Miri.Interpreter.LocalsIdentity) (dstLay : Miri.Interpreter.LocalLayout)
    (targetBb : Nat) :
    (∃ msg m',
        writePlaceValue s.frame.locals s.memory.borrows ⟨dstIdx, []⟩ (.scalar ⟨a.toNat, 8⟩) = .ub ∧
        (do
          annealWritePointer ⟨Miri.ABI.Size.ofBytes a, none⟩ ⟨.local 0 dstIdx none id0, dstLay⟩
          annealReturnToBlock (some targetBb)
          pure true) m = .error (.undefinedBehavior msg) m') ∨
    (∃ locals' tf',
        writePlaceValue s.frame.locals s.memory.borrows ⟨dstIdx, []⟩ (.scalar ⟨a.toNat, 8⟩) =
          .ok locals' ∧
        (do
          annealWritePointer ⟨Miri.ABI.Size.ofBytes a, none⟩ ⟨.local 0 dstIdx none id0, dstLay⟩
          annealReturnToBlock (some targetBb)
          pure true) m = .ok true { m with stack := ⟨#[tf']⟩ } ∧
        tf'.location = .mir ⟨targetBb, 0⟩ ∧
        StateRelLM3_1 body
          { frame := { s.frame with blockIdx := targetBb, stmtIdx := 0, locals := locals' }
            memory := s.memory }
          { m with stack := ⟨#[tf']⟩ } allocMap) := by
  obtain ⟨msc, hrel, hw⟩ := annealWritePointer_none a ⟨.local 0 dstIdx none id0, dstLay⟩
  rw [hw]
  refine hstate.write_immediate_return hframes hdecl himm (.scalar ⟨a.toNat, 8⟩)
    (.scalar (.fromScalarInt msc)) (fun cachedLay hc => ?_) id0 dstLay targetBb
  refine .base (.immediate (.init (.scalar ⟨a.toNat, 8⟩)) (.scalar (.fromScalarInt msc))
    cachedLay hc (Or.inr ⟨.scalar ⟨a.toNat, 8⟩, rfl, .scalar ⟨a.toNat, 8⟩ msc hrel ?_ ?_ ?_⟩))
  · unfold translateTy; rw [hty]; rfl
  · intro hb; rw [hty] at hb; cases hb
  · intro hc'; rw [hty] at hc'; cases hc'

/-- Writing any return pointer to a dead immediate destination local fails with
undefined behavior in both machines. -/
theorem StateRelLM3_1.write_dead_return
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf])
    {dstIdx : Local} {dstDecl : LocalDecl}
    (hdecl : get? body.localDecls dstIdx = some dstDecl)
    (hdead : get? s.frame.locals dstIdx = some .dead)
    (retVal : Value) (newImm : Miri.Interpreter.Immediate AnnealProv)
    (id0 : Miri.Interpreter.LocalsIdentity) (dstLay : Miri.Interpreter.LocalLayout)
    (targetBb : Nat) :
    writePlaceValue s.frame.locals s.memory.borrows ⟨dstIdx, []⟩ retVal = .ub ∧
      (do
        annealWriteImmediate newImm ⟨.local 0 dstIdx none id0, dstLay⟩
        annealReturnToBlock (some targetBb)
        pure true) m = .error (.undefinedBehavior "write to dead local") m := by
  obtain ⟨tf₀, hframes₀, _, _, hfr, _, _, _, _, _, _, _⟩ := id hstate
  rw [hframes] at hframes₀
  injection hframes₀ with h₁
  injection h₁ with htf
  subst htf
  obtain ⟨slot, mls, _, _, hslot, hmls, _, hloc⟩ := hfr.lookup_local hdecl
  rw [hdead] at hslot
  injection hslot with hs
  subst hs
  have hget : tf.getLocal dstIdx = .ok mls := frame_getLocal_of_getElem? tf dstIdx mls hmls
  cases hloc with
  | base hb =>
    cases hb with
    | indirect _ _ _ _ hne _ => exact absurd rfl hne
    | immediate _ _ _ _ hv => rcases hv with ⟨h, _⟩ | ⟨_, h, _⟩ <;> cases h
    | dead _ _ =>
      refine ⟨by simp [writePlaceValue, hdead], ?_⟩
      rw [EStateM.bind_eq_error (annealWriteImmediate_dead hframes hget)]

/-! ## 3. One-step `arith_offset` / `wrapping_offset` call simulation -/

/-- **`call_intrinsic_offset_simulation` (`LM-4.2`)**: one real step of a
translated call of `{core,std}::intrinsics::arith_offset::<T>(ptr, count)` or
its `{core,std}::intrinsics::wrapping_offset::<T>(ptr, count)` alias
(`hpath : AnnealIntrinsic.ofDefPath? calleePath = some k`,
`hk : k = .arithOffset ∨ k = .wrappingOffset`) in both machines, from any
`StateRelLM3_1`-related states.

Pointee byte size `elemBytes` agrees across Anneal (`helem_anneal`) and
`lean-miri` (`helem_miri`) and satisfies Rust's `isize::MAX` layout invariant
`elemBytes < 2 ^ 63` (`helem_lt`, required because `Intrinsics.eval` rejects
layouts of size `≥ 2 ^ 63` with `StepError.invalidProgram`).

Covers:
* `(a)` `ptrIdx` holding a `PtrRel`-related `.ptr p 8` (`LocalRelLM3_1.rawPtr`)
  and initialized `isize` `countOp` (including negative two's-complement
  counts): both write `(p.offsetBytes + countSc.bits * elemBytes) % 2 ^ 64` with
  provenance preserved and return to `targetBb` in `StateRelLM3_1` whenever the
  wrapped offset stays below `PtrRel`'s `2 ^ 32` stack-slot offset bound
  (`hrange`);
* `(b)` `ptrIdx` holding a provenance-free 8-byte scalar `.scalar addr`
  (`LocalRelLM3_1.base`, e.g., `0 as *const T`) and initialized `isize`
  `countOp`: both write `(addr.bits + countSc.bits * elemBytes) % 2 ^ 64`
  without provenance and return to `targetBb` in `StateRelLM3_1` (with no
  `2 ^ 32` range restriction);
* `(c)` uninitialized or dead `ptrIdx` or `countOp`, or a dead destination
  `dstIdx`: both report undefined behavior (`StepRelLM3_1.ub`). -/
theorem call_intrinsic_offset_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    (hstmt_len : s.frame.stmtIdx = length bb.statements)
    {calleePath : DefPath} {k : AnnealIntrinsic} (hk : k = .arithOffset ∨ k = .wrappingOffset)
    {pointeeKind : RigidTy} {c : ConstOperand} {ptrIdx : Local} {countOp : MirAst.Operand}
    {dstIdx : Local} {targetBb : BasicBlockIdx} {unwind : UnwindAction}
    (hterm : bb.terminator.kind =
      .call (.constant c) [.copy ⟨ptrIdx, []⟩, countOp] ⟨dstIdx, []⟩ (some targetBb) unwind)
    (hc : c.ty.kind = .fnDef calleePath [pointeeKind])
    (hcallee : findCallee? s.memory.callees calleePath = none)
    (hpath : AnnealIntrinsic.ofDefPath? calleePath = some k)
    (hprog : targetBb ≠ s.frame.blockIdx ∨ s.frame.stmtIdx ≠ 0)
    {ptrDecl : LocalDecl} {ptrMut : Mutability}
    (hptrDecl : get? body.localDecls ptrIdx = some ptrDecl)
    (hptrTy : ptrDecl.ty.kind = .rawPtr ptrMut pointeeKind)
    (hptrImm : ∀ tf, m.stack.frames = #[tf] → IsImmediateFrameLocal tf ptrIdx)
    {countTy : Ty} (hcountInt : IsIntegralTy countTy .isize)
    (hcountOp : ∀ tf, m.stack.frames = #[tf] → WellTypedScalarOperand body tf countOp countTy)
    {dstDecl : LocalDecl} {dstMut : Mutability}
    (hdst : get? body.localDecls dstIdx = some dstDecl)
    (hdstTy : dstDecl.ty.kind = .rawPtr dstMut pointeeKind)
    (hdstImm : ∀ tf, m.stack.frames = #[tf] → IsImmediateFrameLocal tf dstIdx)
    {elemBytes : Nat}
    (helem_anneal :
      operandPointeeBytes? body.localDecls body.layouts (.copy ⟨ptrIdx, []⟩) = some elemBytes)
    (helem_miri :
      (layoutOfEncodedTyId (encodeTyId { kind := pointeeKind, layoutIdx := 0 })
        body.layouts).layout.size.bytes.toNat = elemBytes)
    (helem_lt : elemBytes < 2 ^ 63)
    (hrange : ∀ p countSc,
      get? s.frame.locals ptrIdx = some (.init (.ptr p 8)) →
      ScalarOperandPreVal s.frame.locals countOp countSc →
      get? s.frame.locals dstIdx ≠ some .dead →
      (p.offsetBytes + countSc.bits * elemBytes) % 2 ^ 64 < 2 ^ 32) :
    StepRelLM3_1 body m allocMap (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, _, _⟩ := id hstate
  have hk_arity : k.arity = 2 := by rcases hk with rfl | rfl <;> rfl
  have hk_ne : k ≠ .exactDiv := by rcases hk with rfl | rfl <;> nofun
  have hk_name : k.name = AnnealIntrinsic.arithOffset.name := by rcases hk with rfl | rfl <;> rfl
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  have hbeq_len : (s.frame.stmtIdx == length bb.statements) = true := by simp [hstmt_len]
  simp only [hbb, hstmt_none, hbeq_len, ↓reduceIte]
  rw [evalTerminator_inline_intrinsic_call_ofDefPath? hterm hc hcallee hpath hk_ne,
    miri_step_at_terminator hframes hfr.body_eq hfr.location_eq hbb hstmt_none,
    translateTerminator_intrinsic_call_ofDefPath? hterm hc hpath]
  simp only [List.map_cons, List.map_nil]
  have hptr_ne_move : ∀ p, translateOperand (.copy ⟨ptrIdx, []⟩) ≠ .Move p :=
    fun _ h => by cases h
  rw [controlFlow_evalTerminator_call _ _ _ rfl,
    evalCallTerminator_intrinsic_two _ _ k _ hk_arity _ _ hptr_ne_move
      ((hcountOp tf hframes).translate_ne_move),
    hk_name]
  -- Destination place and callee.
  obtain ⟨_, _, _, hlt_mf, _, _, hdmls_eq, hdloc⟩ := hfr.lookup_local hdst
  have hplace := annealEvalPlace_unprojected (body := body) hframes hlt_mf hdst
    (by intro l hl; rw [hdmls_eq] at hl; exact hdloc.cachedLayout_eq l hl)
  have hstate₁ := hstate.cache_layout hframes hdst hlt_mf
  have hcallee_m := annealEvalOperand_fnItemConst_ok body.localDecls body.layouts k
    (encodeTyId { kind := pointeeKind, layoutIdx := 0 })
    (m := { m with stack := ⟨#[cacheFrameLocalLayout tf dstIdx hlt_mf
      (translateTy dstDecl.ty body.layouts)]⟩ }) rfl
  rw [EStateM.bind_eq_ok (annealPlaceHooks_frameIndex_eq hframes),
    EStateM.bind_eq_ok (annealPlaceHooks_getFrame_eq hframes), EStateM.bind_eq_ok hplace,
    EStateM.bind_eq_ok hcallee_m]
  have himm₁ : ∀ j, IsImmediateFrameLocal tf j →
      IsImmediateFrameLocal (cacheFrameLocalLayout tf dstIdx hlt_mf
        (translateTy dstDecl.ty body.layouts)) j :=
    fun j hj => hj.cache_layout hlt_mf _
  let argTyId : Miri.MIR.TyId := encodeTyId { kind := pointeeKind, layoutIdx := 0 }
  let dstPlace : Miri.Interpreter.RuntimePlace AnnealProv :=
    ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩
  have helem_miri_lt : (layoutOfEncodedTyId argTyId body.layouts).layout.size.bytes.toNat <
      2 ^ 63 := by
    dsimp only [argTyId]; rw [helem_miri]; exact helem_lt
  have hinline : ∀ v₁ v₂ L,
      evalInlineIntrinsicCall? s calleePath [.copy ⟨ptrIdx, []⟩, countOp]
        [v₁, v₂] L ⟨dstIdx, []⟩ targetBb body.localDecls body.layouts =
      some (evalArithOffsetCall s (.copy ⟨ptrIdx, []⟩) v₁ v₂ L ⟨dstIdx, []⟩ targetBb
        body.localDecls body.layouts) := by
    intro v₁ v₂ L
    unfold evalInlineIntrinsicCall? integerBitIntrinsicOfPath?
    rcases AnnealIntrinsic.ofDefPath?_cases hpath with hdef | ⟨_, hstd⟩ | ⟨_, hstd⟩
    · rw [stringEq_congr_left hdef, stringEq_congr_left hdef, stringEq_congr_left hdef,
        stringEq_congr_left hdef, stringEq_congr_left hdef, stringEq_congr_left hdef,
        stringEq_congr_left hdef, stringEq_congr_left hdef, stringEq_congr_left hdef,
        stringEq_congr_left hdef, stringEq_congr_left hdef, stringEq_congr_left hdef,
        stringEq_congr_left hdef, stringEq_congr_left hdef, stringEq_congr_left hdef,
        stringEq_congr_left hdef]
      rcases hk with rfl | rfl <;> rfl
    · simp only [stringEq_congr_left hstd]; rfl
    · simp only [stringEq_congr_left hstd]; rfl
  -- Pointer operand `ptrIdx`.
  rcases annealEvalOperand_rawPtr_copy_lm3_1 hstate₁ rfl hptrDecl hptrTy
      (himm₁ ptrIdx (hptrImm tf hframes)) with
    ⟨m₂, msg, ha₁, hm₁⟩ | ⟨tf₂, ha₁, hm₁, hstate₂, hvals₂⟩ |
      ⟨addr, maddr, tf₂, hslot_ptr, haddr8, hrel_addr, ha₁, hm₁, hstate₂, hvals₂⟩ |
      ⟨p, mptr, tf₂, hslot_ptr, hptrRel, ha₁, hm₁, hstate₂, hvals₂⟩
  · -- Dead `ptrIdx`.
    rw [EStateM.bind_eq_error hm₁]
    simp only [evalOperands, ha₁]
    exact .ub _ _
  · -- Uninitialized `ptrIdx`.
    rw [EStateM.bind_eq_ok hm₁]
    have himm₂ : ∀ j, IsImmediateFrameLocal tf j → IsImmediateFrameLocal tf₂ j :=
      fun j hj => IsImmediateFrameLocal.of_values_eq hvals₂ (himm₁ j hj)
    rcases annealEvalOperand_scalar_lm3_1 hstate₂ rfl
        ((hcountOp tf hframes).mono_immediate himm₂) hcountInt.prim with
      ⟨m₃, msg, _, hm₂⟩ | ⟨tf₃, _, hm₂, _, _⟩ | ⟨sc₂, msc₂, tf₃, _, hm₂, _, _, _⟩
    · rw [EStateM.bind_eq_error hm₂]
      simp only [evalOperands, ha₁]
      exact .ub _ _
    · rw [EStateM.bind_eq_ok hm₂]
      have hev : Miri.Interpreter.Intrinsics.eval
          (annealIntrinsicHooks body.localDecls body.layouts) ()
          AnnealIntrinsic.arithOffset.name #[argTyId]
          #[⟨.immediate .uninit, translateTy ptrDecl.ty body.layouts⟩,
            ⟨.immediate .uninit, translateTy countTy body.layouts⟩] dstPlace (some targetBb)
          { m with stack := ⟨#[tf₃]⟩ } =
          .error (.undefinedBehavior "read of uninitialized local")
            { m with stack := ⟨#[tf₃]⟩ } := by
        rw [intrinsics_eval_arithOffset]
        unfold annealArithOffsetEval
        rw [EStateM.bind_eq_error (intrinsicPointer_uninit _ _)]
      rw [EStateM.bind_eq_error hev]
      simp only [evalOperands, ha₁]
      exact .ub _ _
    · rw [EStateM.bind_eq_ok hm₂]
      have hev : Miri.Interpreter.Intrinsics.eval
          (annealIntrinsicHooks body.localDecls body.layouts) ()
          AnnealIntrinsic.arithOffset.name #[argTyId]
          #[⟨.immediate .uninit, translateTy ptrDecl.ty body.layouts⟩,
            ⟨.immediate (.scalar (.fromScalarInt msc₂)), translateTy countTy body.layouts⟩]
          dstPlace (some targetBb) { m with stack := ⟨#[tf₃]⟩ } =
          .error (.undefinedBehavior "read of uninitialized local")
            { m with stack := ⟨#[tf₃]⟩ } := by
        rw [intrinsics_eval_arithOffset]
        unfold annealArithOffsetEval
        rw [EStateM.bind_eq_error (intrinsicPointer_uninit _ _)]
      rw [EStateM.bind_eq_error hev]
      simp only [evalOperands, ha₁]
      exact .ub _ _
  · -- Provenance-free 8-byte scalar `addr` in `ptrIdx`.
    rw [EStateM.bind_eq_ok hm₁]
    have himm₂ : ∀ j, IsImmediateFrameLocal tf j → IsImmediateFrameLocal tf₂ j :=
      fun j hj => IsImmediateFrameLocal.of_values_eq hvals₂ (himm₁ j hj)
    rcases annealEvalOperand_scalar_lm3_1 hstate₂ rfl
        ((hcountOp tf hframes).mono_immediate himm₂) hcountInt.prim with
      ⟨m₃, msg, ha₂, hm₂⟩ | ⟨tf₃, ha₂, hm₂, _, _⟩ |
        ⟨countSc, mcount, tf₃, ha₂, hm₂, hstate₃, hrel₂, hvals₃⟩
    · rw [EStateM.bind_eq_error hm₂]
      simp only [evalOperands, ha₁, ha₂]
      exact .ub _ _
    · rw [EStateM.bind_eq_ok hm₂]
      have hev : Miri.Interpreter.Intrinsics.eval
          (annealIntrinsicHooks body.localDecls body.layouts) ()
          AnnealIntrinsic.arithOffset.name #[argTyId]
          #[⟨.immediate (.scalar (.fromScalarInt maddr)), translateTy ptrDecl.ty body.layouts⟩,
            ⟨.immediate .uninit, translateTy countTy body.layouts⟩]
          dstPlace (some targetBb) { m with stack := ⟨#[tf₃]⟩ } =
          .error (.undefinedBehavior "read of uninitialized local")
            { m with stack := ⟨#[tf₃]⟩ } := by
        rw [intrinsics_eval_arithOffset]
        unfold annealArithOffsetEval
        rw [EStateM.bind_eq_ok (intrinsicPointer_fromScalarInt hrel_addr haddr8 _ _),
          EStateM.bind_eq_error (intrinsicIsize_uninit _ _)]
      rw [EStateM.bind_eq_error hev]
      simp only [evalOperands, ha₁, ha₂]
      exact .ub _ _
    · rw [EStateM.bind_eq_ok hm₂]
      cases hrel₂ with
      | scalar _ _ hrel_c hsz_c _ _ =>
        have hcount8 : countSc.sizeBytes = 8 :=
          translateSizeBytes_inj hrel_c.validBytes (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
            (hsz_c.symm.trans (hcountInt.size_eq body.layouts))
        have hevals : evalOperands s.frame.locals [.copy ⟨ptrIdx, []⟩, countOp] s.memory.borrows
            s.memory.globals body.layouts s.memory.callerLocals =
            .ok [.scalar addr, .scalar countSc] s.frame.locals := by
          simp only [evalOperands, ha₁, ha₂]
        simp only [hevals, hinline]
        let outU64 : UInt64 := UInt64.ofNat addr.bits + UInt64.ofNat (countSc.bits * elemBytes)
        have hout_nat : outU64.toNat = (addr.bits + countSc.bits * elemBytes) % scalarModulus 8 := by
          simp only [outU64, UInt64.toNat_add, UInt64.toNat_ofNat']
          rw [show scalarModulus 8 = 2 ^ 64 from by decide, ← Nat.add_mod]
        have hbeq8 : Nat.beq 8 8 = true := rfl
        have hanneal_ev : evalArithOffsetCall s (.copy ⟨ptrIdx, []⟩) (.scalar addr)
            (.scalar countSc) s.frame.locals ⟨dstIdx, []⟩ targetBb body.localDecls body.layouts =
            intrinsicWriteReturn s s.frame.locals ⟨dstIdx, []⟩ targetBb
              (.scalar ⟨outU64.toNat, 8⟩) := by
          unfold evalArithOffsetCall
          simp only [helem_anneal, hcount8, haddr8, hbeq8, hout_nat]
          rfl
        have hev : Miri.Interpreter.Intrinsics.eval
            (annealIntrinsicHooks body.localDecls body.layouts) ()
            AnnealIntrinsic.arithOffset.name #[argTyId]
            #[⟨.immediate (.scalar (.fromScalarInt maddr)), translateTy ptrDecl.ty body.layouts⟩,
              ⟨.immediate (.scalar (.fromScalarInt mcount)), translateTy countTy body.layouts⟩]
            dstPlace (some targetBb) { m with stack := ⟨#[tf₃]⟩ } =
            (do
              annealWritePointer ⟨Miri.ABI.Size.ofBytes outU64, none⟩ dstPlace
              annealReturnToBlock (some targetBb)
              pure true) { m with stack := ⟨#[tf₃]⟩ } := by
          rw [intrinsics_eval_arithOffset,
            annealArithOffsetEval_ok body.layouts argTyId _ dstPlace (some targetBb) _
              (intrinsicPointer_fromScalarInt hrel_addr haddr8 _ _) hrel_c hcount8 helem_miri_lt]
          dsimp only [argTyId, Miri.Memory.Pointer.withoutProvenance, Miri.ABI.Size.ofBytes, outU64]
          rw [helem_miri]
        have himm₃ : IsImmediateFrameLocal tf₃ dstIdx :=
          IsImmediateFrameLocal.of_values_eq hvals₃ (himm₂ dstIdx (hdstImm tf hframes))
        rcases StateRelLM3_1.write_rawPtrScalar_return hstate₃ rfl hdst hdstTy himm₃ outU64
            tf.localsIdentity (translateTy dstDecl.ty body.layouts) targetBb with
          ⟨msgw, mw, hwa, hwm⟩ | ⟨locals', tf₄, hwa, hwm, hloc₄, hstate₄⟩
        · rw [EStateM.bind_eq_error (hev.trans hwm), hanneal_ev]
          simp only [intrinsicWriteReturn, hwa]
          exact .ub _ _
        · rw [EStateM.bind_eq_ok (hev.trans hwm), hanneal_ev]
          simp only [intrinsicWriteReturn, hwa, intrinsicReturnTo, ↓reduceIte,
            Option.isSome_some]
          rw [EStateM.bind_eq_ok (annealPlaceHooks_frameIndex_eq (m := { m with stack := ⟨#[tf₄]⟩ })
            (tf := tf₄) rfl)]
          simp only [beq_self_eq_true, ↓reduceIte]
          rw [EStateM.bind_eq_ok (annealPlaceHooks_getFrame_eq
            (m := { stack := { frames := #[tf₄] }, machine := m.machine }) (tf := tf₄) rfl)]
          rw [hloc₄, hfr.location_eq, frameLocation_beq_false hprog]
          simp only [Bool.false_eq_true, ↓reduceIte, pure, EStateM.pure,
            stack_currentFrame?_singleton m.stack tf hframes, hframes,
            stack_currentFrame?_singleton (⟨#[tf₄]⟩ : Miri.Interpreter.Stack AnnealProv
              Miri.Interpreter.LocalLayout Unit) tf₄ rfl, Option.map_some, hloc₄, hfr.location_eq,
            option_frameLocation_beq_false hprog, Bool.and_false, Except.map]
          exact .step _ _ hstate₄
  · -- Provenance-tracked `PtrRel` pointer `p` / `mptr` in `ptrIdx`.
    rw [EStateM.bind_eq_ok hm₁]
    have himm₂ : ∀ j, IsImmediateFrameLocal tf j → IsImmediateFrameLocal tf₂ j :=
      fun j hj => IsImmediateFrameLocal.of_values_eq hvals₂ (himm₁ j hj)
    rcases annealEvalOperand_scalar_lm3_1 hstate₂ rfl
        ((hcountOp tf hframes).mono_immediate himm₂) hcountInt.prim with
      ⟨m₃, msg, ha₂, hm₂⟩ | ⟨tf₃, ha₂, hm₂, _, _⟩ |
        ⟨countSc, mcount, tf₃, ha₂, hm₂, hstate₃, hrel₂, hvals₃⟩
    · rw [EStateM.bind_eq_error hm₂]
      simp only [evalOperands, ha₁, ha₂]
      exact .ub _ _
    · rw [EStateM.bind_eq_ok hm₂]
      have hev : Miri.Interpreter.Intrinsics.eval
          (annealIntrinsicHooks body.localDecls body.layouts) ()
          AnnealIntrinsic.arithOffset.name #[argTyId]
          #[⟨.immediate (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr)),
              translateTy ptrDecl.ty body.layouts⟩,
            ⟨.immediate .uninit, translateTy countTy body.layouts⟩]
          dstPlace (some targetBb) { m with stack := ⟨#[tf₃]⟩ } =
          .error (.undefinedBehavior "read of uninitialized local")
            { m with stack := ⟨#[tf₃]⟩ } := by
        rw [intrinsics_eval_arithOffset]
        unfold annealArithOffsetEval
        rw [EStateM.bind_eq_ok (intrinsicPointer_fromPointer mptr _ _),
          EStateM.bind_eq_error (intrinsicIsize_uninit _ _)]
      rw [EStateM.bind_eq_error hev]
      simp only [evalOperands, ha₁, ha₂]
      exact .ub _ _
    · rw [EStateM.bind_eq_ok hm₂]
      cases hrel₂ with
      | scalar _ _ hrel_c hsz_c _ _ =>
        have hcount8 : countSc.sizeBytes = 8 :=
          translateSizeBytes_inj hrel_c.validBytes (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
            (hsz_c.symm.trans (hcountInt.size_eq body.layouts))
        have hevals : evalOperands s.frame.locals [.copy ⟨ptrIdx, []⟩, countOp] s.memory.borrows
            s.memory.globals body.layouts s.memory.callerLocals =
            .ok [.ptr p 8, .scalar countSc] s.frame.locals := by
          simp only [evalOperands, ha₁, ha₂]
        simp only [hevals, hinline]
        let p' : ProvenancePtr :=
          { p with offsetBytes := (p.offsetBytes + countSc.bits * elemBytes) % (2 ^ 64) }
        let mptr' : Miri.Memory.Pointer AnnealProv :=
          { mptr with
            offset := Miri.ABI.Size.ofBytes
              (mptr.offset.bytes + UInt64.ofNat (countSc.bits * elemBytes)) }
        have hmod8 : scalarModulus 8 = 2 ^ 64 := by decide
        have hbeq8 : Nat.beq 8 8 = true := rfl
        have hanneal_ev : evalArithOffsetCall s (.copy ⟨ptrIdx, []⟩) (.ptr p 8) (.scalar countSc)
            s.frame.locals ⟨dstIdx, []⟩ targetBb body.localDecls body.layouts =
            intrinsicWriteReturn s s.frame.locals ⟨dstIdx, []⟩ targetBb (.ptr p' 8) := by
          unfold evalArithOffsetCall
          simp only [helem_anneal, hcount8, hbeq8, hmod8, p']
          rfl
        have hev : Miri.Interpreter.Intrinsics.eval
            (annealIntrinsicHooks body.localDecls body.layouts) ()
            AnnealIntrinsic.arithOffset.name #[argTyId]
            #[⟨.immediate (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr)),
                translateTy ptrDecl.ty body.layouts⟩,
              ⟨.immediate (.scalar (.fromScalarInt mcount)), translateTy countTy body.layouts⟩]
            dstPlace (some targetBb) { m with stack := ⟨#[tf₃]⟩ } =
            (do
              annealWritePointer mptr'.withOptionalProvenance dstPlace
              annealReturnToBlock (some targetBb)
              pure true) { m with stack := ⟨#[tf₃]⟩ } := by
          rw [intrinsics_eval_arithOffset,
            annealArithOffsetEval_ok body.layouts argTyId _ dstPlace (some targetBb) _
              (intrinsicPointer_fromPointer mptr _ _) hrel_c hcount8 helem_miri_lt]
          dsimp only [argTyId, Miri.Memory.Pointer.withOptionalProvenance, mptr']
          rw [helem_miri]
        by_cases hdst_dead : get? s.frame.locals dstIdx = some .dead
        · obtain ⟨hwa, hwm⟩ := StateRelLM3_1.write_dead_return hstate₃ rfl hdst hdst_dead
            (.ptr p' 8) (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr'))
            tf.localsIdentity (translateTy dstDecl.ty body.layouts) targetBb
          have hwm' : (do
              annealWritePointer mptr'.withOptionalProvenance dstPlace
              annealReturnToBlock (some targetBb)
              pure true) { m with stack := ⟨#[tf₃]⟩ } =
              .error (.undefinedBehavior "write to dead local") { m with stack := ⟨#[tf₃]⟩ } :=
            hwm
          rw [EStateM.bind_eq_error (hev.trans hwm'), hanneal_ev]
          simp only [intrinsicWriteReturn, hwa]
          exact .ub _ _
        · have hpre_c := (hcountOp tf hframes).prestate_of_evalOperand_ok ha₂
          have hptr'_rel : PtrRel allocMap p' mptr' :=
            hptrRel.wrapping_offset (countSc.bits * elemBytes)
              (hrange p countSc hslot_ptr hpre_c hdst_dead)
          have himm₃ : IsImmediateFrameLocal tf₃ dstIdx :=
            IsImmediateFrameLocal.of_values_eq hvals₃ (himm₂ dstIdx (hdstImm tf hframes))
          rcases StateRelLM3_1.write_rawPtr_return hstate₃ rfl hdst hdstTy himm₃ hptr'_rel
              tf.localsIdentity (translateTy dstDecl.ty body.layouts) targetBb with
            ⟨msgw, mw, hwa, hwm⟩ | ⟨locals', tf₄, hwa, hwm, hloc₄, hstate₄⟩
          · rw [EStateM.bind_eq_error (hev.trans hwm), hanneal_ev]
            simp only [intrinsicWriteReturn, hwa]
            exact .ub _ _
          · rw [EStateM.bind_eq_ok (hev.trans hwm), hanneal_ev]
            simp only [intrinsicWriteReturn, hwa, intrinsicReturnTo, ↓reduceIte,
              Option.isSome_some]
            rw [EStateM.bind_eq_ok (annealPlaceHooks_frameIndex_eq
              (m := { m with stack := ⟨#[tf₄]⟩ }) (tf := tf₄) rfl)]
            simp only [beq_self_eq_true, ↓reduceIte]
            rw [EStateM.bind_eq_ok (annealPlaceHooks_getFrame_eq
              (m := { stack := { frames := #[tf₄] }, machine := m.machine }) (tf := tf₄) rfl)]
            rw [hloc₄, hfr.location_eq, frameLocation_beq_false hprog]
            simp only [Bool.false_eq_true, ↓reduceIte, pure, EStateM.pure,
              stack_currentFrame?_singleton m.stack tf hframes, hframes,
              stack_currentFrame?_singleton (⟨#[tf₄]⟩ : Miri.Interpreter.Stack AnnealProv
                Miri.Interpreter.LocalLayout Unit) tf₄ rfl, Option.map_some, hloc₄, hfr.location_eq,
              option_frameLocation_beq_false hprog, Bool.and_false, Except.map]
            exact .step _ _ hstate₄

end LeanMiriSpec.Correspondence
