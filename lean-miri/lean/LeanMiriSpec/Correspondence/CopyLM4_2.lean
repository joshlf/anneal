/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import LeanMiriSpec.Correspondence.WriteBytesLM4_2

/-!
# `copy_nonoverlapping` Statement Simulation for `LM-4.2`

One-step correspondence between Anneal's `stepMirFn` (`evalCopyNonOverlapping` /
`evalCopyNonOverlappingWithCount`) and `lean-miri`'s `Miri.Interpreter.Step.step`
(`Intrinsics.evalNondiverging (.CopyNonOverlapping ...)` / `annealCopyEval` /
`annealCheckPtrAlign` / `annealMemCopy`) from `StateRelLM3_1`:

* `step_intrinsic_copyNonOverlapping_simulation` (and its explicit-`allocMap'`
  counterpart `step_intrinsic_copyNonOverlapping_simulation_explicit`) proves
  `StepRelLM3_1` lockstep across:
  1. uninitialized or dead `src`, `dst`, or `count` operands (UB in both);
  2. `count * size_of::<T>() > isize::MAX` (`isizeMaxBytes`) overflow (UB in
     both);
  3. misaligned `src` or `dst` (`offset % align_of::<T>() ≠ 0`), including when
     `count = 0` or `size_of::<T>() = 0` (UB in both);
  4. aligned zero-byte copy (`count * size_of::<T>() = 0`), including on
     provenance-free, dead, or out-of-bounds pointers (no-op step preserving
     `StateRelLM3_1` in both);
  5. positive-byte copy with provenance-free `.scalar` `src` or `dst`, dead
     source or destination stack local, or out-of-bounds byte range (UB in
     both);
  6. positive-byte copy on the same live initialized allocation
     (`e_src.localIdx = e_dst.localIdx` ↔ `e_src.allocId = e_dst.allocId`):
     overlap UB (`AllocError.copyRangesOverlap`) in both;
  7. positive-byte copy between distinct live allocations
     (`e_src.localIdx ≠ e_dst.localIdx`) with initialized `src` and valid
     Tree Borrows permissions: copies `rawBytes`, `InitMask`, and
     `ProvenanceMap` byte-for-byte, invalidates conflicting borrows on `dst`,
     and preserves `StateRelLM3_1`.
* Characterized real-step divergences:
  - `step_intrinsic_copyNonOverlapping_uninit_src_divergence`: copying from an
    `.uninit` scalar stack local rejects in Anneal (`MirStepNode.fail .ub`)
    while `lean-miri`'s untyped `Allocation.copyRepeatedly` copies uninitialized
    bytes (`initialized.noBytesInit`) and returns `.ok true`.
  - `step_intrinsic_copyNonOverlapping_perm_divergence`: copying with a
    `.disabled` source borrow or `.frozen` / `.disabled` destination borrow
    rejects in Anneal (`MirStepNode.fail .ub`) while `lean-miri`'s
    `annealMemoryCopyHooks` (which tracks no Tree Borrows state in `LM-3.1`)
    returns `.ok true`.
-/

namespace LeanMiriSpec.Correspondence

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

/-! ## 1. `lean-miri`'s `copy_nonoverlapping` under `annealIntrinsicHooks` -/

/-- `Intrinsics.copyWith` under `(annealIntrinsicHooks ld ly).memory`. -/
def annealCopyEval (ly : LayoutTable) (source dest count : Miri.Interpreter.OpTy AnnealProv) :
    Miri.Interpreter.RvalueM AnnealStepState Unit := do
  let count ← liftScalarResult
    ((← intrinsicScalar count).toTargetUsize
      (Miri.ABI.Size.fromBits annealTargetDataLayout.pointerWidth.bits) |>.mapError
        Miri.Interpreter.ScalarOps.scalarError)
  let ty ← annealPointeeTypeOf source.layout.ty
  let layout ← pure (layoutOfEncodedTyId ty ly)
  let some size := Miri.Interpreter.IntegerOps.computeSizeInBytes layout.layout.size count
      (Miri.ABI.Size.ofBytes 0x7fff_ffff_ffff_ffff)
    | throw (.undefinedBehavior "overflow computing total size of copy")
  let source ← liftScalarResult
    ((← intrinsicScalar source).toPointer annealTargetDataLayout |>.mapError
      Miri.Interpreter.ScalarOps.scalarError)
  let dest ← liftScalarResult
    ((← intrinsicScalar dest).toPointer annealTargetDataLayout |>.mapError
      Miri.Interpreter.ScalarOps.scalarError)
  annealCheckPtrAlign source layout.layout.align.abi
  annealCheckPtrAlign dest layout.layout.align.abi
  annealMemCopy source dest size true

theorem intrinsics_copyWith_eq (ld : List LocalDecl) (ly : LayoutTable)
    (source dest count : Miri.Interpreter.OpTy AnnealProv) :
    Miri.Interpreter.Intrinsics.copyWith (annealIntrinsicHooks ld ly).memory () source dest count
        true = annealCopyEval ly source dest count := rfl

theorem evalNondiverging_copyNonOverlapping_eq (ld : List LocalDecl) (ly : LayoutTable)
    (src dst count : Miri.MIR.Operand) :
    Miri.Interpreter.Intrinsics.evalNondiverging (annealIntrinsicHooks ld ly) ()
        (.CopyNonOverlapping ⟨src, dst, count⟩) =
      (do
        let source ← annealEvalOperand ld ly src none
        let dest ← annealEvalOperand ld ly dst none
        let cnt ← annealEvalOperand ld ly count none
        annealCopyEval ly source dest cnt) := rfl

theorem annealCopyEval_eq (ly : LayoutTable)
    (source dest count : Miri.Interpreter.OpTy AnnealProv) :
    annealCopyEval ly source dest count =
      (do
        let count ← intrinsicUsize count
        let ty ← annealPointeeTypeOf source.layout.ty
        let layout := layoutOfEncodedTyId ty ly
        let some size := Miri.Interpreter.IntegerOps.computeSizeInBytes layout.layout.size count
            (Miri.ABI.Size.ofBytes 0x7fff_ffff_ffff_ffff)
          | throw (.undefinedBehavior "overflow computing total size of copy")
        let source ← intrinsicPointer source
        let dest ← intrinsicPointer dest
        annealCheckPtrAlign source layout.layout.align.abi
        annealCheckPtrAlign dest layout.layout.align.abi
        annealMemCopy source dest size true) := by
  simp only [annealCopyEval, intrinsicUsize, intrinsicPointer, bind_assoc, pure_bind]

/-! ## 2. Pointee type, size, and alignment agreement -/

/-- Valid ABI alignment pair `(reqAlign, elemAlign)` for primitive / pointer /
unit pointee types on x86-64: `(⟨0⟩, 1)`, `(⟨1⟩, 2)`, `(⟨2⟩, 4)`, `(⟨3⟩, 8)`, or
`(⟨4⟩, 16)`. Every width divides both `2^32` and `2^64`. -/
def ValidCopyAlignPair (reqAlign : Miri.ABI.Align) (elemAlign : Nat) : Prop :=
  (reqAlign = ⟨0⟩ ∧ elemAlign = 1) ∨
  (reqAlign = ⟨1⟩ ∧ elemAlign = 2) ∨
  (reqAlign = ⟨2⟩ ∧ elemAlign = 4) ∨
  (reqAlign = ⟨3⟩ ∧ elemAlign = 8) ∨
  (reqAlign = ⟨4⟩ ∧ elemAlign = 16)

/-- Valid ABI alignment in bytes (`1, 2, 4, 8, 16`). -/
def ValidCopyAlign (al : Nat) : Prop :=
  al = 1 ∨ al = 2 ∨ al = 4 ∨ al = 8 ∨ al = 16

theorem ValidCopyAlignPair.validCopyAlign {reqAlign : Miri.ABI.Align} {elemAlign : Nat}
    (h : ValidCopyAlignPair reqAlign elemAlign) : ValidCopyAlign elemAlign := by
  rcases h with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))

/-- Pointee type, byte size, and ABI alignment agreement across Anneal
(`rigidTyByteSize`, `rigidTyAlignBytes`) and `lean-miri`
(`rawPtrPointeeEncodedTyId?`, `layoutOfEncodedTyId`). -/
structure CopyPointee (ly : LayoutTable) (pointeeKind : RigidTy)
    (ptId : Miri.MIR.TyId) (elemBytes elemAlign : Nat) : Prop where
  wb : WriteBytesPointee ly pointeeKind ptId elemBytes
  anneal_align : rigidTyAlignBytes ly { kind := pointeeKind, layoutIdx := 0 } = some elemAlign
  align_pair : ValidCopyAlignPair (layoutOfEncodedTyId ptId ly).layout.align.abi elemAlign

/-- Every primitive scalar type (`bool`, `char`, `i8`..`i128`, `isize`,
`u8`..`u128`, `usize`) satisfies `CopyPointee` with `elemAlign = elemBytes`. -/
theorem IsPrimScalarTy.copyPointee {ty : Ty} (hprim : IsPrimScalarTy ty) (ly : LayoutTable) :
    ∃ ptId elemBytes, CopyPointee ly ty.kind ptId elemBytes elemBytes := by
  rcases hprim with hk | hk | ⟨it, hk⟩ | ⟨ut, hk⟩
  · rw [hk]
    exact ⟨1, 1, ⟨rfl, rfl, rfl, by decide⟩, rfl, Or.inl ⟨rfl, rfl⟩⟩
  · rw [hk]
    exact ⟨2, 4, ⟨rfl, rfl, rfl, by decide⟩, rfl, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
  · rw [hk]
    cases it with
    | i8 => exact ⟨_, 1, ⟨rfl, rfl, rfl, by decide⟩, rfl, Or.inl ⟨rfl, rfl⟩⟩
    | i16 => exact ⟨_, 2, ⟨rfl, rfl, rfl, by decide⟩, rfl, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
    | i32 => exact ⟨_, 4, ⟨rfl, rfl, rfl, by decide⟩, rfl, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
    | i64 => exact ⟨_, 8, ⟨rfl, rfl, rfl, by decide⟩, rfl, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))⟩
    | i128 => exact ⟨_, 16, ⟨rfl, rfl, rfl, by decide⟩, rfl, Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))⟩
    | isize => exact ⟨_, 8, ⟨rfl, rfl, rfl, by decide⟩, rfl, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))⟩
  · rw [hk]
    cases ut with
    | u8 => exact ⟨_, 1, ⟨rfl, rfl, rfl, by decide⟩, rfl, Or.inl ⟨rfl, rfl⟩⟩
    | u16 => exact ⟨_, 2, ⟨rfl, rfl, rfl, by decide⟩, rfl, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
    | u32 => exact ⟨_, 4, ⟨rfl, rfl, rfl, by decide⟩, rfl, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
    | u64 => exact ⟨_, 8, ⟨rfl, rfl, rfl, by decide⟩, rfl, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))⟩
    | u128 => exact ⟨_, 16, ⟨rfl, rfl, rfl, by decide⟩, rfl, Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))⟩
    | usize => exact ⟨_, 8, ⟨rfl, rfl, rfl, by decide⟩, rfl, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))⟩

/-- Every integral type `IsIntegralTy ty kind` satisfies `CopyPointee` with
`elemBytes = elemAlign = integerKindByteWidth kind`. -/
theorem IsIntegralTy.copyPointee {ty : Ty} {kind : Miri.MIR.IntegerKind}
    (hint : IsIntegralTy ty kind) (ly : LayoutTable) :
    ∃ ptId, CopyPointee ly ty.kind ptId (integerKindByteWidth kind) (integerKindByteWidth kind) := by
  rcases hint with ⟨it, hk⟩ | ⟨ut, hk⟩
  · rw [hk]
    cases it with
    | i8 => exact ⟨_, ⟨rfl, rfl, rfl, by decide⟩, rfl, Or.inl ⟨rfl, rfl⟩⟩
    | i16 => exact ⟨_, ⟨rfl, rfl, rfl, by decide⟩, rfl, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
    | i32 => exact ⟨_, ⟨rfl, rfl, rfl, by decide⟩, rfl, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
    | i64 => exact ⟨_, ⟨rfl, rfl, rfl, by decide⟩, rfl, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))⟩
    | i128 => exact ⟨_, ⟨rfl, rfl, rfl, by decide⟩, rfl, Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))⟩
    | isize => exact ⟨_, ⟨rfl, rfl, rfl, by decide⟩, rfl, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))⟩
  · rw [hk]
    cases ut with
    | u8 => exact ⟨_, ⟨rfl, rfl, rfl, by decide⟩, rfl, Or.inl ⟨rfl, rfl⟩⟩
    | u16 => exact ⟨_, ⟨rfl, rfl, rfl, by decide⟩, rfl, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
    | u32 => exact ⟨_, ⟨rfl, rfl, rfl, by decide⟩, rfl, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
    | u64 => exact ⟨_, ⟨rfl, rfl, rfl, by decide⟩, rfl, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))⟩
    | u128 => exact ⟨_, ⟨rfl, rfl, rfl, by decide⟩, rfl, Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))⟩
    | usize => exact ⟨_, ⟨rfl, rfl, rfl, by decide⟩, rfl, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))⟩

/-- Anneal's `operandPointeeTy` on a copy of an unprojected raw-pointer local. -/
theorem operandPointeeTy_copy_rawPtr {localDecls : List LocalDecl} {layouts : LayoutTable}
    {ptrIdx : Local} {ptrDecl : LocalDecl} {mutability : Mutability} {pointeeKind : RigidTy}
    (hdecl : get? localDecls ptrIdx = some ptrDecl)
    (hty : ptrDecl.ty.kind = .rawPtr mutability pointeeKind) :
    operandPointeeTy localDecls layouts (.copy ⟨ptrIdx, []⟩) =
      some { kind := pointeeKind, layoutIdx := 0 } := by
  simp [operandPointeeTy, operandTy, placeTy, hdecl, resolveProjectedTy, pointeeTyOf, hty]

/-- Anneal's `evalOperand` on a copy of an unprojected local. -/
theorem evalOperand_copy_local_eq (locals : List LocalSlot) (idx : Local)
    (borrows : List BorrowEntry) (globals : List CapturedAllocation) (ly : LayoutTable)
    (callerLocals : List LocalSlot) :
    evalOperand locals (.copy ⟨idx, .nil⟩) borrows globals ly callerLocals =
      match get? locals idx with
      | some (.init v) => .ok v locals
      | _ => .ub := by
  unfold evalOperand
  dsimp only
  cases get? locals idx with
  | none => rfl
  | some slot => cases slot <;> rfl

/-- Raw-pointer operand evaluation without the immediate read (`annealEvalOperand`
on a copy of an immediate raw-pointer local from `StateRelLM3_1`). -/
theorem annealEvalOperand_rawPtr_lm3_1
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf])
    {idx : Local} {decl : LocalDecl} {mutability : Mutability} {pk : RigidTy}
    (hdecl : get? body.localDecls idx = some decl)
    (hty : decl.ty.kind = .rawPtr mutability pk)
    (himm : IsImmediateFrameLocal tf idx) :
    (get? s.frame.locals idx = some .dead ∧
      ∃ m' msg, annealEvalOperand body.localDecls body.layouts (.Copy ⟨idx, #[]⟩) none m =
        .error (.undefinedBehavior msg) m') ∨
    (∃ tf', get? s.frame.locals idx = some .uninit ∧
      annealEvalOperand body.localDecls body.layouts (.Copy ⟨idx, #[]⟩) none m =
        .ok ⟨.immediate .uninit, translateTy decl.ty body.layouts⟩ { m with stack := ⟨#[tf']⟩ } ∧
      StateRelLM3_1 body s { m with stack := ⟨#[tf']⟩ } allocMap ∧
      (∀ k : Nat, (tf'.locals[k]?).map Miri.Interpreter.LocalState.value =
        (tf.locals[k]?).map Miri.Interpreter.LocalState.value)) ∨
    (∃ sc msc tf', get? s.frame.locals idx = some (.init (.scalar sc)) ∧ sc.sizeBytes = 8 ∧
      ScalarRel sc msc ∧
      annealEvalOperand body.localDecls body.layouts (.Copy ⟨idx, #[]⟩) none m =
        .ok ⟨.immediate (.scalar (.fromScalarInt msc)), translateTy decl.ty body.layouts⟩
          { m with stack := ⟨#[tf']⟩ } ∧
      StateRelLM3_1 body s { m with stack := ⟨#[tf']⟩ } allocMap ∧
      (∀ k : Nat, (tf'.locals[k]?).map Miri.Interpreter.LocalState.value =
        (tf.locals[k]?).map Miri.Interpreter.LocalState.value)) ∨
    (∃ ptrVal mptr tf', get? s.frame.locals idx = some (.init (.ptr ptrVal 8)) ∧
      PtrRel allocMap ptrVal mptr ∧
      annealEvalOperand body.localDecls body.layouts (.Copy ⟨idx, #[]⟩) none m =
        .ok ⟨.immediate (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr)),
          translateTy decl.ty body.layouts⟩ { m with stack := ⟨#[tf']⟩ } ∧
      StateRelLM3_1 body s { m with stack := ⟨#[tf']⟩ } allocMap ∧
      (∀ k : Nat, (tf'.locals[k]?).map Miri.Interpreter.LocalState.value =
        (tf.locals[k]?).map Miri.Interpreter.LocalState.value)) := by
  rcases id hstate with ⟨tf₀, hframes₀, _, _, hfr, _, _, _, _, _, _, _⟩
  rw [hframes] at hframes₀
  injection hframes₀ with h₁
  injection h₁ with htf
  subst htf
  obtain ⟨slot, mls, _, hlt_mf, hslot, hmls, hmls_eq, hloc⟩ := hfr.lookup_local hdecl
  have hcache := hloc.cachedLayout_eq
  have hvals : ∀ k : Nat,
      ((cacheFrameLocalLayout tf idx hlt_mf (translateTy decl.ty body.layouts)).locals[k]?).map
        Miri.Interpreter.LocalState.value =
      (tf.locals[k]?).map Miri.Interpreter.LocalState.value := by
    intro k
    simp only [cacheFrameLocalLayout]
    by_cases hki : idx = k
    · subst hki
      rw [Array.getElem?_set_self, Array.getElem?_eq_getElem hlt_mf]
      rfl
    · rw [Array.getElem?_set_ne _ hki]
  have hstate' := hstate.cache_layout hframes hdecl hlt_mf
  rcases hloc.rawPtr_immediate_cases hty (himm mls hmls) with
    ⟨hss, hms⟩ | ⟨hss, hms⟩ | ⟨sc, msc, hss, hsz8, hrel, hms⟩ | ⟨ptrVal, mptr, hss, hptr, hms⟩
  · subst hss
    have hmls' : tf.locals[idx]'hlt_mf = ⟨.dead, mls.layout⟩ := by
      rw [hmls_eq]; rcases mls with ⟨v0, l0⟩; dsimp only at hms; subst hms; rfl
    exact Or.inl ⟨hslot, _, _, annealEvalOperand_copy_dead hframes hlt_mf hdecl hmls' hcache⟩
  · subst hss
    have hmls' : tf.locals[idx]'hlt_mf = ⟨.live (.immediate .uninit), mls.layout⟩ := by
      rw [hmls_eq]; rcases mls with ⟨v0, l0⟩; dsimp only at hms; subst hms; rfl
    exact Or.inr (Or.inl ⟨_, hslot,
      annealEvalOperand_copy_live hframes hlt_mf hdecl hmls' hcache, hstate', hvals⟩)
  · subst hss
    have hmls' : tf.locals[idx]'hlt_mf =
        ⟨.live (.immediate (.scalar (.fromScalarInt msc))), mls.layout⟩ := by
      rw [hmls_eq]; rcases mls with ⟨v0, l0⟩; dsimp only at hms; subst hms; rfl
    exact Or.inr (Or.inr (Or.inl ⟨sc, msc, _, hslot, hsz8, hrel,
      annealEvalOperand_copy_live hframes hlt_mf hdecl hmls' hcache, hstate', hvals⟩))
  · subst hss
    have hmls' : tf.locals[idx]'hlt_mf =
        ⟨.live (.immediate (.scalar
          (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))), mls.layout⟩ := by
      rw [hmls_eq]; rcases mls with ⟨v0, l0⟩; dsimp only at hms; subst hms; rfl
    exact Or.inr (Or.inr (Or.inr ⟨ptrVal, mptr, _, hslot, hptr,
      annealEvalOperand_copy_live hframes hlt_mf hdecl hmls' hcache, hstate', hvals⟩))

/-! ## 3. Pointer alignment checks (`annealCheckPtrAlign` ↔ `ptrValueAligned`) -/

private theorem uint64_mod_eq_zero_iff_of_validCopyAlign {al : Nat} (hal : ValidCopyAlign al)
    (x : Nat) :
    (UInt64.ofNat x % UInt64.ofNat al == 0) = (Nat.beq (Nat.mod x al) 0) := by
  have h1 : (UInt64.ofNat x % UInt64.ofNat al).toNat = (x % 2 ^ 64) % al := by
    rcases hal with rfl | rfl | rfl | rfl | rfl
    · have : UInt64.ofNat x % UInt64.ofNat 1 = 0 := by
        apply UInt64.toNat_inj.mp
        rw [UInt64.toNat_mod]
        change (UInt64.ofNat x).toNat % 1 = 0
        exact Nat.mod_one _
      rw [this, Nat.mod_one]; rfl
    all_goals simp [UInt64.toNat_mod, UInt64.toNat_ofNat]
  have h2 : (x % 2 ^ 64) % al = x % al := by
    rcases hal with rfl | rfl | rfl | rfl | rfl <;> omega
  have hmod_def : Nat.mod x al = x % al := rfl
  rw [hmod_def]
  cases h : Nat.beq (x % al) 0 with
  | true =>
    have hx0 : x % al = 0 := Nat.eq_of_beq_eq_true h
    apply beq_iff_eq.mpr
    apply UInt64.toNat_inj.mp
    rw [h1, h2, hx0]; rfl
  | false =>
    have hx0 : x % al ≠ 0 := by
      intro heq
      rw [heq] at h
      cases h
    cases hb : (UInt64.ofNat x % UInt64.ofNat al == 0) with
    | false => rfl
    | true =>
      have := congrArg UInt64.toNat (beq_iff_eq.mp hb)
      rw [h1, h2] at this
      exact absurd this hx0

private theorem stackBaseAddr_add_mod_eq {al : Nat} (hal : ValidCopyAlign al)
    (id : Miri.Memory.AllocId) (off : Nat) :
    ((annealStackBaseAddr id + UInt64.ofNat off) % UInt64.ofNat al == 0) =
      Nat.beq (Nat.mod off al) 0 := by
  have hbase : (annealStackBaseAddr id).toNat = (id.value.toNat * 2 ^ 32) % 2 ^ 64 := by
    unfold annealStackBaseAddr
    rw [UInt64.toNat_shiftLeft]
    have hsh : id.value.toNat <<< (UInt64.toNat 32 % 64) = id.value.toNat * 2 ^ 32 := by
      change id.value.toNat <<< 32 = id.value.toNat * 2 ^ 32
      simp [Nat.shiftLeft_eq]
    rw [hsh]
  have hsum : (annealStackBaseAddr id + UInt64.ofNat off) =
      UInt64.ofNat (id.value.toNat * 2 ^ 32 + off) := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_add, hbase, UInt64.toNat_ofNat', UInt64.toNat_ofNat']
    omega
  rw [hsum, uint64_mod_eq_zero_iff_of_validCopyAlign hal]
  have hmod : (id.value.toNat * 2 ^ 32 + off) % al = off % al := by
    rcases hal with rfl | rfl | rfl | rfl | rfl <;> omega
  change Nat.beq ((id.value.toNat * 2 ^ 32 + off) % al) 0 = Nat.beq (off % al) 0
  rw [hmod]

/-- Every primitive scalar type's translated ABI alignment satisfies
`ValidCopyAlignPair`. -/
private theorem primScalar_align_pair {ty : Ty} (hprim : IsPrimScalarTy ty)
    (ly : LayoutTable) :
    ∃ al, ValidCopyAlignPair (translateTy ty ly).layout.align.abi al := by
  rw [← hprim.translateTy_layoutIdx ly]
  rcases hprim with hk | hk | ⟨it, hk⟩ | ⟨ut, hk⟩
  · rw [hk]; exact ⟨1, Or.inl ⟨rfl, rfl⟩⟩
  · rw [hk]; exact ⟨4, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
  · rw [hk]; cases it with
    | i8 => exact ⟨1, Or.inl ⟨rfl, rfl⟩⟩
    | i16 => exact ⟨2, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
    | i32 => exact ⟨4, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
    | i64 => exact ⟨8, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))⟩
    | i128 => exact ⟨16, Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))⟩
    | isize => exact ⟨8, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))⟩
  · rw [hk]; cases ut with
    | u8 => exact ⟨1, Or.inl ⟨rfl, rfl⟩⟩
    | u16 => exact ⟨2, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
    | u32 => exact ⟨4, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
    | u64 => exact ⟨8, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))⟩
    | u128 => exact ⟨16, Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))⟩
    | usize => exact ⟨8, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))⟩

/-- `annealAlignLookup` on any `e ∈ allocMap` under `StateRelLM3_1` returns an
`AllocationInfo` whose `align` satisfies `ValidCopyAlignPair`. -/
private theorem annealAlignLookup_validPair_of_mem_allocMap
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hframes : m.stack.frames = #[tf])
    {e : AllocMapEntry} (he : e ∈ allocMap) :
    ∃ info al,
      annealAlignLookup m.machine e.allocId = .ok info ∧
      ValidCopyAlignPair info.align al := by
  obtain ⟨tf₀, hframes₀, _, _, hfr, _, _, _, _, _, halloc, _⟩ := id hstate
  rw [hframes] at hframes₀
  injection hframes₀ with h1; injection h1 with h2; subst h2
  obtain ⟨decl, hdecl, hprim⟩ := halloc.target_decl e he
  obtain ⟨slot, _, _, _, hslot, _, _, _⟩ := hfr.lookup_local hdecl
  obtain ⟨hlive_sync, hdead_sync⟩ := halloc.local_alloc_sync tf hframes e he
  by_cases hd : slot = .dead
  · have hs_dead : get? s.frame.locals e.localIdx = some .dead := hslot.trans (congrArg some hd)
    have hnone := hdead_sync hs_dead
    unfold annealAlignLookup annealLookupAlloc
    rw [hnone]
    exact ⟨_, 1, rfl, Or.inl ⟨rfl, rfl⟩⟩
  · obtain ⟨_, _, hshape_fn⟩ := hlive_sync slot hslot hd
    obtain ⟨la, hfind, _, halign_eq, _⟩ := hshape_fn decl hdecl
    unfold annealAlignLookup annealLookupAlloc
    rw [hfind]
    obtain ⟨al, hpair⟩ := primScalar_align_pair hprim body.layouts
    refine ⟨_, al, rfl, ?_⟩
    dsimp only
    rw [halign_eq]
    exact hpair

/-- Replica of the private `Miri.Memory.checkedAlign` (`Access.lean:109-113`). -/
private def copyAccess_checkedAlign (align : Miri.ABI.Align) :
    Except Miri.Memory.AccessError Miri.ABI.Align := do
  let bytes ← (Miri.ABI.Align.bytes align).mapError Miri.Memory.AccessError.malformedAlignment
  let normalized ← (Miri.ABI.Align.fromBytes bytes).mapError
    Miri.Memory.AccessError.malformedAlignment
  if normalized == align then return align
  throw (.malformedAlignment (.tooLarge bytes))

/-- Replica of the private `Miri.Memory.offsetMisalignment` (`Access.lean:183-188`). -/
private def copyAccess_offsetMisalignment (offset : Miri.ABI.Size) (required : Miri.ABI.Align) :
    Except Miri.Memory.AccessError (Option Miri.Memory.Misalignment) := do
  let required ← copyAccess_checkedAlign required
  let requiredBytes ←
    (Miri.ABI.Align.bytes required).mapError Miri.Memory.AccessError.malformedAlignment
  if requiredBytes == 0 || offset.bytes % requiredBytes == 0 then return none
  return some ⟨Miri.ABI.Align.maxAlignedFactor offset, required⟩

/-- Replica of `Miri.Memory.isPtrMisaligned` (`Access.lean:196-221`) over the
replicas above. -/
private def copyAccess_isPtrMisaligned {Prov ProvExtra : Type}
    [Miri.Memory.PointerProvenance Prov]
    (ptr : Miri.Memory.Pointer (Option Prov)) (required : Miri.ABI.Align)
    (enforceAlignment : Bool)
    (resolve : Miri.Memory.PointerResolver Prov ProvExtra)
    (lookup : Miri.Memory.AllocId →
      Except Miri.Memory.AllocationLookupError Miri.Memory.AllocationInfo)
    (machineAlignmentCheck : Miri.Memory.AllocId → Miri.ABI.Align →
      Miri.Memory.AllocationKind → Miri.ABI.Size → Miri.ABI.Align →
      Option Miri.Memory.Misalignment) :
    Except Miri.Memory.AccessError (Option Miri.Memory.Misalignment) := do
  let required ← copyAccess_checkedAlign required
  let requiredBytes ←
    (Miri.ABI.Align.bytes required).mapError Miri.Memory.AccessError.malformedAlignment
  if !enforceAlignment || requiredBytes == 1 then return none
  let resolved := resolve ptr 0
  match resolved with
  | .error address =>
    copyAccess_offsetMisalignment (Miri.ABI.Size.ofBytes address) required
  | .ok resolved =>
    let info ← match lookup resolved.allocId with
      | .ok info => pure info
      | .error reason => throw (.allocationLookup reason)
    let allocationAlign ← copyAccess_checkedAlign info.align
    if let some misalignment := machineAlignmentCheck resolved.allocId allocationAlign
        info.kind resolved.offset required then
      return some misalignment
    if Miri.Memory.PointerProvenance.offsetIsAddr (Prov := Prov) then
      return ← copyAccess_offsetMisalignment ptr.offset required
    let allocationAlignBytes ←
      (Miri.ABI.Align.bytes allocationAlign).mapError Miri.Memory.AccessError.malformedAlignment
    if allocationAlignBytes < requiredBytes then
      return some ⟨allocationAlign, required⟩
    return ← copyAccess_offsetMisalignment resolved.offset required

private theorem copyAccess_isPtrMisaligned_eq {Prov ProvExtra : Type}
    [Miri.Memory.PointerProvenance Prov]
    (ptr : Miri.Memory.Pointer (Option Prov)) (required : Miri.ABI.Align)
    (enforceAlignment : Bool)
    (resolve : Miri.Memory.PointerResolver Prov ProvExtra)
    (lookup : Miri.Memory.AllocId →
      Except Miri.Memory.AllocationLookupError Miri.Memory.AllocationInfo)
    (machineAlignmentCheck : Miri.Memory.AllocId → Miri.ABI.Align →
      Miri.Memory.AllocationKind → Miri.ABI.Size → Miri.ABI.Align →
      Option Miri.Memory.Misalignment) :
    Miri.Memory.isPtrMisaligned ptr required enforceAlignment resolve lookup
      machineAlignmentCheck =
    copyAccess_isPtrMisaligned ptr required enforceAlignment resolve lookup
      machineAlignmentCheck := rfl

private theorem copyAccess_align_ok {reqAlign : Miri.ABI.Align} {elemAlign : Nat}
    (hpair : ValidCopyAlignPair reqAlign elemAlign) :
    copyAccess_checkedAlign reqAlign = .ok reqAlign ∧
    Miri.ABI.Align.bytes reqAlign = .ok (UInt64.ofNat elemAlign) := by
  rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    exact ⟨rfl, rfl⟩

/-- `annealCheckPtrAlign` on a provenance-free scalar pointer (`sc.sizeBytes = 8`)
agrees with `ptrValueAligned elemAlign (.scalar sc)`. -/
theorem annealCheckPtrAlign_withoutProvenance
    {reqAlign : Miri.ABI.Align} {elemAlign : Nat}
    (hpair : ValidCopyAlignPair reqAlign elemAlign)
    {sc : MirAst.ScalarInt} (hsz8 : sc.sizeBytes = 8)
    (st : AnnealStepState) :
    if ptrValueAligned elemAlign (.scalar sc) = true then
      annealCheckPtrAlign (Miri.Memory.Pointer.withoutProvenance (UInt64.ofNat sc.bits))
        reqAlign st = .ok () st
    else
      annealCheckPtrAlign (Miri.Memory.Pointer.withoutProvenance (UInt64.ofNat sc.bits))
        reqAlign st = .error (.undefinedBehavior "accessing memory with an unaligned pointer") st := by
  have hval := hpair.validCopyAlign
  obtain ⟨hchk, hbytes⟩ := copyAccess_align_ok hpair
  have hnez : Nat.beq elemAlign 0 = false := by
    rcases hval with rfl | rfl | rfl | rfl | rfl <;> rfl
  have hsz_beq : Nat.beq sc.sizeBytes 8 = true := by rw [hsz8]; rfl
  have hpva : ptrValueAligned elemAlign (.scalar sc) = Nat.beq (Nat.mod sc.bits elemAlign) 0 := by
    simp [ptrValueAligned, hsz_beq, hnez]
  rw [hpva]
  unfold annealCheckPtrAlign Miri.Memory.checkPtrAlign
  rw [copyAccess_isPtrMisaligned_eq]
  unfold copyAccess_isPtrMisaligned
  rw [hchk]; dsimp only [bind, Except.bind]
  rw [hbytes]; dsimp only [Except.mapError]
  by_cases h1 : elemAlign = 1
  · subst h1
    have hmod0 : Nat.beq (Nat.mod sc.bits 1) 0 = true := by
      change Nat.beq (sc.bits % 1) 0 = true; rw [Nat.mod_one]; rfl
    rw [hmod0]; rfl
  · have hreq1 : (!true || (UInt64.ofNat elemAlign == 1)) = false := by
      rcases hval with rfl | rfl | rfl | rfl | rfl
      · exact absurd rfl h1
      all_goals rfl
    have hreq0 : (UInt64.ofNat elemAlign == 0) = false := by
      rcases hval with rfl | rfl | rfl | rfl | rfl <;> rfl
    have hres : annealResolvePtr st.machine
        (Miri.Memory.Pointer.withoutProvenance (UInt64.ofNat sc.bits)) 0 =
        .error (UInt64.ofNat sc.bits) := rfl
    rw [hreq1, hres]
    unfold copyAccess_offsetMisalignment
    rw [hchk]; dsimp only [bind, Except.bind]
    rw [hbytes]; dsimp only [Except.mapError]
    rw [hreq0, Bool.false_or]
    have hmod_eq := uint64_mod_eq_zero_iff_of_validCopyAlign hval sc.bits
    have hoff_sz : (Miri.ABI.Size.ofBytes (UInt64.ofNat sc.bits)).bytes = UInt64.ofNat sc.bits := rfl
    rw [hoff_sz, hmod_eq]
    cases Nat.beq (Nat.mod sc.bits elemAlign) 0 <;> rfl

/-- `annealCheckPtrAlign` on a `PtrRel`-tracked stack pointer agrees with
`ptrValueAligned elemAlign (.ptr ptrVal 8)`, whether the target local is live
or dead. -/
theorem annealCheckPtrAlign_stackPtr
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hframes : m.stack.frames = #[tf])
    {reqAlign : Miri.ABI.Align} {elemAlign : Nat}
    (hpair : ValidCopyAlignPair reqAlign elemAlign)
    {ptrVal : ProvenancePtr} {mptr : Miri.Memory.Pointer AnnealProv}
    (hptr : PtrRel allocMap ptrVal mptr) :
    if ptrValueAligned elemAlign (.ptr ptrVal 8) = true then
      annealCheckPtrAlign mptr.withOptionalProvenance reqAlign m = .ok () m
    else
      annealCheckPtrAlign mptr.withOptionalProvenance reqAlign m =
        .error (.undefinedBehavior "accessing memory with an unaligned pointer") m := by
  have hval := hpair.validCopyAlign
  obtain ⟨hchk, hbytes⟩ := copyAccess_align_ok hpair
  have hnez : Nat.beq elemAlign 0 = false := by
    rcases hval with rfl | rfl | rfl | rfl | rfl <;> rfl
  have hpva : ptrValueAligned elemAlign (.ptr ptrVal 8) =
      Nat.beq (Nat.mod ptrVal.offsetBytes elemAlign) 0 := by
    simp [ptrValueAligned, hnez]
  rw [hpva]
  rcases hptr with ⟨_, borTag, hprov_eq, hid_lt, hoff_lt, hmptr_off, ⟨e, he, htag, rfl⟩⟩
  obtain ⟨_, _, _, _, _, _, _, _, _, _, halloc, _⟩ := id hstate
  obtain ⟨_, _, hbase⟩ := halloc.base_addr_valid e he
  obtain ⟨info, infoAl, hlook, hinfoPair⟩ :=
    annealAlignLookup_validPair_of_mem_allocMap hstate hframes he
  obtain ⟨haChk, _⟩ := copyAccess_align_ok hinfoPair
  have hmptr_opt : mptr.withOptionalProvenance =
      ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId + UInt64.ofNat ptrVal.offsetBytes),
        some (.concrete e.allocId borTag)⟩ := by
    rcases mptr with ⟨off, prov⟩
    dsimp only [Miri.Memory.Pointer.withOptionalProvenance] at hprov_eq hmptr_off ⊢
    subst hprov_eq hmptr_off; rfl
  rw [hmptr_opt]
  unfold annealCheckPtrAlign Miri.Memory.checkPtrAlign
  rw [copyAccess_isPtrMisaligned_eq]
  unfold copyAccess_isPtrMisaligned
  rw [hchk]; dsimp only [bind, Except.bind]
  rw [hbytes]; dsimp only [Except.mapError]
  by_cases h1 : elemAlign = 1
  · subst h1
    have hmod0 : Nat.beq (Nat.mod ptrVal.offsetBytes 1) 0 = true := by
      change Nat.beq (ptrVal.offsetBytes % 1) 0 = true; rw [Nat.mod_one]; rfl
    rw [hmod0]; rfl
  · have hreq1 : (!true || (UInt64.ofNat elemAlign == 1)) = false := by
      rcases hval with rfl | rfl | rfl | rfl | rfl
      · exact absurd rfl h1
      all_goals rfl
    have hreq0 : (UInt64.ofNat elemAlign == 0) = false := by
      rcases hval with rfl | rfl | rfl | rfl | rfl <;> rfl
    have hres := PtrRel.resolvePtr_concrete_eq e.allocId borTag ptrVal.offsetBytes
      hid_lt hoff_lt hbase 0
    have hoff_addr : Miri.Memory.PointerProvenance.offsetIsAddr (Prov := AnnealProv) = true := rfl
    rw [hreq1, hres]
    dsimp only
    rw [hlook]; dsimp only [pure, Except.pure]
    rw [haChk]; dsimp only
    rw [hoff_addr]
    unfold copyAccess_offsetMisalignment
    rw [hchk]; dsimp only [bind, Except.bind]
    rw [hbytes]; dsimp only [Except.mapError]
    rw [hreq0, Bool.false_or]
    have hmod_eq := stackBaseAddr_add_mod_eq hval e.allocId ptrVal.offsetBytes
    have hoff_sz :
        (Miri.ABI.Size.ofBytes
          (annealStackBaseAddr e.allocId + UInt64.ofNat ptrVal.offsetBytes)).bytes =
        annealStackBaseAddr e.allocId + UInt64.ofNat ptrVal.offsetBytes := rfl
    rw [hoff_sz, hmod_eq]
    cases Nat.beq (Nat.mod ptrVal.offsetBytes elemAlign) 0 <;> rfl

/-! ## 4. Stack-allocation `Allocation.copyRepeatedly` lemmas -/

private def copyAlloc_raw {P E : Type} (a : Miri.Memory.Allocation P E) : Array UInt8 :=
  Miri.Memory.Allocation.casesOn (motive := fun _ => Array UInt8) a
    (fun raw _ _ _ _ _ _ _ => raw)

private def copyAlloc_mkList : Nat → List UInt8 → List UInt8
  | 0, _ => []
  | k + 1, l => l.headD 0 :: copyAlloc_mkList k l.tail

private theorem copyAlloc_mkList_eq (l : List UInt8) :
    copyAlloc_mkList l.length l = l := by
  induction l with
  | nil => rfl
  | cons b bs ih => exact congrArg (b :: ·) ih

private theorem copyAlloc_array_eta (a : Array UInt8) (n : Nat) (h : a.size = n) :
    a = ⟨copyAlloc_mkList n a.toList⟩ := by
  cases a with
  | mk l =>
    subst h
    exact congrArg Array.mk (copyAlloc_mkList_eq l).symm

private theorem allocation_readScalar_congr {E : Type}
    {A B : Miri.Memory.Allocation AnnealProv E}
    (hraw : copyAlloc_raw A = copyAlloc_raw B)
    (hsz : A.byteSize = B.byteSize)
    (hprov : A.provenanceMap = B.provenanceMap)
    (hmask : A.initializationMask = B.initializationMask)
    (layout : Miri.ABI.TargetDataLayout) (range : Miri.Memory.AllocRange) (rp : Bool) :
    A.readScalar layout range rp = B.readScalar layout range rp := by
  cases A; cases B
  dsimp only [copyAlloc_raw, Miri.Memory.Allocation.byteSize,
    Miri.Memory.Allocation.provenanceMap,
    Miri.Memory.Allocation.initializationMask] at hraw hsz hprov hmask
  subst hraw hsz hprov hmask
  rfl

private def copyAlloc_checkedSlice {P E : Type} (allocation : Miri.Memory.Allocation P E)
    (range : Miri.Memory.AllocRange) : Except Miri.Memory.AllocError (Array UInt8) := do
  if (copyAlloc_raw allocation).size != allocation.byteSize.bytes.toNat then
    throw (.storageLengthMismatch allocation.byteSize (copyAlloc_raw allocation).size)
  let finish ← range.endExclusive |>.mapError Miri.Memory.AllocError.memory
  if range.start.bytes > finish.bytes || finish.bytes > allocation.byteSize.bytes then
    throw (.outOfBounds range allocation.byteSize)
  return (copyAlloc_raw allocation).extract range.start.bytes.toNat finish.bytes.toNat

private theorem copyAlloc_getBytesUnchecked_eq {P E : Type}
    (allocation : Miri.Memory.Allocation P E) (range : Miri.Memory.AllocRange) :
    Miri.Memory.Allocation.getBytesUnchecked allocation range =
      copyAlloc_checkedSlice allocation range := rfl

private theorem copyAlloc_allocRange_end (size : Miri.ABI.Size) :
    (Miri.Memory.allocRange Miri.ABI.Size.ZERO size).endExclusive = .ok size := by
  cases size
  simp [Miri.Memory.AllocRange.endExclusive, Miri.Memory.AllocRange.end, Miri.Memory.allocRange,
    Miri.ABI.Size.ZERO, Miri.ABI.Size.add, Miri.ABI.Size.ofBytes, Except.mapError]

private theorem prov_prepareCopy_new {n : Nat} (hn : ValidScalarBytes n) (raw : Array UInt8) :
    (Miri.Memory.ProvenanceMap.new (Prov := AnnealProv)).prepareCopy
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes n))
      raw (Miri.ABI.Size.ofBytes 8) = .ok ⟨#[], #[]⟩ := by
  rcases hn with rfl | rfl | rfl | rfl | rfl <;> with_unfolding_all rfl

private theorem prov_clear_new {n : Nat} (hn : ValidScalarBytes n) (raw : Array UInt8) :
    Miri.Memory.ProvenanceMap.clear
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes n))
      raw (Miri.ABI.Size.ofBytes 8) (Miri.Memory.ProvenanceMap.new (Prov := AnnealProv)) =
    EStateM.Result.ok () Miri.Memory.ProvenanceMap.new := by
  rcases hn with rfl | rfl | rfl | rfl | rfl <;> with_unfolding_all rfl

private theorem prov_applyCopy_empty_fn (range : Miri.Memory.AllocRange) (cnt : UInt64) :
    Miri.Memory.ProvenanceMap.applyCopy (Prov := AnnealProv) ⟨#[], #[]⟩ range cnt =
      fun st => EStateM.Result.ok () st := by
  funext st
  with_unfolding_all rfl

private theorem initMask_prepareCopy_true {n : Nat} (hn : ValidScalarBytes n) :
    (Miri.Memory.InitMask.new (translateSizeBytes n) true).prepareCopy
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes n)) =
    .ok ⟨true, #[UInt64.ofNat n]⟩ := by
  rcases hn with rfl | rfl | rfl | rfl | rfl <;> with_unfolding_all rfl

private def CopyRepeatedlyPost {E : Type} (n : Nat)
    (S D : Miri.Memory.Allocation AnnealProv E) : Prop :=
  ∃ alloc' : Miri.Memory.Allocation AnnealProv E,
    Miri.Memory.Allocation.copyRepeatedly S
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes n))
      Miri.ABI.Size.ZERO 1 (Miri.ABI.Size.ofBytes 8) false true D = .ok () alloc' ∧
    alloc'.align = D.align ∧
    copyAlloc_raw alloc' = copyAlloc_raw S ∧
    alloc'.byteSize = translateSizeBytes n ∧
    alloc'.len = (translateSizeBytes n).bytes.toNat ∧
    alloc'.mutability = .Mut ∧
    alloc'.provenanceMap = Miri.Memory.ProvenanceMap.new ∧
    alloc'.initializationMask = Miri.Memory.InitMask.new (translateSizeBytes n) true

private theorem array_extract_zero_zero (a : Array UInt8) : a.extract 0 0 = #[] := by simp

private theorem array_extract_self_size (a : Array UInt8) (n : Nat) (h : a.size = n) :
    a.extract n a.size = #[] := by
  subst h; simp

private theorem initMask_applyCopy_true {n : Nat} (hn : ValidScalarBytes n) :
    (Miri.Memory.InitMask.new (translateSizeBytes n) true).applyCopy
      ⟨true, #[UInt64.ofNat n]⟩
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes n)) 1 =
    .ok (Miri.Memory.InitMask.new (translateSizeBytes n) true) := by
  rcases hn with rfl | rfl | rfl | rfl | rfl <;> with_unfolding_all rfl

private theorem copyRepeatedly_core {E : Type} {n : Nat} (hn : ValidScalarBytes n) (bD : Bool)
    {S D : Miri.Memory.Allocation AnnealProv E}
    (hszS : S.byteSize = translateSizeBytes n)
    (hlenS : S.len = (translateSizeBytes n).bytes.toNat)
    (hmutS : S.mutability = .Mut)
    (hprovS : S.provenanceMap = Miri.Memory.ProvenanceMap.new)
    (hmaskS : S.initializationMask = Miri.Memory.InitMask.new (translateSizeBytes n) true)
    (hszD : D.byteSize = translateSizeBytes n)
    (hlenD : D.len = (translateSizeBytes n).bytes.toNat)
    (hmutD : D.mutability = .Mut)
    (hprovD : D.provenanceMap = Miri.Memory.ProvenanceMap.new)
    (hmaskD : D.initializationMask = Miri.Memory.InitMask.new (translateSizeBytes n) bD) :
    CopyRepeatedlyPost n S D := by
  have hn_eq : (translateSizeBytes n).bytes.toNat = n := by
    rcases hn with rfl | rfl | rfl | rfl | rfl <;> rfl
  have hmul : (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes n)).size.mul 1 =
      .ok (translateSizeBytes n) := by
    rcases hn with rfl | rfl | rfl | rfl | rfl <;> rfl
  have hsliceS : Miri.Memory.Allocation.getBytesUnchecked S
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes n)) =
      .ok (copyAlloc_raw S) := by
    rw [copyAlloc_getBytesUnchecked_eq]; unfold copyAlloc_checkedSlice
    have hend := copyAlloc_allocRange_end (translateSizeBytes n)
    have hrawsz : (copyAlloc_raw S).size = (translateSizeBytes n).bytes.toNat := hlenS
    change (if (copyAlloc_raw S).size != S.byteSize.bytes.toNat then _ else _) = _
    simp only [hrawsz, hszS, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hend,
      Except.mapError, bind, Except.bind]
    simp [Miri.Memory.allocRange, Miri.ABI.Size.ZERO, pure, Except.pure, ← hrawsz]
  have hsliceD : Miri.Memory.Allocation.getBytesUnchecked D
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes n)) =
      .ok (copyAlloc_raw D) := by
    rw [copyAlloc_getBytesUnchecked_eq]; unfold copyAlloc_checkedSlice
    have hend := copyAlloc_allocRange_end (translateSizeBytes n)
    have hrawsz : (copyAlloc_raw D).size = (translateSizeBytes n).bytes.toNat := hlenD
    change (if (copyAlloc_raw D).size != D.byteSize.bytes.toNat then _ else _) = _
    simp only [hrawsz, hszD, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hend,
      Except.mapError, bind, Except.bind]
    simp [Miri.Memory.allocRange, Miri.ABI.Size.ZERO, pure, Except.pure, ← hrawsz]
  unfold Miri.Memory.Allocation.getBytesUnchecked at hsliceS hsliceD
  cases S with | _ rawS szS provS maskS alignS mutS extraS nbS =>
  cases D with | _ rawD szD provD maskD alignD mutD extraD nbD =>
  change szS = _ at hszS; change rawS.size = _ at hlenS
  change mutS = _ at hmutS; change provS = _ at hprovS; change maskS = _ at hmaskS
  change szD = _ at hszD; change rawD.size = _ at hlenD
  change mutD = _ at hmutD; change provD = _ at hprovD; change maskD = _ at hmaskD
  subst hszS hmutS hprovS hmaskS hszD hmutD hprovD hmaskD
  have h1 : (1 : UInt64).toNat = 1 := rfl
  have hprov_prep := prov_prepareCopy_new hn rawS
  have hmask_prep := initMask_prepareCopy_true hn
  unfold CopyRepeatedlyPost Miri.Memory.Allocation.copyRepeatedly
  rw [hsliceS]; dsimp only [bind, Pure.pure, pure, copyAlloc_raw]
  rw [hmul]; dsimp only [bind, Pure.pure, pure]
  rw [hsliceD, hprov_prep, hmask_prep]
  simp only [Miri.Memory.InitCopy.noBytesInit, Bool.not_true, Bool.false_and, Bool.and_false,
    Bool.false_eq_true, ↓reduceIte, prov_applyCopy_empty_fn,
    show ((1 : UInt64) == 0) = false from rfl,
    h1, Array.empty_append,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one,
    List.range'_succ, List.range'_zero, List.forIn_cons, List.forIn_nil]
  rw [hn_eq] at hlenS hlenD
  have hex0 : rawD.extract 0 0 = #[] := array_extract_zero_zero rawD
  have hexN : rawD.extract n rawD.size = #[] := array_extract_self_size rawD n hlenD
  rcases hn with rfl | rfl | rfl | rfl | rfl <;> cases bD <;> {
    dsimp only [Id.run, bind, Bind.bind, pure, Pure.pure]
    split
    · rename_i afterClear hprep
      with_unfolding_all conv at hprep => lhs; whnf
      with_unfolding_all erw [hsliceD] at hprep
      with_unfolding_all cases hprep
      dsimp only []
      split
      · rename_i afterBytes hover
        with_unfolding_all conv at hover => lhs; whnf
        with_unfolding_all erw [hex0, hexN, Array.empty_append, hlenS] at hover
        with_unfolding_all cases hover
        with_unfolding_all refine ⟨_, rfl, rfl, rfl, rfl, hlenS, rfl, rfl, rfl⟩
      · rename_i reason hover
        with_unfolding_all conv at hover => lhs; whnf
        with_unfolding_all erw [hex0, hexN, Array.empty_append, hlenS] at hover
        with_unfolding_all cases hover
    · rename_i reason updated hprep
      with_unfolding_all conv at hprep => lhs; whnf
      with_unfolding_all erw [hsliceD] at hprep
      with_unfolding_all cases hprep }

/-- Copying an initialized `StackScalarAllocShape` scalar allocation `S` into a
distinct (`sameAllocation = false`) `StackScalarAllocShape` scalar allocation
`D` of the same width `n` (`ValidScalarBytes n`) via `Allocation.copyRepeatedly`
(`repeatCount = 1`, `nonoverlapping = true`) succeeds, preserves `D.align` and
`StackScalarAllocShape`, marks `D` initialized, and reads back the exact scalar
stored in `S`. -/
theorem StackScalarAllocShape.copyRepeatedly_init_distinct {E : Type} {n : Nat}
    (hn : ValidScalarBytes n) {msc : Miri.Memory.ScalarInt}
    {S D : Miri.Memory.Allocation AnnealProv E}
    (hshapeS : StackScalarAllocShape (translateSizeBytes n) S)
    (hshapeD : StackScalarAllocShape (translateSizeBytes n) D)
    (hreadS : S.readScalar annealTargetDataLayout
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes n)) false =
      .ok (.fromScalarInt msc)) :
    ∃ alloc' : Miri.Memory.Allocation AnnealProv E,
      Miri.Memory.Allocation.copyRepeatedly S
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes n))
        Miri.ABI.Size.ZERO 1 (Miri.ABI.Size.ofBytes 8) false true D = .ok () alloc' ∧
      alloc'.align = D.align ∧
      StackScalarAllocShape (translateSizeBytes n) alloc' ∧
      alloc'.initializationMask.isRangeInitialized
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes n)) = .ok (.ok ()) ∧
      alloc'.readScalar annealTargetDataLayout
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes n)) false =
        .ok (.fromScalarInt msc) := by
  have hinitS : S.initializationMask.isRangeInitialized
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes n)) = .ok (.ok ()) :=
    Classical.byContradiction fun hni => by
      obtain ⟨info, herr⟩ := hshapeS.uninit_readScalar_err hni false
      rw [hreadS] at herr
      cases herr
  rcases hshapeS with ⟨hszS, hlenS, hmutS, hprovS, ⟨bS, hmaskS⟩⟩
  rcases hshapeD with ⟨hszD, hlenD, hmutD, hprovD, ⟨bD, hmaskD⟩⟩
  have hbS : bS = true := by
    cases bS with
    | true => rfl
    | false =>
      rw [hmaskS] at hinitS
      rcases hn with rfl | rfl | rfl | rfl | rfl <;> cases hinitS
  subst hbS
  obtain ⟨alloc', hcopy, halign, hraw, hsz, hlen, hmut, hprov, hmask⟩ :=
    copyRepeatedly_core hn bD hszS hlenS hmutS hprovS hmaskS hszD hlenD hmutD hprovD hmaskD
  refine ⟨alloc', hcopy, halign, ⟨hsz, hlen, hmut, hprov, ⟨true, hmask⟩⟩, ?_, ?_⟩
  · rw [hmask]
    rcases hn with rfl | rfl | rfl | rfl | rfl <;> rfl
  · rw [allocation_readScalar_congr hraw (hsz.trans hszS.symm) (hprov.trans hprovS.symm)
      (hmask.trans hmaskS.symm)]
    exact hreadS

/-- Self-copying an initialized `StackScalarAllocShape` scalar allocation `S`
(`sameAllocation = true`, `nonoverlapping = true`, `repeatCount = 1`) fails
with `AllocError.copyRangesOverlap`. -/
theorem StackScalarAllocShape.copyRepeatedly_init_overlap_err {E : Type} {n : Nat}
    (hn : ValidScalarBytes n) {msc : Miri.Memory.ScalarInt}
    {S : Miri.Memory.Allocation AnnealProv E}
    (hshapeS : StackScalarAllocShape (translateSizeBytes n) S)
    (hreadS : S.readScalar annealTargetDataLayout
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes n)) false =
      .ok (.fromScalarInt msc)) :
    ∃ S' : Miri.Memory.Allocation AnnealProv E,
      Miri.Memory.Allocation.copyRepeatedly S
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes n))
        Miri.ABI.Size.ZERO 1 (Miri.ABI.Size.ofBytes 8) true true S =
        .error .copyRangesOverlap S' := by
  have hinitS : S.initializationMask.isRangeInitialized
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes n)) = .ok (.ok ()) :=
    Classical.byContradiction fun hni => by
      obtain ⟨info, herr⟩ := hshapeS.uninit_readScalar_err hni false
      rw [hreadS] at herr
      cases herr
  rcases hshapeS with ⟨hszS, hlenS, hmutS, hprovS, ⟨bS, hmaskS⟩⟩
  have hbS : bS = true := by
    cases bS with
    | true => rfl
    | false =>
      rw [hmaskS] at hinitS
      rcases hn with rfl | rfl | rfl | rfl | rfl <;> cases hinitS
  subst hbS
  cases S with
  | _ rawS szS provS maskS alignS mutS extraS nbS =>
  change szS = _ at hszS; change rawS.size = _ at hlenS
  change mutS = _ at hmutS; change provS = _ at hprovS; change maskS = _ at hmaskS
  subst hszS hmutS hprovS hmaskS
  have hn_eq : (translateSizeBytes n).bytes.toNat = n := by
    rcases hn with rfl | rfl | rfl | rfl | rfl <;> rfl
  rw [hn_eq] at hlenS
  rcases hn with rfl | rfl | rfl | rfl | rfl <;>
    { rw [copyAlloc_array_eta rawS _ hlenS]
      with_unfolding_all exact ⟨_, rfl⟩ }

/-- Copying an uninitialized `StackScalarAllocShape` scalar allocation `S`
(`bS = false`) into `D` (`repeatCount = 1`, `nonoverlapping = true`) takes
`Allocation.copyRepeatedly`'s early `initialized.noBytesInit` exit
(`Allocation.writeUninit`), succeeding for both `sameAllocation = false` and
`sameAllocation = true`. -/
theorem StackScalarAllocShape.copyRepeatedly_uninit {E : Type} {n : Nat}
    (hn : ValidScalarBytes n) {S D : Miri.Memory.Allocation AnnealProv E}
    (hshapeS : StackScalarAllocShape (translateSizeBytes n) S)
    (huninitS : S.initializationMask = Miri.Memory.InitMask.new (translateSizeBytes n) false)
    (hshapeD : StackScalarAllocShape (translateSizeBytes n) D)
    (sameAlloc : Bool) :
    ∃ alloc' : Miri.Memory.Allocation AnnealProv E,
      Miri.Memory.Allocation.copyRepeatedly S
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes n))
        Miri.ABI.Size.ZERO 1 (Miri.ABI.Size.ofBytes 8) sameAlloc true D = .ok () alloc' := by
  rcases hshapeS with ⟨hszS, hlenS, hmutS, hprovS, _⟩
  rcases hshapeD with ⟨hszD, hlenD, hmutD, hprovD, ⟨bD, hmaskD⟩⟩
  cases S with | _ rawS szS provS maskS alignS mutS extraS nbS =>
  cases D with | _ rawD szD provD maskD alignD mutD extraD nbD =>
  change szS = _ at hszS; change rawS.size = _ at hlenS
  change mutS = _ at hmutS; change provS = _ at hprovS; change maskS = _ at huninitS
  change szD = _ at hszD; change rawD.size = _ at hlenD
  change mutD = _ at hmutD; change provD = _ at hprovD; change maskD = _ at hmaskD
  subst hszS hmutS hprovS huninitS hszD hmutD hprovD hmaskD
  have hn_eq : (translateSizeBytes n).bytes.toNat = n := by
    rcases hn with rfl | rfl | rfl | rfl | rfl <;> rfl
  rw [hn_eq] at hlenS hlenD
  rcases hn with rfl | rfl | rfl | rfl | rfl <;> cases bD <;> cases sameAlloc <;>
    { rw [copyAlloc_array_eta rawS _ hlenS, copyAlloc_array_eta rawD _ hlenD]
      with_unfolding_all exact ⟨_, rfl⟩ }

/-! ## 5. `annealMemCopy`, `annealCopyEval`, and `copyNextAllocMap` -/

private theorem annealMemoryCopyHooks_sync_self (mach : AnnealMachine) :
    annealMemoryCopyHooks.synchronizeMemory mach.memory mach = mach := rfl

private theorem annealCopyPointerAccess_self (mach : AnnealMachine)
    (ptr : Miri.Memory.Pointer (Option AnnealProv)) (size : Miri.ABI.Size) :
    annealMemoryCopyHooks.pointerAccess mach.memory mach ptr size =
      { memory := mach.memory
        state := mach
        outcome :=
          match Miri.Memory.sizeAsI64 size with
          | .error err => .error (toString err)
          | .ok signedSize =>
            match Miri.Memory.checkAndDerefPtr annealPointerArithmetic ptr signedSize .memoryAccess
                (annealResolvePtr mach) (annealLookupAlloc mach) with
            | .ok none => .ok none
            | .ok (some access) =>
              .ok (some (access.pointer.allocId, access.pointer.offset, access.pointer.extra))
            | .error err => .error (toString err) } := rfl

private theorem annealTryGetAllocId_self (mach : AnnealMachine)
    (ptr : Miri.Memory.Pointer (Option AnnealProv)) (bytes : UInt64) :
    annealMemoryCopyHooks.tryGetAllocId mach.memory mach ptr bytes =
      match annealResolvePtr mach ptr (Int.ofNat bytes.toNat) with
      | .ok resolved => some resolved.allocId
      | .error _ => none := rfl

private theorem size_mul_one (size : Miri.ABI.Size) :
    Miri.ABI.Size.mul size 1 = .ok size := by
  rcases size with ⟨b⟩
  unfold Miri.ABI.Size.mul Miri.ABI.Size.ofBytes
  have h1 : b * 1 = b := UInt64.mul_one b
  have h2 : b / 1 = b := by
    apply UInt64.toNat_inj.mp
    simp
  simp [h1, h2]

private theorem copySizeAsI64_of_le_isizeMax {total : Nat} (hle : total ≤ isizeMaxBytes) :
    Miri.Memory.sizeAsI64 (Miri.ABI.Size.ofBytes (UInt64.ofNat total)) =
      .ok (Int.ofNat total) := by
  have hlt64 : total < 2 ^ 64 := by unfold isizeMaxBytes at hle; omega
  have ht : (Miri.ABI.Size.ofBytes (UInt64.ofNat total)).bytes.toNat = total :=
    UInt64.toNat_ofNat_of_lt hlt64
  have hlt63 : total < 9223372036854775808 := by unfold isizeMaxBytes at hle; omega
  unfold Miri.Memory.sizeAsI64
  rw [ht]
  simp [hlt63]

private theorem copyInt_lt_two_pow_63 {total : Nat} (hle : total ≤ isizeMaxBytes) :
    (total : Int) < 2 ^ 63 := by
  have hlt : total < 2 ^ 63 := Nat.lt_of_le_of_lt hle (by decide)
  exact Int.ofNat_lt.mpr hlt

private theorem array_any_eq_true_of_find?_eq_some {α : Type} {a : Array α} {p : α → Bool}
    {v : α} (h : a.find? p = some v) : a.any p = true := by
  rw [← Array.any_toList, List.any_eq_true]
  rw [← Array.find?_toList] at h
  exact ⟨v, List.mem_of_find?_eq_some h, List.find?_some h⟩

/-- Zero-byte `annealMemCopy` is a no-op for all `source` and `dest` pointers
(once `annealCheckPtrAlign` has succeeded). -/
theorem annealMemCopy_zero (source dest : Miri.Memory.Pointer (Option AnnealProv))
    (st : AnnealStepState) :
    annealMemCopy source dest (Miri.ABI.Size.ofBytes (UInt64.ofNat 0)) true st = .ok () st := by
  have hsz : Miri.Memory.sizeAsI64 (Miri.ABI.Size.ofBytes (UInt64.ofNat 0)) = .ok 0 := rfl
  have hsrc : Miri.Memory.checkAndDerefPtr annealPointerArithmetic source 0 .memoryAccess
      (annealResolvePtr st.machine) (annealLookupAlloc st.machine) = .ok none := rfl
  have hdst : Miri.Memory.checkAndDerefPtr annealPointerArithmetic dest 0 .memoryAccess
      (annealResolvePtr st.machine) (annealLookupAlloc st.machine) = .ok none := rfl
  have hmul : Miri.ABI.Size.mul (Miri.ABI.Size.ofBytes (UInt64.ofNat 0)) 1 =
      .ok (Miri.ABI.Size.ofBytes (UInt64.ofNat 0)) := rfl
  unfold annealMemCopy Miri.Interpreter.Intrinsics.memoryCopyAdapter
    Miri.Memory.MemoryLifecycle.memCopyRepeatedly
  simp only [Id.run, bind, Bind.bind, pure, Pure.pure,
    annealMemoryCopyHooks_sync_self, annealCopyPointerAccess_self, annealTryGetAllocId_self,
    hsz, hsrc, hmul, hdst]
  cases annealResolvePtr st.machine source
    (Int.ofNat (Miri.ABI.Size.ofBytes (UInt64.ofNat 0)).bytes.toNat) <;> rfl

/-- Any `checkAndDerefPtr` failure on `source` makes `annealMemCopy` report UB. -/
private theorem annealMemCopy_of_src_check_err
    {source dest : Miri.Memory.Pointer (Option AnnealProv)} {size : Miri.ABI.Size}
    {st : AnnealStepState} {signedSize : Int} {err : Miri.Memory.AccessError}
    (hsz : Miri.Memory.sizeAsI64 size = .ok signedSize)
    (hchk : Miri.Memory.checkAndDerefPtr annealPointerArithmetic source signedSize .memoryAccess
      (annealResolvePtr st.machine) (annealLookupAlloc st.machine) = .error err) :
    ∃ msg, annealMemCopy source dest size true st =
      .error (.undefinedBehavior msg) st := by
  unfold annealMemCopy Miri.Interpreter.Intrinsics.memoryCopyAdapter
    Miri.Memory.MemoryLifecycle.memCopyRepeatedly
  simp only [Id.run, pure, Pure.pure,
    annealMemoryCopyHooks_sync_self, annealCopyPointerAccess_self, hsz, hchk]
  exact ⟨_, rfl⟩

/-- Any `checkAndDerefPtr` failure on `dest` makes `annealMemCopy` report UB
(either `source` fails first or `dest` fails). -/
private theorem annealMemCopy_of_dst_check_err
    {source dest : Miri.Memory.Pointer (Option AnnealProv)} {size : Miri.ABI.Size}
    {st : AnnealStepState} {signedSize : Int} {err : Miri.Memory.AccessError}
    (hsz : Miri.Memory.sizeAsI64 size = .ok signedSize)
    (hchk : Miri.Memory.checkAndDerefPtr annealPointerArithmetic dest signedSize .memoryAccess
      (annealResolvePtr st.machine) (annealLookupAlloc st.machine) = .error err) :
    ∃ msg, annealMemCopy source dest size true st =
      .error (.undefinedBehavior msg) st := by
  unfold annealMemCopy Miri.Interpreter.Intrinsics.memoryCopyAdapter
    Miri.Memory.MemoryLifecycle.memCopyRepeatedly
  simp only [Id.run, bind, Bind.bind, pure, Pure.pure,
    annealMemoryCopyHooks_sync_self, annealCopyPointerAccess_self, hsz]
  cases Miri.Memory.checkAndDerefPtr annealPointerArithmetic source signedSize .memoryAccess
      (annealResolvePtr st.machine) (annealLookupAlloc st.machine) with
  | error _ =>
    exact ⟨_, rfl⟩
  | ok opt =>
    cases opt <;>
    · simp only [size_mul_one size, hsz, hchk]
      exact ⟨_, rfl⟩

/-- Non-zero `annealMemCopy` from a provenance-free `source` reports UB. -/
theorem annealMemCopy_src_withoutProvenance_err (addr : UInt64)
    (dest : Miri.Memory.Pointer (Option AnnealProv))
    {total : Nat} (hpos : 0 < total) (hle : total ≤ isizeMaxBytes) (st : AnnealStepState) :
    ∃ msg, annealMemCopy (Miri.Memory.Pointer.withoutProvenance addr) dest
      (Miri.ABI.Size.ofBytes (UInt64.ofNat total)) true st =
      .error (.undefinedBehavior msg) st :=
  annealMemCopy_of_src_check_err (copySizeAsI64_of_le_isizeMax hle)
    (checkAndDerefPtr_withoutProvenance_err st.machine addr (Int.ofNat total) .memoryAccess
      (Int.ofNat_lt.mpr hpos) (copyInt_lt_two_pow_63 hle))

/-- Non-zero `annealMemCopy` to a provenance-free `dest` reports UB. -/
theorem annealMemCopy_dst_withoutProvenance_err
    (source : Miri.Memory.Pointer (Option AnnealProv)) (addr : UInt64)
    {total : Nat} (hpos : 0 < total) (hle : total ≤ isizeMaxBytes) (st : AnnealStepState) :
    ∃ msg, annealMemCopy source (Miri.Memory.Pointer.withoutProvenance addr)
      (Miri.ABI.Size.ofBytes (UInt64.ofNat total)) true st =
      .error (.undefinedBehavior msg) st :=
  annealMemCopy_of_dst_check_err (copySizeAsI64_of_le_isizeMax hle)
    (checkAndDerefPtr_withoutProvenance_err st.machine addr (Int.ofNat total) .memoryAccess
      (Int.ofNat_lt.mpr hpos) (copyInt_lt_two_pow_63 hle))

/-- Non-zero `annealMemCopy` from a dead stack allocation reports UB. -/
theorem annealMemCopy_src_dead_err
    {st : AnnealStepState} (allocId : Miri.Memory.AllocId) (borTag : Miri.Memory.BorTag)
    (offsetBytes : Nat) (dest : Miri.Memory.Pointer (Option AnnealProv)) {total : Nat}
    (hid : allocId.value.toNat < 2 ^ 32) (hoff : offsetBytes < 2 ^ 32)
    (hbase : st.machine.lookupBaseAddr allocId = some (annealStackBaseAddr allocId))
    (hdead : st.machine.memory.live.find? (fun entry => entry.1 == allocId) = none)
    (hpos : 0 < total) (hle : total ≤ isizeMaxBytes) :
    ∃ msg, annealMemCopy
      ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr allocId + UInt64.ofNat offsetBytes),
        some (.concrete allocId borTag)⟩
      dest (Miri.ABI.Size.ofBytes (UInt64.ofNat total)) true st =
      .error (.undefinedBehavior msg) st :=
  annealMemCopy_of_src_check_err (copySizeAsI64_of_le_isizeMax hle)
    (checkAndDerefPtr_deadAlloc_err allocId borTag offsetBytes (Int.ofNat total) .memoryAccess
      hid hoff hbase hdead (Int.ofNat_lt.mpr hpos) (copyInt_lt_two_pow_63 hle))

/-- Non-zero `annealMemCopy` to a dead stack allocation reports UB. -/
theorem annealMemCopy_dst_dead_err
    {st : AnnealStepState} (source : Miri.Memory.Pointer (Option AnnealProv))
    (allocId : Miri.Memory.AllocId) (borTag : Miri.Memory.BorTag)
    (offsetBytes : Nat) {total : Nat}
    (hid : allocId.value.toNat < 2 ^ 32) (hoff : offsetBytes < 2 ^ 32)
    (hbase : st.machine.lookupBaseAddr allocId = some (annealStackBaseAddr allocId))
    (hdead : st.machine.memory.live.find? (fun entry => entry.1 == allocId) = none)
    (hpos : 0 < total) (hle : total ≤ isizeMaxBytes) :
    ∃ msg, annealMemCopy source
      ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr allocId + UInt64.ofNat offsetBytes),
        some (.concrete allocId borTag)⟩
      (Miri.ABI.Size.ofBytes (UInt64.ofNat total)) true st =
      .error (.undefinedBehavior msg) st :=
  annealMemCopy_of_dst_check_err (copySizeAsI64_of_le_isizeMax hle)
    (checkAndDerefPtr_deadAlloc_err allocId borTag offsetBytes (Int.ofNat total) .memoryAccess
      hid hoff hbase hdead (Int.ofNat_lt.mpr hpos) (copyInt_lt_two_pow_63 hle))

/-- Out-of-bounds non-zero `annealMemCopy` on a live `source` stack allocation
reports UB. -/
theorem annealMemCopy_src_oob_err
    {st : AnnealStepState} (allocId : Miri.Memory.AllocId) (borTag : Miri.Memory.BorTag)
    (offsetBytes : Nat)
    (localAlloc : Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
      Miri.Memory.MiriMemoryKind)
    (dest : Miri.Memory.Pointer (Option AnnealProv)) {total : Nat}
    (hid : allocId.value.toNat < 2 ^ 32) (hoff : offsetBytes < 2 ^ 32)
    (hbase : st.machine.lookupBaseAddr allocId = some (annealStackBaseAddr allocId))
    (hlive : st.machine.memory.live.find? (fun entry => entry.1 == allocId) =
      some (allocId, localAlloc))
    (hpos : 0 < total) (hle : total ≤ isizeMaxBytes)
    (hoob : localAlloc.allocation.byteSize.bytes.toNat < offsetBytes + total) :
    ∃ msg, annealMemCopy
      ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr allocId + UInt64.ofNat offsetBytes),
        some (.concrete allocId borTag)⟩
      dest (Miri.ABI.Size.ofBytes (UInt64.ofNat total)) true st =
      .error (.undefinedBehavior msg) st :=
  annealMemCopy_of_src_check_err (copySizeAsI64_of_le_isizeMax hle)
    (checkAndDerefPtr_live_oob_err allocId borTag offsetBytes total localAlloc .memoryAccess
      hid hoff hbase hlive hpos (copyInt_lt_two_pow_63 hle) hoob)

/-- Out-of-bounds non-zero `annealMemCopy` on a live `dest` stack allocation
reports UB. -/
theorem annealMemCopy_dst_oob_err
    {st : AnnealStepState} (source : Miri.Memory.Pointer (Option AnnealProv))
    (allocId : Miri.Memory.AllocId) (borTag : Miri.Memory.BorTag)
    (offsetBytes : Nat)
    (localAlloc : Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
      Miri.Memory.MiriMemoryKind)
    {total : Nat}
    (hid : allocId.value.toNat < 2 ^ 32) (hoff : offsetBytes < 2 ^ 32)
    (hbase : st.machine.lookupBaseAddr allocId = some (annealStackBaseAddr allocId))
    (hlive : st.machine.memory.live.find? (fun entry => entry.1 == allocId) =
      some (allocId, localAlloc))
    (hpos : 0 < total) (hle : total ≤ isizeMaxBytes)
    (hoob : localAlloc.allocation.byteSize.bytes.toNat < offsetBytes + total) :
    ∃ msg, annealMemCopy source
      ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr allocId + UInt64.ofNat offsetBytes),
        some (.concrete allocId borTag)⟩
      (Miri.ABI.Size.ofBytes (UInt64.ofNat total)) true st =
      .error (.undefinedBehavior msg) st :=
  annealMemCopy_of_dst_check_err (copySizeAsI64_of_le_isizeMax hle)
    (checkAndDerefPtr_live_oob_err allocId borTag offsetBytes total localAlloc .memoryAccess
      hid hoff hbase hlive hpos (copyInt_lt_two_pow_63 hle) hoob)

private theorem copyResolvedRanges_live_eq
    {memory : AnnealMemory} {hooksState : AnnealMachine}
    {srcId : Miri.Memory.AllocId} {srcOff : Miri.ABI.Size}
    {srcLA : Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
      Miri.Memory.MiriMemoryKind}
    {dstId : Miri.Memory.AllocId} {dstOff : Miri.ABI.Size}
    {dstLA : Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
      Miri.Memory.MiriMemoryKind}
    {size pointerSize : Miri.ABI.Size}
    (hsrc_live : memory.live.find? (fun entry => entry.1 == srcId) = some (srcId, srcLA))
    (hdst_live : memory.live.find? (fun entry => entry.1 == dstId) = some (dstId, dstLA)) :
    Miri.Memory.MemoryLifecycle.copyResolvedRanges memory hooksState
        srcId srcOff dstId dstOff size 1 pointerSize true =
      match Miri.Memory.Allocation.copyRepeatedly srcLA.allocation
          (Miri.Memory.allocRange srcOff size) dstOff 1 pointerSize
          (srcId == dstId) true dstLA.allocation with
      | .ok () alloc' =>
        ⟨{ memory with
            live := (memory.live.filter (fun x => x.1 != dstId)).push (dstId, ⟨dstLA.kind, alloc'⟩) },
          hooksState, .ok ()⟩
      | .error err alloc' =>
        ⟨{ memory with
            live := (memory.live.filter (fun x => x.1 != dstId)).push (dstId, ⟨dstLA.kind, alloc'⟩) },
          hooksState, .error (.allocation err)⟩ := by
  unfold Miri.Memory.MemoryLifecycle.copyResolvedRanges
  dsimp only [Id.run]
  rw [hsrc_live, hdst_live]
  dsimp only
  cases Miri.Memory.Allocation.copyRepeatedly srcLA.allocation
    (Miri.Memory.allocRange srcOff size) dstOff 1 pointerSize
    (srcId == dstId) true dstLA.allocation <;> with_unfolding_all rfl

private theorem memCopyRepeatedly_ok_eq
    {mach : AnnealMachine}
    {sourcePointer destPointer : Miri.Memory.Pointer (Option AnnealProv)}
    {size pointerSize : Miri.ABI.Size}
    {hooks : Miri.Memory.MemoryCopyHooks AnnealProv (Option Miri.TreeBorrows.BorrowTree)
      Miri.Memory.MiriMemoryKind AnnealMachine Miri.Memory.BorTag}
    {srcId : Miri.Memory.AllocId} {srcOff : Miri.ABI.Size} {srcTag : Miri.Memory.BorTag}
    {srcLA : Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
      Miri.Memory.MiriMemoryKind}
    {dstId : Miri.Memory.AllocId} {dstOff : Miri.ABI.Size} {dstTag : Miri.Memory.BorTag}
    {dstLA : Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
      Miri.Memory.MiriMemoryKind}
    (hsync : ∀ mem h, hooks.synchronizeMemory mem h = { h with memory := mem })
    (hsync_self : hooks.synchronizeMemory mach.memory mach = mach)
    (hpaS : hooks.pointerAccess mach.memory mach sourcePointer size =
      { memory := mach.memory, state := mach, outcome := .ok (some (srcId, srcOff, srcTag)) })
    (hmul : Miri.ABI.Size.mul size 1 = .ok size)
    (hpaD : hooks.pointerAccess mach.memory mach destPointer size =
      { memory := mach.memory, state := mach, outcome := .ok (some (dstId, dstOff, dstTag)) })
    (hba : ∀ id, hooks.beforeAllocationAccess mach.memory mach id =
      { memory := mach.memory, state := mach, outcome := .ok () })
    (hsrc_live : mach.memory.live.find? (fun entry => entry.1 == srcId) = some (srcId, srcLA))
    (hbr : ∀ a p id e r, hooks.beforeMemoryRead mach mach.memory a p id e r =
      { memory := mach.memory, hooks := mach, outcome := .ok () })
    (hanyD : (mach.memory.live.any fun entry => entry.1 == dstId) = true)
    (hdst_live : mach.memory.live.find? (fun entry => entry.1 == dstId) = some (dstId, dstLA))
    (hbw : ∀ a p id e r, hooks.beforeMemoryWrite mach mach.memory a p id e r =
      { memory := mach.memory, hooks := mach, outcome := .ok () }) :
    Miri.Memory.MemoryLifecycle.memCopyRepeatedly mach.memory mach sourcePointer destPointer
        size 1 true pointerSize hooks =
      let copied := Miri.Memory.MemoryLifecycle.copyResolvedRanges mach.memory mach
        srcId srcOff dstId dstOff size 1 pointerSize true
      { copied with hooks := { copied.hooks with memory := copied.memory } } := by
  unfold Miri.Memory.MemoryLifecycle.memCopyRepeatedly
  simp only [Id.run, bind, Bind.bind, pure, Pure.pure,
    hsync_self, hpaS, hmul, hpaD]
  cases hooks.tryGetAllocId mach.memory mach sourcePointer size.bytes <;>
  · simp only [hba, hsync_self, hsrc_live, hbr, hanyD, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte, hdst_live, hbw, hsync]

private theorem annealCopyPointerAccess_of_ok
    {mach : AnnealMachine} {ptr : Miri.Memory.Pointer (Option AnnealProv)}
    {size : Miri.ABI.Size} {signedSize : Int}
    {access : Miri.Memory.CheckedPointerAccess Miri.Memory.BorTag}
    (hsz : Miri.Memory.sizeAsI64 size = .ok signedSize)
    (hchk : Miri.Memory.checkAndDerefPtr annealPointerArithmetic ptr signedSize .memoryAccess
      (annealResolvePtr mach) (annealLookupAlloc mach) = .ok (some access)) :
    annealMemoryCopyHooks.pointerAccess mach.memory mach ptr size =
      { memory := mach.memory
        state := mach
        outcome :=
          .ok (some (access.pointer.allocId, access.pointer.offset, access.pointer.extra)) } := by
  rw [annealCopyPointerAccess_self]
  simp only [hsz, hchk]

private theorem annealCopyPointerAccess_live_inbounds
    {st : AnnealStepState}
    (id : Miri.Memory.AllocId) (tag : Miri.Memory.BorTag) (off : Nat)
    (la : Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
      Miri.Memory.MiriMemoryKind)
    {total : Nat}
    (hid : id.value.toNat < 2 ^ 32) (hoff : off < 2 ^ 32)
    (hbase : st.machine.lookupBaseAddr id = some (annealStackBaseAddr id))
    (hlive : st.machine.memory.live.find? (fun entry => entry.1 == id) = some (id, la))
    (hinb : off + total ≤ la.allocation.byteSize.bytes.toNat)
    (hpos : 0 < total) (hle : total ≤ isizeMaxBytes) :
    annealMemoryCopyHooks.pointerAccess st.machine.memory st.machine
      ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr id + UInt64.ofNat off),
        some (.concrete id tag)⟩
      (Miri.ABI.Size.ofBytes (UInt64.ofNat total)) =
      { memory := st.machine.memory
        state := st.machine
        outcome := .ok (some (id, Miri.ABI.Size.ofBytes (UInt64.ofNat off), tag)) } :=
  annealCopyPointerAccess_of_ok (copySizeAsI64_of_le_isizeMax hle)
    (checkAndDerefPtr_live_inbounds_ok id tag off total la .memoryAccess
      hid hoff hbase hlive hpos (copyInt_lt_two_pow_63 hle) hinb)

/-- In-bounds non-zero `annealMemCopy` between live stack allocations reduces to
`Allocation.copyRepeatedly`. -/
private theorem annealMemCopy_live_inbounds_eq
    {st : AnnealStepState}
    (srcId : Miri.Memory.AllocId) (srcTag : Miri.Memory.BorTag) (srcOff : Nat)
    (srcLA : Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
      Miri.Memory.MiriMemoryKind)
    (dstId : Miri.Memory.AllocId) (dstTag : Miri.Memory.BorTag) (dstOff : Nat)
    (dstLA : Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
      Miri.Memory.MiriMemoryKind)
    {total : Nat}
    (hsrc_id : srcId.value.toNat < 2 ^ 32) (hsrc_off : srcOff < 2 ^ 32)
    (hsrc_base : st.machine.lookupBaseAddr srcId = some (annealStackBaseAddr srcId))
    (hsrc_live : st.machine.memory.live.find? (fun entry => entry.1 == srcId) = some (srcId, srcLA))
    (hsrc_inb : srcOff + total ≤ srcLA.allocation.byteSize.bytes.toNat)
    (hdst_id : dstId.value.toNat < 2 ^ 32) (hdst_off : dstOff < 2 ^ 32)
    (hdst_base : st.machine.lookupBaseAddr dstId = some (annealStackBaseAddr dstId))
    (hdst_live : st.machine.memory.live.find? (fun entry => entry.1 == dstId) = some (dstId, dstLA))
    (hdst_inb : dstOff + total ≤ dstLA.allocation.byteSize.bytes.toNat)
    (hpos : 0 < total) (hle : total ≤ isizeMaxBytes) :
    annealMemCopy
      ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr srcId + UInt64.ofNat srcOff),
        some (.concrete srcId srcTag)⟩
      ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr dstId + UInt64.ofNat dstOff),
        some (.concrete dstId dstTag)⟩
      (Miri.ABI.Size.ofBytes (UInt64.ofNat total)) true st =
      match Miri.Memory.Allocation.copyRepeatedly srcLA.allocation
          (Miri.Memory.allocRange (Miri.ABI.Size.ofBytes (UInt64.ofNat srcOff))
            (Miri.ABI.Size.ofBytes (UInt64.ofNat total)))
          (Miri.ABI.Size.ofBytes (UInt64.ofNat dstOff)) 1 (Miri.ABI.Size.ofBytes 8)
          (srcId == dstId) true dstLA.allocation with
      | .ok () alloc' =>
        .ok () { st with machine := { st.machine with
          memory := { st.machine.memory with
            live := (st.machine.memory.live.filter (fun x => x.1 != dstId)).push
              (dstId, ⟨dstLA.kind, alloc'⟩) } } }
      | .error err alloc' =>
        .error (annealClassifyMemCopyError (.allocation err)) { st with machine := { st.machine with
          memory := { st.machine.memory with
            live := (st.machine.memory.live.filter (fun x => x.1 != dstId)).push
              (dstId, ⟨dstLA.kind, alloc'⟩) } } } := by
  have hpaS := annealCopyPointerAccess_live_inbounds srcId srcTag srcOff srcLA
    hsrc_id hsrc_off hsrc_base hsrc_live hsrc_inb hpos hle
  have hpaD := annealCopyPointerAccess_live_inbounds dstId dstTag dstOff dstLA
    hdst_id hdst_off hdst_base hdst_live hdst_inb hpos hle
  have hanyD := array_any_eq_true_of_find?_eq_some hdst_live
  have hpw : Miri.ABI.Size.fromBits annealTargetDataLayout.pointerWidth.bits =
      Miri.ABI.Size.ofBytes 8 := rfl
  have hmcr := memCopyRepeatedly_ok_eq (mach := st.machine)
    (fun _ _ => rfl) rfl hpaS (size_mul_one _) hpaD (fun _ => rfl)
    hsrc_live (fun _ _ _ _ _ => rfl) hanyD hdst_live (fun _ _ _ _ _ => rfl)
    (pointerSize := Miri.ABI.Size.ofBytes 8)
  unfold annealMemCopy Miri.Interpreter.Intrinsics.memoryCopyAdapter
  rw [hpw, hmcr, copyResolvedRanges_live_eq hsrc_live hdst_live]
  cases Miri.Memory.Allocation.copyRepeatedly srcLA.allocation
      (Miri.Memory.allocRange (Miri.ABI.Size.ofBytes (UInt64.ofNat srcOff))
        (Miri.ABI.Size.ofBytes (UInt64.ofNat total)))
      (Miri.ABI.Size.ofBytes (UInt64.ofNat dstOff)) 1 (Miri.ABI.Size.ofBytes 8)
      (srcId == dstId) true dstLA.allocation <;> rfl

/-- Distinct (`srcId ≠ dstId`) whole-allocation `annealMemCopy` on live
`StackScalarAllocShape` allocations with initialized `srcLA` updates `dstId` in
`live`. -/
theorem annealMemCopy_live_distinct_ok
    {st : AnnealStepState} {n : Nat} (hn : ValidScalarBytes n)
    (srcId : Miri.Memory.AllocId) (srcTag : Miri.Memory.BorTag)
    (srcLA : Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
      Miri.Memory.MiriMemoryKind)
    (dstId : Miri.Memory.AllocId) (dstTag : Miri.Memory.BorTag)
    (dstLA : Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
      Miri.Memory.MiriMemoryKind)
    (alloc' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree))
    (hne : srcId ≠ dstId)
    (hsrc_id : srcId.value.toNat < 2 ^ 32)
    (hsrc_base : st.machine.lookupBaseAddr srcId = some (annealStackBaseAddr srcId))
    (hsrc_live : st.machine.memory.live.find? (fun entry => entry.1 == srcId) = some (srcId, srcLA))
    (hsrc_sz : srcLA.allocation.byteSize.bytes.toNat = n)
    (hdst_id : dstId.value.toNat < 2 ^ 32)
    (hdst_base : st.machine.lookupBaseAddr dstId = some (annealStackBaseAddr dstId))
    (hdst_live : st.machine.memory.live.find? (fun entry => entry.1 == dstId) = some (dstId, dstLA))
    (hdst_sz : dstLA.allocation.byteSize.bytes.toNat = n)
    (hcopy : Miri.Memory.Allocation.copyRepeatedly srcLA.allocation
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes n))
      Miri.ABI.Size.ZERO 1 (Miri.ABI.Size.ofBytes 8) false true dstLA.allocation = .ok () alloc') :
    annealMemCopy
      ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr srcId + UInt64.ofNat 0),
        some (.concrete srcId srcTag)⟩
      ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr dstId + UInt64.ofNat 0),
        some (.concrete dstId dstTag)⟩
      (Miri.ABI.Size.ofBytes (UInt64.ofNat n)) true st =
      .ok () { st with machine := { st.machine with
        memory := { st.machine.memory with
          live := (st.machine.memory.live.filter (fun x => x.1 != dstId)).push
            (dstId, ⟨dstLA.kind, alloc'⟩) } } } := by
  have hpos : 0 < n := by rcases hn with rfl | rfl | rfl | rfl | rfl <;> omega
  have hle : n ≤ isizeMaxBytes := by
    unfold isizeMaxBytes; rcases hn with rfl | rfl | rfl | rfl | rfl <;> omega
  have hts : Miri.ABI.Size.ofBytes (UInt64.ofNat n) = translateSizeBytes n := by
    rcases hn with rfl | rfl | rfl | rfl | rfl <;> rfl
  have hz : Miri.ABI.Size.ofBytes (UInt64.ofNat 0) = Miri.ABI.Size.ZERO := rfl
  have hbeq : (srcId == dstId) = false := beq_false_of_ne hne
  rw [annealMemCopy_live_inbounds_eq srcId srcTag 0 srcLA dstId dstTag 0 dstLA
    hsrc_id (by decide) hsrc_base hsrc_live (by omega)
    hdst_id (by decide) hdst_base hdst_live (by omega) hpos hle]
  dsimp only
  rw [hts, hz, hbeq, hcopy]

/-- Self-overlapping (`srcId = dstId`) whole-allocation `annealMemCopy` on an
initialized `StackScalarAllocShape` allocation reports UB
(`"copy_nonoverlapping called on overlapping ranges"`). -/
theorem annealMemCopy_live_overlap_err
    {st : AnnealStepState} {n : Nat} (hn : ValidScalarBytes n)
    (allocId : Miri.Memory.AllocId) (srcTag dstTag : Miri.Memory.BorTag)
    (localAlloc : Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
      Miri.Memory.MiriMemoryKind)
    (alloc' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree))
    (hid : allocId.value.toNat < 2 ^ 32)
    (hbase : st.machine.lookupBaseAddr allocId = some (annealStackBaseAddr allocId))
    (hlive : st.machine.memory.live.find? (fun entry => entry.1 == allocId) =
      some (allocId, localAlloc))
    (hsz : localAlloc.allocation.byteSize.bytes.toNat = n)
    (hcopy : Miri.Memory.Allocation.copyRepeatedly localAlloc.allocation
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes n))
      Miri.ABI.Size.ZERO 1 (Miri.ABI.Size.ofBytes 8) true true localAlloc.allocation =
      .error .copyRangesOverlap alloc') :
    ∃ st', annealMemCopy
      ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr allocId + UInt64.ofNat 0),
        some (.concrete allocId srcTag)⟩
      ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr allocId + UInt64.ofNat 0),
        some (.concrete allocId dstTag)⟩
      (Miri.ABI.Size.ofBytes (UInt64.ofNat n)) true st =
      .error (.undefinedBehavior "copy_nonoverlapping called on overlapping ranges") st' := by
  have hpos : 0 < n := by rcases hn with rfl | rfl | rfl | rfl | rfl <;> omega
  have hle : n ≤ isizeMaxBytes := by
    unfold isizeMaxBytes; rcases hn with rfl | rfl | rfl | rfl | rfl <;> omega
  have hts : Miri.ABI.Size.ofBytes (UInt64.ofNat n) = translateSizeBytes n := by
    rcases hn with rfl | rfl | rfl | rfl | rfl <;> rfl
  have hz : Miri.ABI.Size.ofBytes (UInt64.ofNat 0) = Miri.ABI.Size.ZERO := rfl
  have heq := annealMemCopy_live_inbounds_eq (st := st) allocId srcTag 0 localAlloc allocId dstTag 0
    localAlloc hid (by decide) hbase hlive (by omega) hid (by decide) hbase hlive (by omega) hpos hle
  rw [hts, hz, beq_self_eq_true, hcopy] at heq
  exact ⟨_, heq⟩

/-- Whole-allocation `annealMemCopy` from an uninitialized `StackScalarAllocShape`
allocation succeeds (`Allocation.copyRepeatedly_uninit`). -/
theorem annealMemCopy_live_uninit_ok
    {st : AnnealStepState} {n : Nat} (hn : ValidScalarBytes n)
    (srcId : Miri.Memory.AllocId) (srcTag : Miri.Memory.BorTag)
    (srcLA : Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
      Miri.Memory.MiriMemoryKind)
    (dstId : Miri.Memory.AllocId) (dstTag : Miri.Memory.BorTag)
    (dstLA : Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
      Miri.Memory.MiriMemoryKind)
    (hsrc_id : srcId.value.toNat < 2 ^ 32)
    (hsrc_base : st.machine.lookupBaseAddr srcId = some (annealStackBaseAddr srcId))
    (hsrc_live : st.machine.memory.live.find? (fun entry => entry.1 == srcId) = some (srcId, srcLA))
    (hsrc_shape : StackScalarAllocShape (translateSizeBytes n) srcLA.allocation)
    (hsrc_uninit : srcLA.allocation.initializationMask =
      Miri.Memory.InitMask.new (translateSizeBytes n) false)
    (hdst_id : dstId.value.toNat < 2 ^ 32)
    (hdst_base : st.machine.lookupBaseAddr dstId = some (annealStackBaseAddr dstId))
    (hdst_live : st.machine.memory.live.find? (fun entry => entry.1 == dstId) = some (dstId, dstLA))
    (hdst_shape : StackScalarAllocShape (translateSizeBytes n) dstLA.allocation) :
    ∃ mach', annealMemCopy
      ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr srcId + UInt64.ofNat 0),
        some (.concrete srcId srcTag)⟩
      ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr dstId + UInt64.ofNat 0),
        some (.concrete dstId dstTag)⟩
      (Miri.ABI.Size.ofBytes (UInt64.ofNat n)) true st = .ok () { st with machine := mach' } := by
  have hpos : 0 < n := by rcases hn with rfl | rfl | rfl | rfl | rfl <;> omega
  have hle : n ≤ isizeMaxBytes := by
    unfold isizeMaxBytes; rcases hn with rfl | rfl | rfl | rfl | rfl <;> omega
  have hts : Miri.ABI.Size.ofBytes (UInt64.ofNat n) = translateSizeBytes n := by
    rcases hn with rfl | rfl | rfl | rfl | rfl <;> rfl
  have hn_eq : (translateSizeBytes n).bytes.toNat = n := by
    rcases hn with rfl | rfl | rfl | rfl | rfl <;> rfl
  have hsrc_sz : srcLA.allocation.byteSize.bytes.toNat = n := by
    rw [hsrc_shape.byteSize_eq, hn_eq]
  have hdst_sz : dstLA.allocation.byteSize.bytes.toNat = n := by
    rw [hdst_shape.byteSize_eq, hn_eq]
  have hz : Miri.ABI.Size.ofBytes (UInt64.ofNat 0) = Miri.ABI.Size.ZERO := rfl
  obtain ⟨alloc', hcopy⟩ := hsrc_shape.copyRepeatedly_uninit hn hsrc_uninit hdst_shape
    (srcId == dstId)
  have heq := annealMemCopy_live_inbounds_eq (st := st) srcId srcTag 0 srcLA dstId dstTag 0 dstLA
    hsrc_id (by decide) hsrc_base hsrc_live (by omega)
    hdst_id (by decide) hdst_base hdst_live (by omega) hpos hle
  rw [hts, hz, hcopy] at heq
  exact ⟨_, heq⟩

private theorem copyIntrinsicPointer_uninit (lay : Miri.Interpreter.LocalLayout)
    (m : AnnealStepState) :
    intrinsicPointer ⟨.immediate .uninit, lay⟩ m =
      .error (.undefinedBehavior "read of uninitialized local") m := rfl

private theorem copyIntrinsicUsize_uninit (lay : Miri.Interpreter.LocalLayout)
    (m : AnnealStepState) :
    intrinsicUsize ⟨.immediate .uninit, lay⟩ m =
      .error (.undefinedBehavior "read of uninitialized local") m := rfl

private theorem copyIntrinsicPointer_fromPointer (mptr : Miri.Memory.Pointer AnnealProv)
    (lay : Miri.Interpreter.LocalLayout) (m : AnnealStepState) :
    intrinsicPointer
        ⟨.immediate (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr)), lay⟩ m =
      .ok mptr.withOptionalProvenance m := rfl

private theorem copyIntrinsicPointer_fromScalarInt {sc : MirAst.ScalarInt}
    {msc : Miri.Memory.ScalarInt} (hrel : ScalarRel sc msc) (hsz8 : sc.sizeBytes = 8)
    (lay : Miri.Interpreter.LocalLayout) (m : AnnealStepState) :
    intrinsicPointer ⟨.immediate (.scalar (.fromScalarInt msc)), lay⟩ m =
      .ok (Miri.Memory.Pointer.withoutProvenance (UInt64.ofNat sc.bits)) m := by
  have h := scalar_fromScalarInt_toPointer_eq hrel hsz8
  have hs : intrinsicScalar ⟨.immediate (.scalar (.fromScalarInt msc)), lay⟩ m =
      .ok (.fromScalarInt msc) m := rfl
  unfold intrinsicPointer
  rw [EStateM.bind_eq_ok hs, h]
  rfl

private theorem copyIntrinsicUsize_fromScalarInt {sc : MirAst.ScalarInt}
    {msc : Miri.Memory.ScalarInt} (hrel : ScalarRel sc msc) (hsz8 : sc.sizeBytes = 8)
    (lay : Miri.Interpreter.LocalLayout) (m : AnnealStepState) :
    sc.bits < 2 ^ 64 ∧
    intrinsicUsize ⟨.immediate (.scalar (.fromScalarInt msc)), lay⟩ m =
      .ok (UInt64.ofNat sc.bits) m := by
  have hlt : sc.bits < 2 ^ 64 := by
    have hc := hrel.canonical; rw [hsz8] at hc; simpa [scalarModulus] using hc
  refine ⟨hlt, ?_⟩
  have hsi : (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) msc).toScalarInt = .ok msc := rfl
  have hbz : ((Miri.ABI.Size.ofBytes 8).bytes == 0) = false := rfl
  have hsz8' : Miri.ABI.Size.ofBytes 8 = translateSizeBytes sc.sizeBytes := by rw [hsz8]; rfl
  have htb : msc.toBits (Miri.ABI.Size.ofBytes 8) = .ok (BitVec.ofNat 128 sc.bits) := by
    rw [hsz8']; exact hrel.toBits_eq
  have hbv : (BitVec.ofNat 128 sc.bits).toNat = sc.bits := by rw [BitVec.toNat_ofNat]; omega
  have hfit : ¬ sc.bits > 18446744073709551615 := by omega
  have htu : (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) msc).toTargetUsize
      (Miri.ABI.Size.ofBytes 8) = .ok (UInt64.ofNat sc.bits) := by
    unfold Miri.Memory.Scalar.toTargetUsize Miri.Memory.Scalar.toUInt Miri.Memory.Scalar.toBits
    simp only [hbz, Bool.false_eq_true, ↓reduceIte, hsi, htb, hbv, hfit,
      Except.mapError, bind, Except.bind, pure, Except.pure]
  have hs : intrinsicScalar ⟨.immediate (.scalar (.fromScalarInt msc)), lay⟩ m =
      .ok (.fromScalarInt msc) m := rfl
  have hpw : Miri.ABI.Size.fromBits annealTargetDataLayout.pointerWidth.bits =
      Miri.ABI.Size.ofBytes 8 := rfl
  unfold intrinsicUsize
  rw [EStateM.bind_eq_ok hs, hpw, htu]
  rfl

private theorem copyAnnealCopyEval_uninit_count {ly : LayoutTable}
    (v₁ v₂ : Miri.Interpreter.OpTy AnnealProv) (countLay : Miri.Interpreter.LocalLayout)
    (m : AnnealStepState) :
    annealCopyEval ly v₁ v₂ ⟨.immediate .uninit, countLay⟩ m =
      .error (.undefinedBehavior "read of uninitialized local") m := by
  rw [annealCopyEval_eq]
  rw [EStateM.bind_eq_error (copyIntrinsicUsize_uninit countLay m)]

private theorem copyAnnealCopyEval_uninit_src {ly : LayoutTable}
    {srcLay countLay : Miri.Interpreter.LocalLayout}
    {ptId : Miri.MIR.TyId} {elemBytes : Nat}
    {countSc : MirAst.ScalarInt} {mcount : Miri.Memory.ScalarInt}
    (v₂ : Miri.Interpreter.OpTy AnnealProv) (m : AnnealStepState)
    (hpt : annealPointeeTypeOf srcLay.ty m = .ok ptId m)
    (hlay_sz : (layoutOfEncodedTyId ptId ly).layout.size =
      Miri.ABI.Size.ofBytes (UInt64.ofNat elemBytes))
    (helem_lt : elemBytes < 2 ^ 64)
    (hrelC : ScalarRel countSc mcount) (hszC : countSc.sizeBytes = 8) :
    ∃ msg, annealCopyEval ly ⟨.immediate .uninit, srcLay⟩ v₂
      ⟨.immediate (.scalar (.fromScalarInt mcount)), countLay⟩ m =
      .error (.undefinedBehavior msg) m := by
  obtain ⟨hcnt_lt, hcnt⟩ := copyIntrinsicUsize_fromScalarInt hrelC hszC countLay m
  have hcomp := computeSizeInBytes_writeBytes helem_lt hcnt_lt
  rw [annealCopyEval_eq, EStateM.bind_eq_ok hcnt, EStateM.bind_eq_ok hpt]
  rw [hlay_sz, hcomp]
  by_cases hle : countSc.bits * elemBytes ≤ isizeMaxBytes
  · simp only [hle, ↓reduceIte]
    exact ⟨"read of uninitialized local",
      EStateM.bind_eq_error (copyIntrinsicPointer_uninit srcLay m)⟩
  · simp only [hle, ↓reduceIte]
    exact ⟨"overflow computing total size of copy", rfl⟩

private theorem copyAnnealCopyEval_uninit_dst {ly : LayoutTable}
    {v₁ : Miri.Interpreter.OpTy AnnealProv}
    {dstLay countLay : Miri.Interpreter.LocalLayout}
    {ptId : Miri.MIR.TyId} {elemBytes : Nat}
    {srcPtr : Miri.Memory.Pointer (Option AnnealProv)}
    {countSc : MirAst.ScalarInt} {mcount : Miri.Memory.ScalarInt}
    (m : AnnealStepState)
    (hpt : annealPointeeTypeOf v₁.layout.ty m = .ok ptId m)
    (hlay_sz : (layoutOfEncodedTyId ptId ly).layout.size =
      Miri.ABI.Size.ofBytes (UInt64.ofNat elemBytes))
    (helem_lt : elemBytes < 2 ^ 64)
    (hsrc : intrinsicPointer v₁ m = .ok srcPtr m)
    (hrelC : ScalarRel countSc mcount) (hszC : countSc.sizeBytes = 8) :
    ∃ msg, annealCopyEval ly v₁ ⟨.immediate .uninit, dstLay⟩
      ⟨.immediate (.scalar (.fromScalarInt mcount)), countLay⟩ m =
      .error (.undefinedBehavior msg) m := by
  obtain ⟨hcnt_lt, hcnt⟩ := copyIntrinsicUsize_fromScalarInt hrelC hszC countLay m
  have hcomp := computeSizeInBytes_writeBytes helem_lt hcnt_lt
  rw [annealCopyEval_eq, EStateM.bind_eq_ok hcnt, EStateM.bind_eq_ok hpt]
  rw [hlay_sz, hcomp]
  by_cases hle : countSc.bits * elemBytes ≤ isizeMaxBytes
  · simp only [hle, ↓reduceIte]
    rw [EStateM.bind_eq_ok hsrc, EStateM.bind_eq_error (copyIntrinsicPointer_uninit dstLay m)]
    exact ⟨"read of uninitialized local", rfl⟩
  · simp only [hle, ↓reduceIte]
    exact ⟨"overflow computing total size of copy", rfl⟩

private theorem copyAnnealCopyEval_init {ly : LayoutTable}
    {v₁ v₂ : Miri.Interpreter.OpTy AnnealProv} {countLay : Miri.Interpreter.LocalLayout}
    {ptId : Miri.MIR.TyId} {elemBytes : Nat}
    {srcPtr dstPtr : Miri.Memory.Pointer (Option AnnealProv)}
    {countSc : MirAst.ScalarInt} {mcount : Miri.Memory.ScalarInt}
    (m : AnnealStepState)
    (hpt : annealPointeeTypeOf v₁.layout.ty m = .ok ptId m)
    (hlay_sz : (layoutOfEncodedTyId ptId ly).layout.size =
      Miri.ABI.Size.ofBytes (UInt64.ofNat elemBytes))
    (helem_lt : elemBytes < 2 ^ 64)
    (hsrc : intrinsicPointer v₁ m = .ok srcPtr m)
    (hdst : intrinsicPointer v₂ m = .ok dstPtr m)
    (hrelC : ScalarRel countSc mcount) (hszC : countSc.sizeBytes = 8) :
    annealCopyEval ly v₁ v₂ ⟨.immediate (.scalar (.fromScalarInt mcount)), countLay⟩ m =
      if countSc.bits * elemBytes ≤ isizeMaxBytes then
        (do
          annealCheckPtrAlign srcPtr (layoutOfEncodedTyId ptId ly).layout.align.abi
          annealCheckPtrAlign dstPtr (layoutOfEncodedTyId ptId ly).layout.align.abi
          annealMemCopy srcPtr dstPtr
            (Miri.ABI.Size.ofBytes (UInt64.ofNat (countSc.bits * elemBytes))) true) m
      else
        .error (.undefinedBehavior "overflow computing total size of copy") m := by
  obtain ⟨hcnt_lt, hcnt⟩ := copyIntrinsicUsize_fromScalarInt hrelC hszC countLay m
  have hcomp := computeSizeInBytes_writeBytes helem_lt hcnt_lt
  rw [annealCopyEval_eq, EStateM.bind_eq_ok hcnt, EStateM.bind_eq_ok hpt]
  rw [hlay_sz, hcomp]
  by_cases hle : countSc.bits * elemBytes ≤ isizeMaxBytes
  · simp only [hle, ↓reduceIte]
    rw [EStateM.bind_eq_ok hsrc, EStateM.bind_eq_ok hdst]
  · simp only [hle, ↓reduceIte]
    rfl

/-- Computable post-step `allocMap'` for
`copy_nonoverlapping::<T>(copy _src, copy _dst, countOp)` with pointee byte size
`elemBytes`: leaves `allocMap` unchanged on zero-byte copies
(`count * elemBytes = 0`) or non-tracked pointers, and applies
`updateAllocMapOnWrite allocMap e_dst.localIdx (some dstPtr.tag)` on
positive-byte copies into a tracked destination pointer `dstPtr`. -/
def copyNextAllocMap (locals : List LocalSlot) (allocMap : List AllocMapEntry)
    (dstIdx : Local) (countOp : MirAst.Operand) (elemBytes : Nat) : List AllocMapEntry :=
  writeBytesNextAllocMap locals allocMap dstIdx countOp elemBytes

/-! ## 6. End-to-end `CopyNonOverlapping` statement simulation and divergences -/

private theorem copyImmediateRel_of_integral {ty : Ty} {ly : LayoutTable}
    {kind : Miri.MIR.IntegerKind} {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    (h : IsIntegralTy ty kind)
    (hrelI : ImmediateRel ty ly (.scalar sc) (.scalar (.fromScalarInt msc))) :
    ScalarRel sc msc ∧ sc.sizeBytes = integerKindByteWidth kind := by
  obtain ⟨sc', msc', hsc, hmsc, hrel, hsz, _, _⟩ := hrelI.of_primitive_scalar h.prim
  injection hsc with hsc'; subst hsc'
  injection hmsc with h1
  unfold Miri.Memory.Scalar.fromScalarInt at h1
  injection h1 with h2
  injection h2 with h3; subst h3
  have hlay_sz :
      (translateTy ty ly).layout.size = translateSizeBytes (integerKindByteWidth kind) := by
    rw [← h.prim.translateTy_layoutIdx ly]
    rcases h with ⟨it, hk⟩ | ⟨ut, hk⟩
    · rw [hk]; cases it <;> rfl
    · rw [hk]; cases ut <;> rfl
  have heq : (translateSizeBytes sc.sizeBytes).bytes.toNat =
      (translateSizeBytes (integerKindByteWidth kind)).bytes.toNat := by
    rw [← hsz, hlay_sz]
  have h1 : (translateSizeBytes sc.sizeBytes).bytes.toNat = sc.sizeBytes := by
    rcases hrel.validBytes with hsz1 | hsz1 | hsz1 | hsz1 | hsz1 <;> (rw [hsz1]; rfl)
  have h2 : (translateSizeBytes (integerKindByteWidth kind)).bytes.toNat =
      integerKindByteWidth kind := by
    cases kind <;> rfl
  exact ⟨hrel, h1 ▸ h2 ▸ heq⟩

private theorem copyScalarVal?_of_evalOperand_ok
    {body : CapturedMir} {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {locals : List LocalSlot} {op : MirAst.Operand} {ty : Ty} {sc : MirAst.ScalarInt}
    {borrows : List BorrowEntry} {globals : List CapturedAllocation} {callerLocals : List LocalSlot}
    (hop : WellTypedScalarOperand body tf op ty)
    (heval : evalOperand locals op borrows globals body.layouts callerLocals =
      .ok (.scalar sc) locals) :
    writeBytesScalarVal? locals op = some sc ∧ WriteBytesScalarPreVal locals op sc := by
  cases hop with
  | constScalar c sc₀ hval _ _ _ _ _ _ =>
    unfold evalOperand at heval
    dsimp only at heval
    rw [hval] at heval
    injection heval with hv _
    injection hv with hsc
    subst hsc
    exact ⟨by simp [writeBytesScalarVal?, hval], Or.inl ⟨c, rfl, hval⟩⟩
  | copyLocal idx _ _ _ _ =>
    rw [evalOperand_copy_local_eq] at heval
    cases hslot : get? locals idx with
    | none => rw [hslot] at heval; cases heval
    | some slot =>
      cases slot with
      | dead => rw [hslot] at heval; cases heval
      | uninit => rw [hslot] at heval; cases heval
      | init v =>
        rw [hslot] at heval
        injection heval with hv _
        subst hv
        exact ⟨by simp [writeBytesScalarVal?, hslot], Or.inr ⟨idx, rfl, hslot⟩⟩

private theorem copyEvalOperand_scalar_ub_or_ok
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf])
    {op : MirAst.Operand} {ty : Ty}
    (hop : WellTypedScalarOperand body tf op ty)
    (hprim : IsPrimScalarTy ty) :
    (∃ m' msg,
      annealEvalOperand body.localDecls body.layouts (translateOperand op) none m =
        .error (.undefinedBehavior msg) m') ∨
    (∃ v tf',
      annealEvalOperand body.localDecls body.layouts (translateOperand op) none m =
        .ok v { m with stack := ⟨#[tf']⟩ } ∧
      StateRelLM3_1 body s { m with stack := ⟨#[tf']⟩ } allocMap ∧
      (∀ k : Nat, (tf'.locals[k]?).map Miri.Interpreter.LocalState.value =
        (tf.locals[k]?).map Miri.Interpreter.LocalState.value)) := by
  rcases annealEvalOperand_scalar_lm3_1 hstate hframes hop hprim with
    ⟨m', msg, _, hm⟩ | ⟨tf', _, hm, hst, hv⟩ | ⟨_, _, tf', _, hm, hst, _, hv⟩
  · exact Or.inl ⟨m', msg, hm⟩
  · exact Or.inr ⟨_, tf', hm, hst, hv⟩
  · exact Or.inr ⟨_, tf', hm, hst, hv⟩

private theorem copyLookupAllocMapByTag_of_mem_nodup
    {allocMap : List AllocMapEntry} (hnodup : (allocMap.map AllocMapEntry.tag).Nodup)
    {e : AllocMapEntry} (he : e ∈ allocMap) {t : Nat} (htag : e.tag = t) :
    lookupAllocMapByTag allocMap t = some e := by
  induction allocMap with
  | nil => cases he
  | cons hd tl ih =>
    simp only [List.map_cons, List.nodup_cons] at hnodup
    simp only [lookupAllocMapByTag]
    rcases List.mem_cons.mp he with rfl | hmem
    · subst htag; simp [Nat.beq_refl]
    · have hne : Nat.beq hd.tag t = false := by
        cases hb : Nat.beq hd.tag t
        · rfl
        · have heq := Nat.eq_of_beq_eq_true hb
          exact absurd (heq.trans htag.symm ▸ List.mem_map_of_mem hmem) hnodup.1
      rw [hne]
      exact ih hnodup.2 hmem

private theorem copyInvalidateConflictingBorrows_eq_map_updateAllocMapOnWrite
    (allocMap : List AllocMapEntry) (targetLocal : Local) (writerTag : Option Nat) :
    invalidateConflictingBorrows (allocMap.map AllocMapEntry.toBorrowEntry) targetLocal writerTag =
      (updateAllocMapOnWrite allocMap targetLocal writerTag).map AllocMapEntry.toBorrowEntry := by
  induction allocMap with
  | nil => rfl
  | cons e rest ih =>
    simp only [List.map_cons, invalidateConflictingBorrows_cons, updateAllocMapOnWrite,
      AllocMapEntry.toBorrowEntry_updateOnWrite, ih]

private theorem copy_inbounds_pos_eq {off cnt elem : Nat}
    (hpos : 0 < cnt * elem) (hle : off + cnt * elem ≤ elem) :
    off = 0 ∧ cnt = 1 ∧ 0 < elem := by
  have hcnt_ne : cnt ≠ 0 := by intro h; simp [h] at hpos
  have helem_ne : elem ≠ 0 := by intro h; simp [h] at hpos
  have hcnt_pos : 1 ≤ cnt := Nat.pos_of_ne_zero hcnt_ne
  have helem_pos : 0 < elem := Nat.pos_of_ne_zero helem_ne
  have hmul_ge : elem ≤ cnt * elem := by
    simpa [Nat.one_mul] using Nat.mul_le_mul_right elem hcnt_pos
  have hoff0 : off = 0 := by omega
  have hmul_eq : cnt * elem = elem := by omega
  have hcnt1 : cnt = 1 := by
    cases h : cnt with
    | zero => exact absurd h hcnt_ne
    | succ k =>
      cases k with
      | zero => rfl
      | succ k' =>
        have h2 : 2 * elem ≤ (k' + 1 + 1) * elem :=
          Nat.mul_le_mul_right elem (by omega)
        rw [h] at hmul_eq
        omega
  exact ⟨hoff0, hcnt1, helem_pos⟩

private theorem isPrimScalarTy_of_kind_eq {t₁ t₂ : Ty}
    (h₁ : IsPrimScalarTy t₁) (hk : t₁.kind = t₂.kind) : IsPrimScalarTy t₂ := by
  rcases h₁ with h | h | ⟨it, h⟩ | ⟨ut, h⟩
  · exact Or.inl (hk.symm.trans h)
  · exact Or.inr (Or.inl (hk.symm.trans h))
  · exact Or.inr (Or.inr (Or.inl ⟨it, hk.symm.trans h⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ut, hk.symm.trans h⟩))

private theorem primScalar_size_of_writeBytesPointee
    {ty : Ty} {ly : LayoutTable} {ptId : Miri.MIR.TyId} {elemBytes : Nat}
    (hprim : IsPrimScalarTy ty)
    (hwb : WriteBytesPointee ly ty.kind ptId elemBytes) :
    rigidTyByteSize ly ty = some elemBytes ∧
    (translateTy ty ly).layout.size = translateSizeBytes elemBytes ∧
    ValidScalarBytes elemBytes := by
  have hsz_eq : rigidTyByteSize ly ty = rigidTyByteSize ly { kind := ty.kind, layoutIdx := 0 } := by
    rcases hprim with hk | hk | ⟨it, hk⟩ | ⟨ut, hk⟩ <;>
      simp [rigidTyByteSize, rigidTyKindByteSize, hk]
    · cases it <;> rfl
    · cases ut <;> rfl
  have hb := hwb.anneal_size
  refine ⟨hsz_eq.trans hb, ?_⟩
  rw [← hprim.translateTy_layoutIdx ly]
  rcases hprim with hk | hk | ⟨it, hk⟩ | ⟨ut, hk⟩
  · rw [hk] at hb ⊢; injection hb with h; subst h; exact ⟨rfl, Or.inl rfl⟩
  · rw [hk] at hb ⊢; injection hb with h; subst h; exact ⟨rfl, Or.inr (Or.inr (Or.inl rfl))⟩
  · rw [hk] at hb ⊢; cases it <;>
      (injection hb with h; subst h; exact ⟨rfl, by simp [ValidScalarBytes]⟩)
  · rw [hk] at hb ⊢; cases ut <;>
      (injection hb with h; subst h; exact ⟨rfl, by simp [ValidScalarBytes]⟩)

private theorem sameRigidTyShape_of_primScalar {ty : Ty} (hprim : IsPrimScalarTy ty) :
    sameRigidTyShape ty.kind ty.kind = true := by
  rcases hprim with hk | hk | ⟨it, hk⟩ | ⟨ut, hk⟩ <;> rw [hk]
  · cases it <;> rfl
  · cases ut <;> rfl

private theorem stackScalarAllocShape_uninit_mask_eq
    {P E : Type} {n : Nat} (hn : ValidScalarBytes n)
    {alloc : Miri.Memory.Allocation P E}
    (hshape : StackScalarAllocShape (translateSizeBytes n) alloc)
    (hnot : alloc.initializationMask.isRangeInitialized
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes n)) ≠ .ok (.ok ())) :
    alloc.initializationMask = Miri.Memory.InitMask.new (translateSizeBytes n) false := by
  obtain ⟨b, hb⟩ := hshape.initMask_lazy
  cases b with
  | false => exact hb
  | true =>
    exfalso
    apply hnot
    rw [hb]
    rcases hn with rfl | rfl | rfl | rfl | rfl <;> rfl

private inductive CopyPtrArgRel (allocMap : List AllocMapEntry) :
    Value → Miri.Memory.Pointer (Option AnnealProv) → Prop where
  | scalar (sc : MirAst.ScalarInt) (hsz8 : sc.sizeBytes = 8) :
      CopyPtrArgRel allocMap (.scalar sc)
        (Miri.Memory.Pointer.withoutProvenance (UInt64.ofNat sc.bits))
  | ptr (ptrVal : ProvenancePtr) (mptr : Miri.Memory.Pointer AnnealProv)
      (hrel : PtrRel allocMap ptrVal mptr) :
      CopyPtrArgRel allocMap (.ptr ptrVal 8) mptr.withOptionalProvenance

private theorem CopyPtrArgRel.checkAlign
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hframes : m.stack.frames = #[tf])
    {reqAlign : Miri.ABI.Align} {elemAlign : Nat}
    (hpair : ValidCopyAlignPair reqAlign elemAlign)
    {val : Value} {mptr : Miri.Memory.Pointer (Option AnnealProv)}
    (harg : CopyPtrArgRel allocMap val mptr) :
    if ptrValueAligned elemAlign val = true then
      annealCheckPtrAlign mptr reqAlign m = .ok () m
    else
      annealCheckPtrAlign mptr reqAlign m =
        .error (.undefinedBehavior "accessing memory with an unaligned pointer") m := by
  cases harg with
  | scalar sc hsz8 => exact annealCheckPtrAlign_withoutProvenance hpair hsz8 m
  | ptr ptrVal p hrel => exact annealCheckPtrAlign_stackPtr hstate hframes hpair hrel

private theorem copyBle_eq_false_of_gt {a b : Nat} (h : ¬ a ≤ b) : Nat.ble a b = false := by
  cases hb : Nat.ble a b
  · rfl
  · exact absurd (Nat.ble_eq.mp hb) h

private theorem copyPrecheck_eq
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    {src : MirAst.Operand} {srcPt : Ty} {elemBytes elemAlign : Nat}
    (srcVal dstVal : Value) (countBits : Nat)
    (hop : operandPointeeTy localDecls layouts src = some srcPt)
    (hsz : rigidTyByteSize layouts srcPt = some elemBytes)
    (hal : rigidTyAlignBytes layouts srcPt = some elemAlign) :
    copyPrecheck localDecls layouts src srcVal dstVal countBits =
      if countBits * elemBytes ≤ isizeMaxBytes then
        if (ptrValueAligned elemAlign srcVal && ptrValueAligned elemAlign dstVal) = true then
          if countBits * elemBytes = 0 then .zero
          else .nonZero (some (countBits * elemBytes))
        else .ub
      else .ub := by
  unfold copyPrecheck
  rw [hop]; dsimp only
  rw [hsz]; dsimp only
  rw [show Nat.mul countBits elemBytes = countBits * elemBytes from rfl]
  have hmax : (9223372036854775807 : Nat) = isizeMaxBytes := rfl
  rw [hmax]
  by_cases hle : countBits * elemBytes ≤ isizeMaxBytes
  · rw [Nat.ble_eq.mpr hle]; dsimp only
    simp only [hle, ↓reduceIte]
    rw [hal]; dsimp only
    rw [show Bool.and (ptrValueAligned elemAlign srcVal) (ptrValueAligned elemAlign dstVal) =
      (ptrValueAligned elemAlign srcVal && ptrValueAligned elemAlign dstVal) from rfl]
    cases hok : (ptrValueAligned elemAlign srcVal && ptrValueAligned elemAlign dstVal) with
    | false => simp
    | true =>
      simp only [↓reduceIte]
      by_cases hz : countBits * elemBytes = 0
      · simp only [hz, ↓reduceIte]
        cases Nat.beq countBits 0 <;> rfl
      · simp only [hz, ↓reduceIte]
        have hc0 : Nat.beq countBits 0 = false := by
          cases hb : Nat.beq countBits 0
          · rfl
          · have hc := Nat.eq_of_beq_eq_true hb; simp [hc] at hz
        rw [hc0]; dsimp only
        cases htot : countBits * elemBytes with
        | zero => exact absurd htot hz
        | succ _ => rfl
  · rw [copyBle_eq_false_of_gt hle]; simp [hle]

private theorem lookupCopyBorrowChecked_root
    {localDecls : List LocalDecl} {layouts : LayoutTable} {borrows : List BorrowEntry}
    {ptr : ProvenancePtr} {e : AllocMapEntry} {decl : LocalDecl} {elemBytes total : Nat}
    (hlook : lookupBorrow borrows ptr.tag = some e.toBorrowEntry)
    (hdecl : get? localDecls e.localIdx = some decl)
    (hsz : rigidTyByteSize layouts decl.ty = some elemBytes) :
    lookupCopyBorrowChecked localDecls layouts borrows ptr (some total) =
      if ptr.offsetBytes + total ≤ elemBytes then some e.toBorrowEntry else none := by
  unfold lookupCopyBorrowChecked copyBorrowInRootBounds
  rw [hlook]; dsimp only [AllocMapEntry.toBorrowEntry]
  rw [hdecl]; dsimp only
  rw [hsz]; dsimp only
  rw [show Nat.add ptr.offsetBytes total = ptr.offsetBytes + total from rfl]
  by_cases hle : ptr.offsetBytes + total ≤ elemBytes
  · rw [Nat.ble_eq.mpr hle]; simp [hle]
  · rw [copyBle_eq_false_of_gt hle]; simp [hle]

private theorem evalCopySingleDirect_dead_src_ub
    {s : MachineState} {src dst : MirAst.Operand}
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    {srcPtr dstPtr : ProvenancePtr} {e_s e_d : AllocMapEntry}
    (_hcaller : s.memory.callerLocals = .nil)
    (hdead : get? s.frame.locals e_s.localIdx = some .dead) :
    evalCopySingleDirect s src dst localDecls layouts srcPtr dstPtr
        e_s.toBorrowEntry e_d.toBorrowEntry s.frame.locals =
      MirStepNode.fail .ub := by
  have hpo : projectionsOverlap .nil .nil = true := rfl
  unfold evalCopySingleDirect
  dsimp only [AllocMapEntry.toBorrowEntry]
  cases Nat.beq srcPtr.tag dstPtr.tag with
  | true => rfl
  | false =>
    dsimp only
    cases Nat.beq e_s.localIdx e_d.localIdx with
    | true => dsimp only; rw [hpo]
    | false => dsimp only; rw [hdead]

private theorem evalCopySingleDirect_dead_dst_ub
    {s : MachineState} {src dst : MirAst.Operand}
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    {srcPtr dstPtr : ProvenancePtr} {e_s e_d : AllocMapEntry}
    {pointeeTy : Ty}
    (_hcaller : s.memory.callerLocals = .nil)
    (hprim : IsPrimScalarTy pointeeTy)
    (hopS : operandPointeeTy localDecls layouts src = some { kind := pointeeTy.kind, layoutIdx := 0 })
    (hopD : operandPointeeTy localDecls layouts dst = some { kind := pointeeTy.kind, layoutIdx := 0 })
    {slot_s : LocalSlot}
    (hslot_s : get? s.frame.locals e_s.localIdx = some slot_s)
    (hdead_d : get? s.frame.locals e_d.localIdx = some .dead) :
    evalCopySingleDirect s src dst localDecls layouts srcPtr dstPtr
        e_s.toBorrowEntry e_d.toBorrowEntry s.frame.locals =
      MirStepNode.fail .ub := by
  have hpo : projectionsOverlap .nil .nil = true := rfl
  unfold evalCopySingleDirect
  dsimp only [AllocMapEntry.toBorrowEntry]
  cases Nat.beq srcPtr.tag dstPtr.tag with
  | true => rfl
  | false =>
    dsimp only
    cases Nat.beq e_s.localIdx e_d.localIdx with
    | true => dsimp only; rw [hpo]
    | false =>
      dsimp only
      rw [hslot_s]
      cases slot_s with
      | dead => rfl
      | uninit => rfl
      | init v_s =>
        dsimp only [readProjectedValue]
        rw [hopS, hopD]; dsimp only
        rw [sameRigidTyShape_of_primScalar hprim]; dsimp only
        unfold writePlaceValue; dsimp only
        rw [hdead_d]

private theorem evalCopySingleDirect_overlap_ub
    {s : MachineState} {src dst : MirAst.Operand}
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    {srcPtr dstPtr : ProvenancePtr} {e_s e_d : AllocMapEntry}
    (hsame : e_s.localIdx = e_d.localIdx) :
    evalCopySingleDirect s src dst localDecls layouts srcPtr dstPtr
        e_s.toBorrowEntry e_d.toBorrowEntry s.frame.locals =
      MirStepNode.fail .ub := by
  have hpo : projectionsOverlap .nil .nil = true := rfl
  unfold evalCopySingleDirect
  dsimp only [AllocMapEntry.toBorrowEntry]
  cases Nat.beq srcPtr.tag dstPtr.tag with
  | true => rfl
  | false =>
    dsimp only
    rw [hsame, Nat.beq_refl]; dsimp only; rw [hpo]

private theorem evalCopySingleDirect_uninit_src_ub
    {s : MachineState} {src dst : MirAst.Operand}
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    {srcPtr dstPtr : ProvenancePtr} {e_s e_d : AllocMapEntry}
    (huninit : get? s.frame.locals e_s.localIdx = some .uninit) :
    evalCopySingleDirect s src dst localDecls layouts srcPtr dstPtr
        e_s.toBorrowEntry e_d.toBorrowEntry s.frame.locals =
      MirStepNode.fail .ub := by
  have hpo : projectionsOverlap .nil .nil = true := rfl
  unfold evalCopySingleDirect
  dsimp only [AllocMapEntry.toBorrowEntry]
  cases Nat.beq srcPtr.tag dstPtr.tag with
  | true => rfl
  | false =>
    dsimp only
    cases Nat.beq e_s.localIdx e_d.localIdx with
    | true => dsimp only; rw [hpo]
    | false => dsimp only; rw [huninit]

private theorem evalCopySingleDirect_distinct_ok
    {s : MachineState} {src dst : MirAst.Operand}
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    {srcPtr dstPtr : ProvenancePtr} {e_s e_d : AllocMapEntry}
    {pointeeTy : Ty} {sc_s : MirAst.ScalarInt} {slot_d : LocalSlot}
    (hprim : IsPrimScalarTy pointeeTy)
    (hopS : operandPointeeTy localDecls layouts src = some { kind := pointeeTy.kind, layoutIdx := 0 })
    (hopD : operandPointeeTy localDecls layouts dst = some { kind := pointeeTy.kind, layoutIdx := 0 })
    (hne_tag : srcPtr.tag ≠ dstPtr.tag)
    (hne_loc : e_s.localIdx ≠ e_d.localIdx)
    (hslot_s : get? s.frame.locals e_s.localIdx = some (.init (.scalar sc_s)))
    (hslot_d : get? s.frame.locals e_d.localIdx = some slot_d)
    (hne_dead_d : slot_d ≠ .dead) :
    evalCopySingleDirect s src dst localDecls layouts srcPtr dstPtr
        e_s.toBorrowEntry e_d.toBorrowEntry s.frame.locals =
      MirStepNode.step
        (advanceStmt s (s.frame.locals.set e_d.localIdx (.init (.scalar sc_s)))
          { s.memory with
            borrows := invalidateConflictingBorrows s.memory.borrows e_d.localIdx
              (some dstPtr.tag) }) := by
  have hb_tag : Nat.beq srcPtr.tag dstPtr.tag = false := by
    cases h : Nat.beq srcPtr.tag dstPtr.tag
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true h) hne_tag
  have hb_loc : Nat.beq e_s.localIdx e_d.localIdx = false := by
    cases h : Nat.beq e_s.localIdx e_d.localIdx
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true h) hne_loc
  have hlt_d : e_d.localIdx < s.frame.locals.length := by
    rw [get?_eq_getElem?] at hslot_d
    exact (List.getElem?_eq_some_iff.mp hslot_d).1
  have hset_d := set?_eq_some_set hlt_d (.init (.scalar sc_s))
  unfold evalCopySingleDirect
  dsimp only [AllocMapEntry.toBorrowEntry]
  rw [hb_tag]; dsimp only
  rw [hb_loc]; dsimp only
  rw [hslot_s]; dsimp only [readProjectedValue]
  rw [hopS, hopD]; dsimp only
  rw [sameRigidTyShape_of_primScalar hprim]; dsimp only
  unfold writePlaceValue; dsimp only
  rw [hslot_d]
  cases slot_d with
  | dead => exact absurd rfl hne_dead_d
  | uninit => dsimp only; rw [hset_d]
  | init _ => dsimp only; rw [hset_d]

private def copyMiriStmtAction (body : CapturedMir) (srcIdx dstIdx : Local)
    (countOp : MirAst.Operand) :
    Miri.Interpreter.RvalueM AnnealStepState Unit := do
  let source ← annealEvalOperand body.localDecls body.layouts (.Copy ⟨srcIdx, #[]⟩) none
  let dest ← annealEvalOperand body.localDecls body.layouts (.Copy ⟨dstIdx, #[]⟩) none
  let cnt ← annealEvalOperand body.localDecls body.layouts (translateOperand countOp) none
  annealCopyEval body.layouts source dest cnt

private theorem evalStatement_copyNonOverlapping_eq
    (body : CapturedMir) (srcIdx dstIdx : Local) (countOp : MirAst.Operand) (span : String)
    (m : AnnealStepState) :
    Miri.Interpreter.Step.evalStatement
        (annealStepHooks body.localDecls body.layouts) ()
        (translateStmt
          ⟨.intrinsic (.copyNonOverlapping (.copy ⟨srcIdx, []⟩) (.copy ⟨dstIdx, []⟩) countOp),
            span⟩) m =
      Miri.Interpreter.runRvalue (copyMiriStmtAction body srcIdx dstIdx countOp) m := rfl

private theorem copyStep_miri_ub
    {body : CapturedMir} {s : MachineState} {m m' : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {bb : BasicBlockData} {srcIdx dstIdx : Local} {countOp : MirAst.Operand} {span msg : String}
    (hframes : m.stack.frames = #[tf])
    (hbody : tf.body = translateBody body)
    (hloc : tf.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩)
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.intrinsic (.copyNonOverlapping (.copy ⟨srcIdx, []⟩) (.copy ⟨dstIdx, []⟩) countOp),
        span⟩)
    (hact : copyMiriStmtAction body srcIdx dstIdx countOp m =
      .error (.undefinedBehavior msg) m') :
    Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
      (m', .error (.undefinedBehavior msg)) := by
  have hm_err : Miri.Interpreter.Step.evalStatement
      (annealStepHooks body.localDecls body.layouts) ()
      (translateStmt
        ⟨.intrinsic (.copyNonOverlapping (.copy ⟨srcIdx, []⟩) (.copy ⟨dstIdx, []⟩) countOp),
          span⟩) m =
      (m', .error (.undefinedBehavior msg)) := by
    rw [evalStatement_copyNonOverlapping_eq]
    unfold Miri.Interpreter.runRvalue
    rw [hact]
  exact miri_step_at_statement_error _ hframes hbody hloc hbb hstmt hm_err

private theorem copyStep_miri_ok
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {tf tf' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {mach' : AnnealMachine}
    {bb : BasicBlockData} {srcIdx dstIdx : Local} {countOp : MirAst.Operand} {span : String}
    (hframes : m.stack.frames = #[tf])
    (hbody : tf.body = translateBody body)
    (hloc : tf.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩)
    (hloc' : tf'.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩)
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.intrinsic (.copyNonOverlapping (.copy ⟨srcIdx, []⟩) (.copy ⟨dstIdx, []⟩) countOp),
        span⟩)
    (hact : copyMiriStmtAction body srcIdx dstIdx countOp m =
      .ok () { stack := ⟨#[tf']⟩, machine := mach' }) :
    Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
      ({ stack := ⟨#[{ tf' with location := .mir ⟨s.frame.blockIdx, s.frame.stmtIdx + 1⟩ }]⟩,
         machine := mach' }, .ok true) := by
  have hm_ok : Miri.Interpreter.Step.evalStatement
      (annealStepHooks body.localDecls body.layouts) ()
      (translateStmt
        ⟨.intrinsic (.copyNonOverlapping (.copy ⟨srcIdx, []⟩) (.copy ⟨dstIdx, []⟩) countOp),
          span⟩) m =
      ({ stack := ⟨#[tf']⟩, machine := mach' }, .ok ()) := by
    rw [evalStatement_copyNonOverlapping_eq]
    unfold Miri.Interpreter.runRvalue
    rw [hact]
  exact miri_step_at_statement_ok _ hframes hbody hloc hbb hstmt hm_ok rfl hloc'

/-- Evaluate `(src, dst)` raw-pointer operands in lockstep: either both report UB
(when `src`, `dst`, or `count` fails to read), or both yield initialized
`CopyPtrArgRel`-related pointer arguments and a `StateRelLM3_1`-related frame. -/
private theorem copyEvalSrcDst_lockstep
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf])
    {srcIdx dstIdx : Local} {countOp : MirAst.Operand}
    {srcDecl dstDecl : LocalDecl} {srcMut dstMut : Mutability} {pointeeTy countTy : Ty}
    {ptId : Miri.MIR.TyId} {elemBytes elemAlign : Nat}
    (hsrcDecl : get? body.localDecls srcIdx = some srcDecl)
    (hsrcTy : srcDecl.ty.kind = .rawPtr srcMut pointeeTy.kind)
    (hsrcImm : IsImmediateFrameLocal tf srcIdx)
    (hdstDecl : get? body.localDecls dstIdx = some dstDecl)
    (hdstTy : dstDecl.ty.kind = .rawPtr dstMut pointeeTy.kind)
    (hdstImm : IsImmediateFrameLocal tf dstIdx)
    (hcountInt : IsIntegralTy countTy .usize)
    (hcountOp : WellTypedScalarOperand body tf countOp countTy)
    (hpt : CopyPointee body.layouts pointeeTy.kind ptId elemBytes elemAlign) :
    (evalCopyNonOverlapping s (.copy ⟨srcIdx, []⟩) (.copy ⟨dstIdx, []⟩) countOp
        body.localDecls body.layouts = MirStepNode.fail .ub ∧
      ∃ m' msg, copyMiriStmtAction body srcIdx dstIdx countOp m =
        .error (.undefinedBehavior msg) m') ∨
    (∃ srcVal msrcPtr dstVal mdstPtr countSc mcount tf₃,
      CopyPtrArgRel allocMap srcVal msrcPtr ∧
      CopyPtrArgRel allocMap dstVal mdstPtr ∧
      (∀ srcPtr, srcVal = .ptr srcPtr 8 → get? s.frame.locals srcIdx = some (.init (.ptr srcPtr 8))) ∧
      (∀ dstPtr, dstVal = .ptr dstPtr 8 → get? s.frame.locals dstIdx = some (.init (.ptr dstPtr 8))) ∧
      ScalarRel countSc mcount ∧ countSc.sizeBytes = 8 ∧
      writeBytesScalarVal? s.frame.locals countOp = some countSc ∧
      WriteBytesScalarPreVal s.frame.locals countOp countSc ∧
      evalCopyNonOverlapping s (.copy ⟨srcIdx, []⟩) (.copy ⟨dstIdx, []⟩) countOp
          body.localDecls body.layouts =
        evalCopyNonOverlappingWithCount s (.copy ⟨srcIdx, []⟩) (.copy ⟨dstIdx, []⟩)
          body.localDecls body.layouts srcVal dstVal countSc.bits s.frame.locals ∧
      copyMiriStmtAction body srcIdx dstIdx countOp m =
        (if countSc.bits * elemBytes ≤ isizeMaxBytes then
          (do
            annealCheckPtrAlign msrcPtr (layoutOfEncodedTyId ptId body.layouts).layout.align.abi
            annealCheckPtrAlign mdstPtr (layoutOfEncodedTyId ptId body.layouts).layout.align.abi
            annealMemCopy msrcPtr mdstPtr
              (Miri.ABI.Size.ofBytes (UInt64.ofNat (countSc.bits * elemBytes))) true)
            { m with stack := ⟨#[tf₃]⟩ }
        else
          .error (.undefinedBehavior "overflow computing total size of copy")
            { m with stack := ⟨#[tf₃]⟩ }) ∧
      StateRelLM3_1 body s { m with stack := ⟨#[tf₃]⟩ } allocMap) := by
  have hpt_m : ∀ st, annealPointeeTypeOf (translateTy srcDecl.ty body.layouts).ty st =
      .ok ptId st := annealPointeeTypeOf_rawPtr hsrcTy hpt.wb.encoded_eq
  -- Evaluate `src`.
  rcases annealEvalOperand_rawPtr_lm3_1 hstate hframes hsrcDecl hsrcTy hsrcImm with
    ⟨hsrc_dead, m₁, msg, hm₁⟩ |
    ⟨tf₁, hsrc_un, hm₁, hstate₁, hvals₁⟩ |
    ⟨sc_s, msc_s, tf₁, hsrc_sc, hsz8_s, hrel_s, hm₁, hstate₁, hvals₁⟩ |
    ⟨srcPtr, mptr_s, tf₁, hsrc_ptr, hptrRel_s, hm₁, hstate₁, hvals₁⟩
  · -- `src` is `.dead`.
    left
    refine ⟨?_, m₁, msg, by unfold copyMiriStmtAction; rw [EStateM.bind_eq_error hm₁]⟩
    unfold evalCopyNonOverlapping; rw [evalOperand_copy_local_eq, hsrc_dead]
  · -- `src` is `.uninit`.
    have ha_ub : evalCopyNonOverlapping s (.copy ⟨srcIdx, []⟩) (.copy ⟨dstIdx, []⟩) countOp
        body.localDecls body.layouts = MirStepNode.fail .ub := by
      unfold evalCopyNonOverlapping; rw [evalOperand_copy_local_eq, hsrc_un]
    have hdstImm₁ : IsImmediateFrameLocal tf₁ dstIdx :=
      IsImmediateFrameLocal.of_values_eq hvals₁ hdstImm
    rcases annealEvalOperand_rawPtr_lm3_1 hstate₁ rfl hdstDecl hdstTy hdstImm₁ with
      ⟨_, m₂, msg, hm₂⟩ | ⟨tf₂, _, hm₂, hstate₂, hvals₂⟩ |
      ⟨_, _, tf₂, _, _, _, hm₂, hstate₂, hvals₂⟩ | ⟨_, _, tf₂, _, _, hm₂, hstate₂, hvals₂⟩
    · left; exact ⟨ha_ub, m₂, msg,
        by unfold copyMiriStmtAction; rw [EStateM.bind_eq_ok hm₁, EStateM.bind_eq_error hm₂]⟩
    all_goals
      have himm₂ : ∀ j, IsImmediateFrameLocal tf j → IsImmediateFrameLocal tf₂ j :=
        fun j hj => IsImmediateFrameLocal.of_values_eq hvals₂
          (IsImmediateFrameLocal.of_values_eq hvals₁ hj)
      rcases annealEvalOperand_scalar_lm3_1 hstate₂ rfl (hcountOp.mono_immediate himm₂)
          hcountInt.prim with
        ⟨m₃, msg, _, hm₃⟩ | ⟨tf₃, _, hm₃, _, _⟩ | ⟨countSc, mcount, tf₃, _, hm₃, _, hrelI_c, _⟩
      · left; exact ⟨ha_ub, m₃, msg, by
          unfold copyMiriStmtAction
          rw [EStateM.bind_eq_ok hm₁, EStateM.bind_eq_ok hm₂, EStateM.bind_eq_error hm₃]⟩
      · left; exact ⟨ha_ub, _, _, by
          unfold copyMiriStmtAction
          rw [EStateM.bind_eq_ok hm₁, EStateM.bind_eq_ok hm₂, EStateM.bind_eq_ok hm₃]
          exact copyAnnealCopyEval_uninit_count _ _ _ _⟩
      · obtain ⟨hrelC, hszC⟩ := copyImmediateRel_of_integral hcountInt hrelI_c
        obtain ⟨msg, hev_err⟩ := copyAnnealCopyEval_uninit_src _ { m with stack := ⟨#[tf₃]⟩ }
          (hpt_m _) hpt.wb.miri_size hpt.wb.lt_u64 hrelC hszC
          (countLay := translateTy countTy body.layouts)
        left; exact ⟨ha_ub, _, msg, by
          unfold copyMiriStmtAction
          rw [EStateM.bind_eq_ok hm₁, EStateM.bind_eq_ok hm₂, EStateM.bind_eq_ok hm₃]
          exact hev_err⟩
  · -- `src` is `.scalar sc_s` (`CopyPtrArgRel.scalar`).
    have ha₁ : evalOperand s.frame.locals (.copy ⟨srcIdx, []⟩) s.memory.borrows s.memory.globals
        body.layouts s.memory.callerLocals = .ok (.scalar sc_s) s.frame.locals := by
      rw [evalOperand_copy_local_eq, hsrc_sc]
    have hsrcP := copyIntrinsicPointer_fromScalarInt hrel_s hsz8_s
      (translateTy srcDecl.ty body.layouts)
    have hdstImm₁ : IsImmediateFrameLocal tf₁ dstIdx :=
      IsImmediateFrameLocal.of_values_eq hvals₁ hdstImm
    rcases annealEvalOperand_rawPtr_lm3_1 hstate₁ rfl hdstDecl hdstTy hdstImm₁ with
      ⟨hdst_dead, m₂, msg, hm₂⟩ |
      ⟨tf₂, hdst_un, hm₂, hstate₂, hvals₂⟩ |
      ⟨sc_d, msc_d, tf₂, hdst_sc, hsz8_d, hrel_d, hm₂, hstate₂, hvals₂⟩ |
      ⟨dstPtr, mptr_d, tf₂, hdst_ptr, hptrRel_d, hm₂, hstate₂, hvals₂⟩
    · left; refine ⟨?_, m₂, msg,
        by unfold copyMiriStmtAction; rw [EStateM.bind_eq_ok hm₁, EStateM.bind_eq_error hm₂]⟩
      unfold evalCopyNonOverlapping; rw [ha₁]; dsimp only
      rw [evalOperand_copy_local_eq, hdst_dead]
    · have ha_ub : evalCopyNonOverlapping s (.copy ⟨srcIdx, []⟩) (.copy ⟨dstIdx, []⟩) countOp
          body.localDecls body.layouts = MirStepNode.fail .ub := by
        unfold evalCopyNonOverlapping; rw [ha₁]; dsimp only
        rw [evalOperand_copy_local_eq, hdst_un]
      have himm₂ : ∀ j, IsImmediateFrameLocal tf j → IsImmediateFrameLocal tf₂ j :=
        fun j hj => IsImmediateFrameLocal.of_values_eq hvals₂
          (IsImmediateFrameLocal.of_values_eq hvals₁ hj)
      rcases annealEvalOperand_scalar_lm3_1 hstate₂ rfl (hcountOp.mono_immediate himm₂)
          hcountInt.prim with
        ⟨m₃, msg, _, hm₃⟩ | ⟨tf₃, _, hm₃, _, _⟩ | ⟨countSc, mcount, tf₃, _, hm₃, _, hrelI_c, _⟩
      · left; exact ⟨ha_ub, m₃, msg, by
          unfold copyMiriStmtAction
          rw [EStateM.bind_eq_ok hm₁, EStateM.bind_eq_ok hm₂, EStateM.bind_eq_error hm₃]⟩
      · left; exact ⟨ha_ub, _, _, by
          unfold copyMiriStmtAction
          rw [EStateM.bind_eq_ok hm₁, EStateM.bind_eq_ok hm₂, EStateM.bind_eq_ok hm₃]
          exact copyAnnealCopyEval_uninit_count _ _ _ _⟩
      · obtain ⟨hrelC, hszC⟩ := copyImmediateRel_of_integral hcountInt hrelI_c
        obtain ⟨msg, hev_err⟩ := copyAnnealCopyEval_uninit_dst { m with stack := ⟨#[tf₃]⟩ }
          (hpt_m _) hpt.wb.miri_size hpt.wb.lt_u64 (hsrcP _) hrelC hszC
          (dstLay := translateTy dstDecl.ty body.layouts)
          (countLay := translateTy countTy body.layouts)
        left; exact ⟨ha_ub, _, msg, by
          unfold copyMiriStmtAction
          rw [EStateM.bind_eq_ok hm₁, EStateM.bind_eq_ok hm₂, EStateM.bind_eq_ok hm₃]
          exact hev_err⟩
    · have ha₂ : evalOperand s.frame.locals (.copy ⟨dstIdx, []⟩) s.memory.borrows s.memory.globals
          body.layouts s.memory.callerLocals = .ok (.scalar sc_d) s.frame.locals := by
        rw [evalOperand_copy_local_eq, hdst_sc]
      have himm₂ : ∀ j, IsImmediateFrameLocal tf j → IsImmediateFrameLocal tf₂ j :=
        fun j hj => IsImmediateFrameLocal.of_values_eq hvals₂
          (IsImmediateFrameLocal.of_values_eq hvals₁ hj)
      rcases annealEvalOperand_scalar_lm3_1 hstate₂ rfl (hcountOp.mono_immediate himm₂)
          hcountInt.prim with
        ⟨m₃, msg, ha₃, hm₃⟩ | ⟨tf₃, ha₃, hm₃, _, _⟩ |
        ⟨countSc, mcount, tf₃, ha₃, hm₃, hstate₃, hrelI_c, _⟩
      · left; refine ⟨?_, m₃, msg, by
          unfold copyMiriStmtAction
          rw [EStateM.bind_eq_ok hm₁, EStateM.bind_eq_ok hm₂, EStateM.bind_eq_error hm₃]⟩
        unfold evalCopyNonOverlapping; rw [ha₁]; dsimp only; rw [ha₂]; dsimp only; rw [ha₃]
      · left; refine ⟨?_, _, _, by
          unfold copyMiriStmtAction
          rw [EStateM.bind_eq_ok hm₁, EStateM.bind_eq_ok hm₂, EStateM.bind_eq_ok hm₃]
          exact copyAnnealCopyEval_uninit_count _ _ _ _⟩
        unfold evalCopyNonOverlapping; rw [ha₁]; dsimp only; rw [ha₂]; dsimp only; rw [ha₃]
      · obtain ⟨hrelC, hszC⟩ := copyImmediateRel_of_integral hcountInt hrelI_c
        obtain ⟨hc_opt, hc_pre⟩ := copyScalarVal?_of_evalOperand_ok hcountOp ha₃
        right
        refine ⟨.scalar sc_s, _, .scalar sc_d, _, countSc, mcount, tf₃,
          .scalar sc_s hsz8_s, .scalar sc_d hsz8_d,
          (by intro _ h; cases h), (by intro _ h; cases h),
          hrelC, hszC, hc_opt, hc_pre, ?_, ?_, hstate₃⟩
        · unfold evalCopyNonOverlapping; rw [ha₁]; dsimp only; rw [ha₂]; dsimp only; rw [ha₃]
        · unfold copyMiriStmtAction
          rw [EStateM.bind_eq_ok hm₁, EStateM.bind_eq_ok hm₂, EStateM.bind_eq_ok hm₃]
          exact copyAnnealCopyEval_init _ (hpt_m _) hpt.wb.miri_size hpt.wb.lt_u64 (hsrcP _)
            (copyIntrinsicPointer_fromScalarInt hrel_d hsz8_d
              (translateTy dstDecl.ty body.layouts) _) hrelC hszC
    · have ha₂ : evalOperand s.frame.locals (.copy ⟨dstIdx, []⟩) s.memory.borrows s.memory.globals
          body.layouts s.memory.callerLocals = .ok (.ptr dstPtr 8) s.frame.locals := by
        rw [evalOperand_copy_local_eq, hdst_ptr]
      have himm₂ : ∀ j, IsImmediateFrameLocal tf j → IsImmediateFrameLocal tf₂ j :=
        fun j hj => IsImmediateFrameLocal.of_values_eq hvals₂
          (IsImmediateFrameLocal.of_values_eq hvals₁ hj)
      rcases annealEvalOperand_scalar_lm3_1 hstate₂ rfl (hcountOp.mono_immediate himm₂)
          hcountInt.prim with
        ⟨m₃, msg, ha₃, hm₃⟩ | ⟨tf₃, ha₃, hm₃, _, _⟩ |
        ⟨countSc, mcount, tf₃, ha₃, hm₃, hstate₃, hrelI_c, _⟩
      · left; refine ⟨?_, m₃, msg, by
          unfold copyMiriStmtAction
          rw [EStateM.bind_eq_ok hm₁, EStateM.bind_eq_ok hm₂, EStateM.bind_eq_error hm₃]⟩
        unfold evalCopyNonOverlapping; rw [ha₁]; dsimp only; rw [ha₂]; dsimp only; rw [ha₃]
      · left; refine ⟨?_, _, _, by
          unfold copyMiriStmtAction
          rw [EStateM.bind_eq_ok hm₁, EStateM.bind_eq_ok hm₂, EStateM.bind_eq_ok hm₃]
          exact copyAnnealCopyEval_uninit_count _ _ _ _⟩
        unfold evalCopyNonOverlapping; rw [ha₁]; dsimp only; rw [ha₂]; dsimp only; rw [ha₃]
      · obtain ⟨hrelC, hszC⟩ := copyImmediateRel_of_integral hcountInt hrelI_c
        obtain ⟨hc_opt, hc_pre⟩ := copyScalarVal?_of_evalOperand_ok hcountOp ha₃
        right
        refine ⟨.scalar sc_s, _, .ptr dstPtr 8, _, countSc, mcount, tf₃,
          .scalar sc_s hsz8_s, .ptr dstPtr mptr_d hptrRel_d,
          (by intro _ h; cases h),
          (by intro p h; injection h with h1 _; subst h1; exact hdst_ptr),
          hrelC, hszC, hc_opt, hc_pre, ?_, ?_, hstate₃⟩
        · unfold evalCopyNonOverlapping; rw [ha₁]; dsimp only; rw [ha₂]; dsimp only; rw [ha₃]
        · unfold copyMiriStmtAction
          rw [EStateM.bind_eq_ok hm₁, EStateM.bind_eq_ok hm₂, EStateM.bind_eq_ok hm₃]
          exact copyAnnealCopyEval_init _ (hpt_m _) hpt.wb.miri_size hpt.wb.lt_u64 (hsrcP _)
            (copyIntrinsicPointer_fromPointer mptr_d (translateTy dstDecl.ty body.layouts) _)
            hrelC hszC
  · -- `src` is `.ptr srcPtr 8` (`CopyPtrArgRel.ptr`).
    have ha₁ : evalOperand s.frame.locals (.copy ⟨srcIdx, []⟩) s.memory.borrows s.memory.globals
        body.layouts s.memory.callerLocals = .ok (.ptr srcPtr 8) s.frame.locals := by
      rw [evalOperand_copy_local_eq, hsrc_ptr]
    have hsrcP := copyIntrinsicPointer_fromPointer mptr_s (translateTy srcDecl.ty body.layouts)
    have hdstImm₁ : IsImmediateFrameLocal tf₁ dstIdx :=
      IsImmediateFrameLocal.of_values_eq hvals₁ hdstImm
    rcases annealEvalOperand_rawPtr_lm3_1 hstate₁ rfl hdstDecl hdstTy hdstImm₁ with
      ⟨hdst_dead, m₂, msg, hm₂⟩ |
      ⟨tf₂, hdst_un, hm₂, hstate₂, hvals₂⟩ |
      ⟨sc_d, msc_d, tf₂, hdst_sc, hsz8_d, hrel_d, hm₂, hstate₂, hvals₂⟩ |
      ⟨dstPtr, mptr_d, tf₂, hdst_ptr, hptrRel_d, hm₂, hstate₂, hvals₂⟩
    · left; refine ⟨?_, m₂, msg,
        by unfold copyMiriStmtAction; rw [EStateM.bind_eq_ok hm₁, EStateM.bind_eq_error hm₂]⟩
      unfold evalCopyNonOverlapping; rw [ha₁]; dsimp only
      rw [evalOperand_copy_local_eq, hdst_dead]
    · have ha_ub : evalCopyNonOverlapping s (.copy ⟨srcIdx, []⟩) (.copy ⟨dstIdx, []⟩) countOp
          body.localDecls body.layouts = MirStepNode.fail .ub := by
        unfold evalCopyNonOverlapping; rw [ha₁]; dsimp only
        rw [evalOperand_copy_local_eq, hdst_un]
      have himm₂ : ∀ j, IsImmediateFrameLocal tf j → IsImmediateFrameLocal tf₂ j :=
        fun j hj => IsImmediateFrameLocal.of_values_eq hvals₂
          (IsImmediateFrameLocal.of_values_eq hvals₁ hj)
      rcases annealEvalOperand_scalar_lm3_1 hstate₂ rfl (hcountOp.mono_immediate himm₂)
          hcountInt.prim with
        ⟨m₃, msg, _, hm₃⟩ | ⟨tf₃, _, hm₃, _, _⟩ | ⟨countSc, mcount, tf₃, _, hm₃, _, hrelI_c, _⟩
      · left; exact ⟨ha_ub, m₃, msg, by
          unfold copyMiriStmtAction
          rw [EStateM.bind_eq_ok hm₁, EStateM.bind_eq_ok hm₂, EStateM.bind_eq_error hm₃]⟩
      · left; exact ⟨ha_ub, _, _, by
          unfold copyMiriStmtAction
          rw [EStateM.bind_eq_ok hm₁, EStateM.bind_eq_ok hm₂, EStateM.bind_eq_ok hm₃]
          exact copyAnnealCopyEval_uninit_count _ _ _ _⟩
      · obtain ⟨hrelC, hszC⟩ := copyImmediateRel_of_integral hcountInt hrelI_c
        obtain ⟨msg, hev_err⟩ := copyAnnealCopyEval_uninit_dst { m with stack := ⟨#[tf₃]⟩ }
          (hpt_m _) hpt.wb.miri_size hpt.wb.lt_u64 (hsrcP _) hrelC hszC
          (dstLay := translateTy dstDecl.ty body.layouts)
          (countLay := translateTy countTy body.layouts)
        left; exact ⟨ha_ub, _, msg, by
          unfold copyMiriStmtAction
          rw [EStateM.bind_eq_ok hm₁, EStateM.bind_eq_ok hm₂, EStateM.bind_eq_ok hm₃]
          exact hev_err⟩
    · have ha₂ : evalOperand s.frame.locals (.copy ⟨dstIdx, []⟩) s.memory.borrows s.memory.globals
          body.layouts s.memory.callerLocals = .ok (.scalar sc_d) s.frame.locals := by
        rw [evalOperand_copy_local_eq, hdst_sc]
      have himm₂ : ∀ j, IsImmediateFrameLocal tf j → IsImmediateFrameLocal tf₂ j :=
        fun j hj => IsImmediateFrameLocal.of_values_eq hvals₂
          (IsImmediateFrameLocal.of_values_eq hvals₁ hj)
      rcases annealEvalOperand_scalar_lm3_1 hstate₂ rfl (hcountOp.mono_immediate himm₂)
          hcountInt.prim with
        ⟨m₃, msg, ha₃, hm₃⟩ | ⟨tf₃, ha₃, hm₃, _, _⟩ |
        ⟨countSc, mcount, tf₃, ha₃, hm₃, hstate₃, hrelI_c, _⟩
      · left; refine ⟨?_, m₃, msg, by
          unfold copyMiriStmtAction
          rw [EStateM.bind_eq_ok hm₁, EStateM.bind_eq_ok hm₂, EStateM.bind_eq_error hm₃]⟩
        unfold evalCopyNonOverlapping; rw [ha₁]; dsimp only; rw [ha₂]; dsimp only; rw [ha₃]
      · left; refine ⟨?_, _, _, by
          unfold copyMiriStmtAction
          rw [EStateM.bind_eq_ok hm₁, EStateM.bind_eq_ok hm₂, EStateM.bind_eq_ok hm₃]
          exact copyAnnealCopyEval_uninit_count _ _ _ _⟩
        unfold evalCopyNonOverlapping; rw [ha₁]; dsimp only; rw [ha₂]; dsimp only; rw [ha₃]
      · obtain ⟨hrelC, hszC⟩ := copyImmediateRel_of_integral hcountInt hrelI_c
        obtain ⟨hc_opt, hc_pre⟩ := copyScalarVal?_of_evalOperand_ok hcountOp ha₃
        right
        refine ⟨.ptr srcPtr 8, _, .scalar sc_d, _, countSc, mcount, tf₃,
          .ptr srcPtr mptr_s hptrRel_s, .scalar sc_d hsz8_d,
          (by intro p h; injection h with h1 _; subst h1; exact hsrc_ptr),
          (by intro _ h; cases h),
          hrelC, hszC, hc_opt, hc_pre, ?_, ?_, hstate₃⟩
        · unfold evalCopyNonOverlapping; rw [ha₁]; dsimp only; rw [ha₂]; dsimp only; rw [ha₃]
        · unfold copyMiriStmtAction
          rw [EStateM.bind_eq_ok hm₁, EStateM.bind_eq_ok hm₂, EStateM.bind_eq_ok hm₃]
          exact copyAnnealCopyEval_init _ (hpt_m _) hpt.wb.miri_size hpt.wb.lt_u64 (hsrcP _)
            (copyIntrinsicPointer_fromScalarInt hrel_d hsz8_d
              (translateTy dstDecl.ty body.layouts) _) hrelC hszC
    · have ha₂ : evalOperand s.frame.locals (.copy ⟨dstIdx, []⟩) s.memory.borrows s.memory.globals
          body.layouts s.memory.callerLocals = .ok (.ptr dstPtr 8) s.frame.locals := by
        rw [evalOperand_copy_local_eq, hdst_ptr]
      have himm₂ : ∀ j, IsImmediateFrameLocal tf j → IsImmediateFrameLocal tf₂ j :=
        fun j hj => IsImmediateFrameLocal.of_values_eq hvals₂
          (IsImmediateFrameLocal.of_values_eq hvals₁ hj)
      rcases annealEvalOperand_scalar_lm3_1 hstate₂ rfl (hcountOp.mono_immediate himm₂)
          hcountInt.prim with
        ⟨m₃, msg, ha₃, hm₃⟩ | ⟨tf₃, ha₃, hm₃, _, _⟩ |
        ⟨countSc, mcount, tf₃, ha₃, hm₃, hstate₃, hrelI_c, _⟩
      · left; refine ⟨?_, m₃, msg, by
          unfold copyMiriStmtAction
          rw [EStateM.bind_eq_ok hm₁, EStateM.bind_eq_ok hm₂, EStateM.bind_eq_error hm₃]⟩
        unfold evalCopyNonOverlapping; rw [ha₁]; dsimp only; rw [ha₂]; dsimp only; rw [ha₃]
      · left; refine ⟨?_, _, _, by
          unfold copyMiriStmtAction
          rw [EStateM.bind_eq_ok hm₁, EStateM.bind_eq_ok hm₂, EStateM.bind_eq_ok hm₃]
          exact copyAnnealCopyEval_uninit_count _ _ _ _⟩
        unfold evalCopyNonOverlapping; rw [ha₁]; dsimp only; rw [ha₂]; dsimp only; rw [ha₃]
      · obtain ⟨hrelC, hszC⟩ := copyImmediateRel_of_integral hcountInt hrelI_c
        obtain ⟨hc_opt, hc_pre⟩ := copyScalarVal?_of_evalOperand_ok hcountOp ha₃
        right
        refine ⟨.ptr srcPtr 8, _, .ptr dstPtr 8, _, countSc, mcount, tf₃,
          .ptr srcPtr mptr_s hptrRel_s, .ptr dstPtr mptr_d hptrRel_d,
          (by intro p h; injection h with h1 _; subst h1; exact hsrc_ptr),
          (by intro p h; injection h with h1 _; subst h1; exact hdst_ptr),
          hrelC, hszC, hc_opt, hc_pre, ?_, ?_, hstate₃⟩
        · unfold evalCopyNonOverlapping; rw [ha₁]; dsimp only; rw [ha₂]; dsimp only; rw [ha₃]
        · unfold copyMiriStmtAction
          rw [EStateM.bind_eq_ok hm₁, EStateM.bind_eq_ok hm₂, EStateM.bind_eq_ok hm₃]
          exact copyAnnealCopyEval_init _ (hpt_m _) hpt.wb.miri_size hpt.wb.lt_u64 (hsrcP _)
            (copyIntrinsicPointer_fromPointer mptr_d (translateTy dstDecl.ty body.layouts) _)
            hrelC hszC

private theorem evalCopyNonOverlappingWithCount_of_perm_or_single
    {s : MachineState} {src dst : MirAst.Operand}
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    {srcPt : Ty} {elemBytes elemAlign : Nat}
    {srcPtr dstPtr : ProvenancePtr} {e_s e_d : AllocMapEntry}
    {decl_s decl_d : LocalDecl}
    (hopS : operandPointeeTy localDecls layouts src = some srcPt)
    (hszPt : rigidTyByteSize layouts srcPt = some elemBytes)
    (halPt : rigidTyAlignBytes layouts srcPt = some elemAlign)
    (hle : elemBytes ≤ isizeMaxBytes)
    (hpos : 0 < elemBytes)
    (halS : ptrValueAligned elemAlign (.ptr srcPtr 8) = true)
    (halD : ptrValueAligned elemAlign (.ptr dstPtr 8) = true)
    (hlookS : lookupBorrow s.memory.borrows srcPtr.tag = some e_s.toBorrowEntry)
    (hdeclS : get? localDecls e_s.localIdx = some decl_s)
    (hszS : rigidTyByteSize layouts decl_s.ty = some elemBytes)
    (hoffS : srcPtr.offsetBytes = 0)
    (hlookD : lookupBorrow s.memory.borrows dstPtr.tag = some e_d.toBorrowEntry)
    (hdeclD : get? localDecls e_d.localIdx = some decl_d)
    (hszD : rigidTyByteSize layouts decl_d.ty = some elemBytes)
    (hoffD : dstPtr.offsetBytes = 0) :
    evalCopyNonOverlappingWithCount s src dst localDecls layouts
        (.ptr srcPtr 8) (.ptr dstPtr 8) 1 s.frame.locals =
      match e_s.perm, e_d.perm with
      | .disabled, _ => MirStepNode.fail .ub
      | _, .frozen => MirStepNode.fail .ub
      | _, .disabled => MirStepNode.fail .ub
      | _, _ =>
        evalCopySingleDirect s src dst localDecls layouts srcPtr dstPtr
          e_s.toBorrowEntry e_d.toBorrowEntry s.frame.locals := by
  have hle1 : 1 * elemBytes ≤ isizeMaxBytes := by simpa using hle
  have hnz1 : ¬ (1 * elemBytes = 0) := by omega
  have hinS : srcPtr.offsetBytes + 1 * elemBytes ≤ elemBytes := by omega
  have hinD : dstPtr.offsetBytes + 1 * elemBytes ≤ elemBytes := by omega
  unfold evalCopyNonOverlappingWithCount
  rw [copyPrecheck_eq _ _ 1 hopS hszPt halPt]
  simp only [hle1, halS, halD, Bool.and_self, hnz1, ↓reduceIte]
  rw [lookupCopyBorrowChecked_root hlookS hdeclS hszS,
    lookupCopyBorrowChecked_root hlookD hdeclD hszD]
  simp only [hinS, hinD, ↓reduceIte]
  dsimp only [AllocMapEntry.toBorrowEntry]
  cases e_s.perm <;> cases e_d.perm <;>
    simp [hoffS, hoffD, Nat.beq_refl]

private theorem evalCopyNonOverlappingWithCount_dead_ub
    {s : MachineState} {src dst : MirAst.Operand}
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    {srcPt : Ty} {elemBytes elemAlign countBits : Nat}
    {srcPtr dstPtr : ProvenancePtr} {e_s e_d : AllocMapEntry}
    {decl_s decl_d : LocalDecl}
    (hopS : operandPointeeTy localDecls layouts src = some srcPt)
    (hszPt : rigidTyByteSize layouts srcPt = some elemBytes)
    (halPt : rigidTyAlignBytes layouts srcPt = some elemAlign)
    (hle : countBits * elemBytes ≤ isizeMaxBytes)
    (hpos : 0 < countBits * elemBytes)
    (halS : ptrValueAligned elemAlign (.ptr srcPtr 8) = true)
    (halD : ptrValueAligned elemAlign (.ptr dstPtr 8) = true)
    (hlookS : lookupBorrow s.memory.borrows srcPtr.tag = some e_s.toBorrowEntry)
    (hdeclS : get? localDecls e_s.localIdx = some decl_s)
    (hszS : rigidTyByteSize layouts decl_s.ty = some elemBytes)
    (hlookD : lookupBorrow s.memory.borrows dstPtr.tag = some e_d.toBorrowEntry)
    (hdeclD : get? localDecls e_d.localIdx = some decl_d)
    (hszD : rigidTyByteSize layouts decl_d.ty = some elemBytes)
    (hsingle : srcPtr.offsetBytes = 0 → dstPtr.offsetBytes = 0 → countBits = 1 →
      evalCopySingleDirect s src dst localDecls layouts srcPtr dstPtr
        e_s.toBorrowEntry e_d.toBorrowEntry s.frame.locals = MirStepNode.fail .ub) :
    evalCopyNonOverlappingWithCount s src dst localDecls layouts
        (.ptr srcPtr 8) (.ptr dstPtr 8) countBits s.frame.locals =
      MirStepNode.fail .ub := by
  have hnz : ¬ (countBits * elemBytes = 0) := by omega
  unfold evalCopyNonOverlappingWithCount
  rw [copyPrecheck_eq _ _ countBits hopS hszPt halPt]
  simp only [hle, halS, halD, Bool.and_self, hnz, ↓reduceIte]
  rw [lookupCopyBorrowChecked_root hlookS hdeclS hszS,
    lookupCopyBorrowChecked_root hlookD hdeclD hszD]
  by_cases hinS : srcPtr.offsetBytes + countBits * elemBytes ≤ elemBytes
  · by_cases hinD : dstPtr.offsetBytes + countBits * elemBytes ≤ elemBytes
    · obtain ⟨hoffS, hcnt1, _⟩ := copy_inbounds_pos_eq hpos hinS
      obtain ⟨hoffD, _, _⟩ := copy_inbounds_pos_eq hpos hinD
      simp only [hinS, hinD, ↓reduceIte]
      have hsd := hsingle hoffS hoffD hcnt1
      dsimp only [AllocMapEntry.toBorrowEntry] at hsd ⊢
      cases e_s.perm <;> cases e_d.perm <;>
        first
        | rfl
        | (simp only [hoffS, hoffD, hcnt1, Nat.beq_refl, Bool.and_self]; exact hsd)
    · simp [hinS, hinD]
  · simp [hinS]

/-- **`step_intrinsic_copyNonOverlapping_simulation_explicit` (`LM-4.2`)**:
one real step of `StatementKind.intrinsic (.copyNonOverlapping (.copy ⟨srcIdx, []⟩)
(.copy ⟨dstIdx, []⟩) countOp)` from `StateRelLM3_1` with explicit computable
post-step `copyNextAllocMap s.frame.locals allocMap dstIdx countOp elemBytes`.

Covers all non-diverging paths without assuming the outcome of either machine:
* uninitialized or dead `src`, `dst`, or `count` operands (UB in both);
* `count * size_of::<T>() > isize::MAX` overflow (UB in both);
* misaligned `src` or `dst`, including when `count = 0` or `size_of::<T>() = 0`
  (UB in both);
* aligned zero-byte copies (`count * size_of::<T>() = 0`), including ZSTs and
  provenance-free / dead / out-of-bounds pointers (no-op step preserving
  `StateRelLM3_1` in both);
* positive-byte copies with provenance-free `.scalar` pointers, dead stack
  locals, out-of-bounds offsets/counts, or same-allocation overlap (UB in both);
* positive-byte copies between distinct live initialized primitive-scalar stack
  locals with valid Tree Borrows permissions (copies the scalar & raw bytes and
  preserves `StateRelLM3_1` under `copyNextAllocMap`). -/
theorem step_intrinsic_copyNonOverlapping_simulation_explicit
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {srcIdx dstIdx : Local} {countOp : MirAst.Operand} {span : String}
    {srcDecl dstDecl : LocalDecl} {srcMut dstMut : Mutability} {pointeeTy countTy : Ty}
    {ptId : Miri.MIR.TyId} {elemBytes elemAlign : Nat}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.intrinsic (.copyNonOverlapping (.copy ⟨srcIdx, []⟩) (.copy ⟨dstIdx, []⟩) countOp),
        span⟩)
    (hsrcDecl : get? body.localDecls srcIdx = some srcDecl)
    (hsrcTy : srcDecl.ty.kind = .rawPtr srcMut pointeeTy.kind)
    (hsrcImm : ∀ tf, m.stack.frames = #[tf] → IsImmediateFrameLocal tf srcIdx)
    (hdstDecl : get? body.localDecls dstIdx = some dstDecl)
    (hdstTy : dstDecl.ty.kind = .rawPtr dstMut pointeeTy.kind)
    (hdstImm : ∀ tf, m.stack.frames = #[tf] → IsImmediateFrameLocal tf dstIdx)
    (hcountInt : IsIntegralTy countTy .usize)
    (hcountOp : ∀ tf, m.stack.frames = #[tf] → WellTypedScalarOperand body tf countOp countTy)
    (hpt : CopyPointee body.layouts pointeeTy.kind ptId elemBytes elemAlign)
    (hsrc_tgt : ∀ srcPtr e_s decl_s,
      get? s.frame.locals srcIdx = some (.init (.ptr srcPtr 8)) →
      e_s ∈ allocMap → e_s.tag = srcPtr.tag →
      get? body.localDecls e_s.localIdx = some decl_s →
      0 < elemBytes → decl_s.ty.kind = pointeeTy.kind)
    (hdst_tgt : ∀ dstPtr e_d decl_d,
      get? s.frame.locals dstIdx = some (.init (.ptr dstPtr 8)) →
      e_d ∈ allocMap → e_d.tag = dstPtr.tag →
      get? body.localDecls e_d.localIdx = some decl_d →
      0 < elemBytes → decl_d.ty.kind = pointeeTy.kind)
    (hlive_ok : ∀ srcPtr dstPtr countSc e_s e_d,
      get? s.frame.locals srcIdx = some (.init (.ptr srcPtr 8)) →
      get? s.frame.locals dstIdx = some (.init (.ptr dstPtr 8)) →
      WriteBytesScalarPreVal s.frame.locals countOp countSc →
      0 < countSc.bits * elemBytes →
      countSc.bits * elemBytes ≤ isizeMaxBytes →
      e_s ∈ allocMap → e_s.tag = srcPtr.tag →
      e_d ∈ allocMap → e_d.tag = dstPtr.tag →
      srcPtr.offsetBytes + countSc.bits * elemBytes ≤ elemBytes →
      dstPtr.offsetBytes + countSc.bits * elemBytes ≤ elemBytes →
      get? s.frame.locals e_s.localIdx ≠ some .dead →
      get? s.frame.locals e_d.localIdx ≠ some .dead →
      e_s.perm ≠ .disabled ∧
        (e_d.perm = .active ∨ e_d.perm = .reserved) ∧
        get? s.frame.locals e_s.localIdx ≠ some .uninit) :
    StepRelLM3_1 body m
      (copyNextAllocMap s.frame.locals allocMap dstIdx countOp elemBytes)
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, _, _⟩ := id hstate
  have hanneal_step : stepMirFn body s =
      evalCopyNonOverlapping s (.copy ⟨srcIdx, []⟩) (.copy ⟨dstIdx, []⟩) countOp
        body.localDecls body.layouts := by
    rw [stepMirFn_eq_of_not_other body s hcal hphase]
    simp only [hbb, hstmt]; rfl
  have mk_ub : ∀ {m' msg},
      evalCopyNonOverlapping s (.copy ⟨srcIdx, []⟩) (.copy ⟨dstIdx, []⟩) countOp
        body.localDecls body.layouts = MirStepNode.fail .ub →
      copyMiriStmtAction body srcIdx dstIdx countOp m = .error (.undefinedBehavior msg) m' →
      StepRelLM3_1 body m
        (copyNextAllocMap s.frame.locals allocMap dstIdx countOp elemBytes)
        (stepMirFn body s)
        (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
    intro m' msg ha hm
    rw [hanneal_step, ha,
      copyStep_miri_ub hframes hfr.body_eq hfr.location_eq hbb hstmt hm]
    exact .ub _ _
  rcases copyEvalSrcDst_lockstep hstate hframes hsrcDecl hsrcTy (hsrcImm tf hframes)
      hdstDecl hdstTy (hdstImm tf hframes) hcountInt (hcountOp tf hframes) hpt with
    ⟨ha_ub, m', msg, hm_ub⟩ |
    ⟨srcVal, msrcPtr, dstVal, mdstPtr, countSc, mcount, tf₃,
      hargS, hargD, hsrc_slot_fn, hdst_slot_fn, _, _, hc_opt, hc_pre,
      ha_red, hm_red, hstate₃⟩
  · exact mk_ub ha_ub hm_ub
  · obtain ⟨tf₃', hframes₃, _, _, hfr₃, _, _, _, hcaller, hbor, halloc, _⟩ := id hstate₃
    injection hframes₃ with h1; injection h1 with h2; subst h2
    have hopS := operandPointeeTy_copy_rawPtr (layouts := body.layouts) hsrcDecl hsrcTy
    have hopD := operandPointeeTy_copy_rawPtr (layouts := body.layouts) hdstDecl hdstTy
    -- 1. Size overflow precheck.
    by_cases hle : countSc.bits * elemBytes ≤ isizeMaxBytes
    · simp only [hle, ↓reduceIte] at hm_red
      have hchkS := hargS.checkAlign hstate₃ rfl hpt.align_pair
      have hchkD := hargD.checkAlign hstate₃ rfl hpt.align_pair
      -- 2. Pointer alignment precheck.
      cases hs_al : ptrValueAligned elemAlign srcVal with
      | false =>
        rw [hs_al] at hchkS; simp only [Bool.false_eq_true, ↓reduceIte] at hchkS
        have hm_err : copyMiriStmtAction body srcIdx dstIdx countOp m =
            .error (.undefinedBehavior "accessing memory with an unaligned pointer")
              { m with stack := ⟨#[tf₃]⟩ } := by
          rw [hm_red, EStateM.bind_eq_error hchkS]
        refine mk_ub ?_ hm_err
        rw [ha_red]; unfold evalCopyNonOverlappingWithCount
        rw [copyPrecheck_eq _ _ _ hopS hpt.wb.anneal_size hpt.anneal_align]
        simp [hle, hs_al]
      | true =>
        rw [hs_al] at hchkS; simp only [↓reduceIte] at hchkS
        cases hd_al : ptrValueAligned elemAlign dstVal with
        | false =>
          rw [hd_al] at hchkD; simp only [Bool.false_eq_true, ↓reduceIte] at hchkD
          have hm_err : copyMiriStmtAction body srcIdx dstIdx countOp m =
              .error (.undefinedBehavior "accessing memory with an unaligned pointer")
                { m with stack := ⟨#[tf₃]⟩ } := by
            rw [hm_red, EStateM.bind_eq_ok hchkS, EStateM.bind_eq_error hchkD]
          refine mk_ub ?_ hm_err
          rw [ha_red]; unfold evalCopyNonOverlappingWithCount
          rw [copyPrecheck_eq _ _ _ hopS hpt.wb.anneal_size hpt.anneal_align]
          simp [hle, hs_al, hd_al]
        | true =>
          rw [hd_al] at hchkD; simp only [↓reduceIte] at hchkD
          have hm_mem : copyMiriStmtAction body srcIdx dstIdx countOp m =
              annealMemCopy msrcPtr mdstPtr
                (Miri.ABI.Size.ofBytes (UInt64.ofNat (countSc.bits * elemBytes))) true
                { m with stack := ⟨#[tf₃]⟩ } := by
            rw [hm_red, EStateM.bind_eq_ok hchkS, EStateM.bind_eq_ok hchkD]
          -- 3. Zero-byte copy (`countSc.bits * elemBytes = 0`).
          by_cases hz : countSc.bits * elemBytes = 0
          · have ha_zero : evalCopyNonOverlapping s (.copy ⟨srcIdx, []⟩) (.copy ⟨dstIdx, []⟩)
                countOp body.localDecls body.layouts =
                MirStepNode.step (advanceStmt s s.frame.locals) := by
              rw [ha_red]; unfold evalCopyNonOverlappingWithCount
              rw [copyPrecheck_eq _ _ _ hopS hpt.wb.anneal_size hpt.anneal_align]
              simp [hs_al, hd_al, hz]
            have hm_zero : copyMiriStmtAction body srcIdx dstIdx countOp m =
                .ok () { stack := ⟨#[tf₃]⟩, machine := m.machine } := by
              rw [hm_mem, hz]
              exact annealMemCopy_zero msrcPtr mdstPtr { m with stack := ⟨#[tf₃]⟩ }
            have hmap_eq : copyNextAllocMap s.frame.locals allocMap dstIdx countOp elemBytes =
                allocMap := by
              unfold copyNextAllocMap writeBytesNextAllocMap
              rw [hc_opt]; simp [hz]
            rw [hanneal_step, ha_zero, hmap_eq,
              copyStep_miri_ok hframes hfr.body_eq hfr.location_eq hfr₃.location_eq hbb hstmt hm_zero]
            exact .step _ _ (StateRelLM3_1.advance_same hstate₃ rfl)
          · -- 4. Positive-byte copy (`0 < countSc.bits * elemBytes`).
            have hpos : 0 < countSc.bits * elemBytes := Nat.pos_of_ne_zero hz
            have helem_pos : 0 < elemBytes := by
              cases elemBytes with
              | zero => simp at hpos
              | succ k => omega
            cases hargS with
            | scalar sc_s _ =>
              obtain ⟨msg, herr⟩ := annealMemCopy_src_withoutProvenance_err
                (UInt64.ofNat sc_s.bits) mdstPtr hpos hle { m with stack := ⟨#[tf₃]⟩ }
              refine mk_ub ?_ (hm_mem.trans herr)
              rw [ha_red]; unfold evalCopyNonOverlappingWithCount
              rw [copyPrecheck_eq _ _ _ hopS hpt.wb.anneal_size hpt.anneal_align]
              simp [hle, hs_al, hd_al, hz]
            | ptr srcPtr p_s hptrRel_s =>
              cases hargD with
              | scalar sc_d _ =>
                obtain ⟨msg, herr⟩ := annealMemCopy_dst_withoutProvenance_err
                  p_s.withOptionalProvenance (UInt64.ofNat sc_d.bits) hpos hle
                  { m with stack := ⟨#[tf₃]⟩ }
                refine mk_ub ?_ (hm_mem.trans herr)
                rw [ha_red]; unfold evalCopyNonOverlappingWithCount
                rw [copyPrecheck_eq _ _ _ hopS hpt.wb.anneal_size hpt.anneal_align]
                simp [hle, hs_al, hd_al, hz]
              | ptr dstPtr p_d hptrRel_d =>
                have hsrc_loc_eq := hsrc_slot_fn srcPtr rfl
                have hdst_loc_eq := hdst_slot_fn dstPtr rfl
                rcases hptrRel_s with
                  ⟨srcId, srcBorTag, hprov_s, hid_s, hoff_s, haddr_s, e_s, he_s, het_s, hea_s⟩
                rcases hptrRel_d with
                  ⟨dstId, dstBorTag, hprov_d, hid_d, hoff_d, haddr_d, e_d, he_d, het_d, hea_d⟩
                have hp_s_eq : p_s.withOptionalProvenance =
                    ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr srcId + UInt64.ofNat srcPtr.offsetBytes),
                      some (.concrete srcId srcBorTag)⟩ := by
                  rcases p_s with ⟨o, pr⟩
                  dsimp only [Miri.Memory.Pointer.withOptionalProvenance] at haddr_s hprov_s ⊢
                  subst haddr_s hprov_s; rfl
                have hp_d_eq : p_d.withOptionalProvenance =
                    ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr dstId + UInt64.ofNat dstPtr.offsetBytes),
                      some (.concrete dstId dstBorTag)⟩ := by
                  rcases p_d with ⟨o, pr⟩
                  dsimp only [Miri.Memory.Pointer.withOptionalProvenance] at haddr_d hprov_d ⊢
                  subst haddr_d hprov_d; rfl
                rw [hp_s_eq, hp_d_eq] at hm_mem
                obtain ⟨decl_s, hdecl_s, hprim_s⟩ := halloc.target_decl e_s he_s
                obtain ⟨decl_d, hdecl_d, hprim_d⟩ := halloc.target_decl e_d he_d
                have hk_s := hsrc_tgt srcPtr e_s decl_s hsrc_loc_eq he_s het_s hdecl_s helem_pos
                have hk_d := hdst_tgt dstPtr e_d decl_d hdst_loc_eq he_d het_d hdecl_d helem_pos
                have hprim_pt := isPrimScalarTy_of_kind_eq hprim_s hk_s
                obtain ⟨hrig_s, htr_s, hvalid_sz⟩ :=
                  primScalar_size_of_writeBytesPointee hprim_s (hk_s.symm ▸ hpt.wb)
                obtain ⟨hrig_d, htr_d, _⟩ :=
                  primScalar_size_of_writeBytesPointee hprim_d (hk_d.symm ▸ hpt.wb)
                have hlook_s : lookupBorrow s.memory.borrows srcPtr.tag = some e_s.toBorrowEntry := by
                  rw [← het_s]; exact (halloc.borrow_sync e_s he_s).2
                have hlook_d : lookupBorrow s.memory.borrows dstPtr.tag = some e_d.toBorrowEntry := by
                  rw [← het_d]; exact (halloc.borrow_sync e_d he_d).2
                have hbase_s : m.machine.lookupBaseAddr srcId = some (annealStackBaseAddr srcId) := by
                  rw [← hea_s]; exact (halloc.base_addr_valid e_s he_s).2.2
                have hbase_d : m.machine.lookupBaseAddr dstId = some (annealStackBaseAddr dstId) := by
                  rw [← hea_d]; exact (halloc.base_addr_valid e_d he_d).2.2
                obtain ⟨slot_s, mls_s, _, _, hslot_s, hmls_s, _, hloc_s⟩ := hfr₃.lookup_local hdecl_s
                obtain ⟨slot_d, _, _, _, hslot_d, _, _, _⟩ := hfr₃.lookup_local hdecl_d
                -- 4a. Dead source local.
                by_cases hd_s : slot_s = .dead
                · subst hd_s
                  have hnone_s : m.machine.memory.live.find? (fun x => x.1 == srcId) = none := by
                    rw [← hea_s]; exact (halloc.local_alloc_sync tf₃ rfl e_s he_s).2 hslot_s
                  obtain ⟨msg, herr⟩ := annealMemCopy_src_dead_err
                    (st := { m with stack := ⟨#[tf₃]⟩ }) srcId srcBorTag srcPtr.offsetBytes _
                    hid_s hoff_s hbase_s hnone_s hpos hle
                  refine mk_ub ?_ (hm_mem.trans herr)
                  rw [ha_red]
                  exact evalCopyNonOverlappingWithCount_dead_ub hopS hpt.wb.anneal_size
                    hpt.anneal_align hle hpos hs_al hd_al hlook_s hdecl_s hrig_s hlook_d hdecl_d
                    hrig_d (fun _ _ _ => evalCopySingleDirect_dead_src_ub hcaller hslot_s)
                · -- 4b. Dead destination local.
                  by_cases hd_d : slot_d = .dead
                  · subst hd_d
                    have hnone_d : m.machine.memory.live.find? (fun x => x.1 == dstId) = none := by
                      rw [← hea_d]; exact (halloc.local_alloc_sync tf₃ rfl e_d he_d).2 hslot_d
                    obtain ⟨msg, herr⟩ := annealMemCopy_dst_dead_err
                      (st := { m with stack := ⟨#[tf₃]⟩ }) _ dstId dstBorTag dstPtr.offsetBytes
                      hid_d hoff_d hbase_d hnone_d hpos hle
                    refine mk_ub ?_ (hm_mem.trans herr)
                    rw [ha_red]
                    exact evalCopyNonOverlappingWithCount_dead_ub hopS hpt.wb.anneal_size
                      hpt.anneal_align hle hpos hs_al hd_al hlook_s hdecl_s hrig_s hlook_d hdecl_d
                      hrig_d (fun _ _ _ =>
                        evalCopySingleDirect_dead_dst_ub hcaller hprim_pt hopS hopD hslot_s hslot_d)
                  · -- 4c. Both target locals are live.
                    obtain ⟨⟨lay_s, hlay_s⟩, hsc_only_s, hshape_fn_s⟩ :=
                      (halloc.local_alloc_sync tf₃ rfl e_s he_s).1 slot_s hslot_s hd_s
                    obtain ⟨srcLA, hfind_s', _, _, hshape_s'⟩ := hshape_fn_s decl_s hdecl_s
                    have hfind_s : m.machine.memory.live.find? (fun x => x.1 == srcId) =
                        some (srcId, srcLA) := by rw [← hea_s]; exact hfind_s'
                    have hshape_s : StackScalarAllocShape (translateSizeBytes elemBytes)
                        srcLA.allocation := htr_s ▸ hshape_s'
                    obtain ⟨_, _, hshape_fn_d⟩ :=
                      (halloc.local_alloc_sync tf₃ rfl e_d he_d).1 slot_d hslot_d hd_d
                    obtain ⟨dstLA, hfind_d', hkind_d, halign_d, hshape_d'⟩ :=
                      hshape_fn_d decl_d hdecl_d
                    have hfind_d : m.machine.memory.live.find? (fun x => x.1 == dstId) =
                        some (dstId, dstLA) := by rw [← hea_d]; exact hfind_d'
                    have hshape_d : StackScalarAllocShape (translateSizeBytes elemBytes)
                        dstLA.allocation := htr_d ▸ hshape_d'
                    have hts_nat : (translateSizeBytes elemBytes).bytes.toNat = elemBytes := by
                      rcases hvalid_sz with rfl | rfl | rfl | rfl | rfl <;> rfl
                    have hsz_la_s : srcLA.allocation.byteSize.bytes.toNat = elemBytes := by
                      rw [hshape_s.byteSize_eq, hts_nat]
                    have hsz_la_d : dstLA.allocation.byteSize.bytes.toNat = elemBytes := by
                      rw [hshape_d.byteSize_eq, hts_nat]
                    -- 4d. Source OOB.
                    by_cases hinS : srcPtr.offsetBytes + countSc.bits * elemBytes ≤ elemBytes
                    · -- 4e. Destination OOB.
                      by_cases hinD : dstPtr.offsetBytes + countSc.bits * elemBytes ≤ elemBytes
                      · -- 4f. Both in-bounds (`offsetBytes = 0`, `countSc.bits = 1`).
                        obtain ⟨hoff0_s, hcnt1, _⟩ := copy_inbounds_pos_eq hpos hinS
                        obtain ⟨hoff0_d, _, _⟩ := copy_inbounds_pos_eq hpos hinD
                        have hlive_s_ne : get? s.frame.locals e_s.localIdx ≠ some .dead := by
                          rw [hslot_s]; intro h; injection h with h; exact hd_s h
                        have hlive_d_ne : get? s.frame.locals e_d.localIdx ≠ some .dead := by
                          rw [hslot_d]; intro h; injection h with h; exact hd_d h
                        obtain ⟨hperm_s, hperm_d, hnot_un_s⟩ := hlive_ok srcPtr dstPtr countSc
                          e_s e_d hsrc_loc_eq hdst_loc_eq hc_pre hpos hle he_s het_s he_d het_d
                          hinS hinD hlive_s_ne hlive_d_ne
                        -- `slot_s` is initialized (`slot_s = .init (.scalar sc_s)`).
                        have hs_init : ∃ sc_s, slot_s = .init (.scalar sc_s) := by
                          cases hs : slot_s with
                          | dead => exact absurd hs hd_s
                          | uninit => exact absurd (hslot_s.trans (congrArg some hs)) hnot_un_s
                          | init v =>
                            obtain ⟨sc_s, rfl⟩ := hsc_only_s v hs
                            exact ⟨sc_s, rfl⟩
                        obtain ⟨sc_s, rfl⟩ := hs_init
                        -- Extract `msc_s` and `readScalar` via `indirect_stackAllocPlace_spec`.
                        have hmls_s_eq : mls_s = ⟨.live (.indirect (stackAllocPlace e_s.allocId)), lay_s⟩ := by
                          rw [hlay_s] at hmls_s; exact Option.some.inj hmls_s.symm
                        have hnz_sz_s : (translateTy decl_s.ty body.layouts).layout.size ≠
                            Miri.ABI.Size.ZERO := by
                          rw [htr_s]; intro h
                          have := congrArg (fun z : Miri.ABI.Size => z.bytes.toNat) h
                          rw [hts_nat] at this; change elemBytes = 0 at this; omega
                        obtain ⟨_, hsc_spec⟩ := hloc_s.indirect_stackAllocPlace_spec hmls_s_eq
                          (halloc.base_addr_valid e_s he_s).2.2 hfind_s'
                          (halloc.live_key_unique e_s he_s) hnz_sz_s
                        obtain ⟨hsz_sc_eq, hbool_s, hchar_s, msc_s, hrel_sc, hread_s⟩ :=
                          hsc_spec sc_s rfl
                        have hsc_bytes : sc_s.sizeBytes = elemBytes := by
                          have h := htr_s.symm.trans hsz_sc_eq
                          have h1 : (translateSizeBytes sc_s.sizeBytes).bytes.toNat = sc_s.sizeBytes := by
                            rcases hrel_sc.validBytes with h0 | h0 | h0 | h0 | h0 <;> (rw [h0]; rfl)
                          have := congrArg (fun z : Miri.ABI.Size => z.bytes.toNat) h
                          omega
                        rw [htr_s] at hread_s
                        have hle1 : elemBytes ≤ isizeMaxBytes := by simpa [hcnt1] using hle
                        have ha_step1 : evalCopyNonOverlappingWithCount s (.copy ⟨srcIdx, []⟩)
                            (.copy ⟨dstIdx, []⟩) body.localDecls body.layouts
                            (.ptr srcPtr 8) (.ptr dstPtr 8) countSc.bits s.frame.locals =
                            evalCopySingleDirect s (.copy ⟨srcIdx, []⟩) (.copy ⟨dstIdx, []⟩)
                              body.localDecls body.layouts srcPtr dstPtr
                              e_s.toBorrowEntry e_d.toBorrowEntry s.frame.locals := by
                          rw [hcnt1, evalCopyNonOverlappingWithCount_of_perm_or_single hopS
                            hpt.wb.anneal_size hpt.anneal_align hle1 helem_pos hs_al hd_al
                            hlook_s hdecl_s hrig_s hoff0_s hlook_d hdecl_d hrig_d hoff0_d]
                          rcases hperm_d with hp_d | hp_d <;> rw [hp_d] <;>
                            (cases hp_s : e_s.perm <;> simp_all)
                        -- 4g. Same allocation (overlap) vs. distinct allocations.
                        by_cases hsame : e_s.localIdx = e_d.localIdx
                        · have heq_id : srcId = dstId := by
                            rw [← hea_s, ← hea_d]
                            exact halloc.local_to_alloc_unique e_s he_s e_d he_d hsame
                          obtain ⟨alloc', hcopy_err⟩ :=
                            hshape_s.copyRepeatedly_init_overlap_err hvalid_sz hread_s
                          obtain ⟨st', herr⟩ := annealMemCopy_live_overlap_err
                            (st := { m with stack := ⟨#[tf₃]⟩ }) hvalid_sz srcId srcBorTag dstBorTag
                            srcLA alloc' hid_s hbase_s hfind_s hsz_la_s hcopy_err
                          have hm_err : copyMiriStmtAction body srcIdx dstIdx countOp m =
                              .error (.undefinedBehavior "copy_nonoverlapping called on overlapping ranges")
                                st' := by
                            rw [hm_mem, hcnt1, Nat.one_mul, hoff0_s, hoff0_d, ← heq_id]
                            exact herr
                          refine mk_ub ?_ hm_err
                          rw [ha_red, ha_step1, evalCopySingleDirect_overlap_ub hsame]
                        · -- Distinct live allocations (`e_s.localIdx ≠ e_d.localIdx`).
                          have hne_id : srcId ≠ e_d.allocId := by
                            intro hid
                            apply hsame
                            exact halloc.alloc_to_local_injective e_s he_s e_d he_d
                              (hea_s.trans hid)
                          have hne_tag : srcPtr.tag ≠ dstPtr.tag := by
                            intro htag
                            have hl1 := copyLookupAllocMapByTag_of_mem_nodup halloc.tags_nodup he_s het_s
                            have hl2 := copyLookupAllocMapByTag_of_mem_nodup halloc.tags_nodup he_d
                              (het_d.trans htag.symm)
                            rw [hl1] at hl2; injection hl2 with heq; exact hsame (congrArg _ heq)
                          have hid_d' : e_d.allocId.value.toNat < 2 ^ 32 := hea_d.symm ▸ hid_d
                          have hbase_d' : m.machine.lookupBaseAddr e_d.allocId =
                              some (annealStackBaseAddr e_d.allocId) :=
                            (halloc.base_addr_valid e_d he_d).2.2
                          obtain ⟨alloc', hcopy_ok, halign_a', hshape_a', hinit_a', hread_a'⟩ :=
                            hshape_s.copyRepeatedly_init_distinct hvalid_sz hshape_d hread_s
                          have hm_copy := annealMemCopy_live_distinct_ok
                            (st := { m with stack := ⟨#[tf₃]⟩ }) hvalid_sz srcId srcBorTag srcLA
                            e_d.allocId dstBorTag dstLA alloc' hne_id hid_s hbase_s hfind_s hsz_la_s
                            hid_d' hbase_d' hfind_d' hsz_la_d hcopy_ok
                          have hm_act : copyMiriStmtAction body srcIdx dstIdx countOp m =
                              .ok () { stack := ⟨#[tf₃]⟩, machine := { m.machine with
                                memory := { m.machine.memory with
                                  live := (m.machine.memory.live.filter (fun x => x.1 != e_d.allocId)).push
                                    (e_d.allocId, ⟨dstLA.kind, alloc'⟩) } } } := by
                            rw [hm_mem, hcnt1, Nat.one_mul, hoff0_s, hoff0_d, ← hea_d]
                            exact hm_copy
                          have ha_ok : evalCopyNonOverlapping s (.copy ⟨srcIdx, []⟩)
                              (.copy ⟨dstIdx, []⟩) countOp body.localDecls body.layouts =
                              MirStepNode.step
                                (advanceStmt s (s.frame.locals.set e_d.localIdx (.init (.scalar sc_s)))
                                  { s.memory with
                                    borrows := (updateAllocMapOnWrite allocMap e_d.localIdx
                                      (some dstPtr.tag)).map AllocMapEntry.toBorrowEntry }) := by
                            rw [ha_red, ha_step1,
                              evalCopySingleDirect_distinct_ok hprim_pt hopS hopD hne_tag hsame
                                hslot_s hslot_d hd_d,
                              hbor, copyInvalidateConflictingBorrows_eq_map_updateAllocMapOnWrite]
                          have hmap_eq : copyNextAllocMap s.frame.locals allocMap dstIdx countOp
                              elemBytes =
                              updateAllocMapOnWrite allocMap e_d.localIdx (some dstPtr.tag) := by
                            unfold copyNextAllocMap writeBytesNextAllocMap
                            rw [hc_opt]
                            simp only [hz, ↓reduceIte, hdst_loc_eq,
                              copyLookupAllocMapByTag_of_mem_nodup halloc.tags_nodup he_d het_d]
                          have hkind_eq : decl_d.ty.kind = decl_s.ty.kind := hk_d.trans hk_s.symm
                          have hbool_d : decl_d.ty.kind = .bool →
                              sc_s.sizeBytes = 1 ∧ (sc_s.bits = 0 ∨ sc_s.bits = 1) :=
                            fun h => hbool_s (hkind_eq ▸ h)
                          have hchar_d : decl_d.ty.kind = .char →
                              sc_s.sizeBytes = 4 ∧ isValidCharCode sc_s.bits = true :=
                            fun h => hchar_s (hkind_eq ▸ h)
                          have hsz_tgt_d : (translateTy decl_d.ty body.layouts).layout.size =
                              translateSizeBytes sc_s.sizeBytes := by
                            rw [htr_d, hsc_bytes]
                          have hpost := StateRelLM3_1.advance_write_deref_scalar hstate₃ rfl
                            (fun x => x.updateOnWrite e_d.localIdx (some dstPtr.tag))
                            (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
                            he_d hdecl_d hprim_d hslot_d hd_d hfind_d' hkind_d halign_d
                            hrel_sc hsz_tgt_d hbool_d hchar_d halign_a'
                            (hsc_bytes.symm ▸ hshape_a')
                            (hsc_bytes.symm ▸ hinit_a')
                            (hsc_bytes.symm ▸ hread_a')
                          rw [hanneal_step, ha_ok, hmap_eq,
                            copyStep_miri_ok hframes hfr.body_eq hfr.location_eq hfr₃.location_eq
                              hbb hstmt hm_act]
                          exact .step _ _ hpost
                      · -- Destination OOB (`elemBytes < dstPtr.offsetBytes + total`).
                        have hoobD : dstLA.allocation.byteSize.bytes.toNat <
                            dstPtr.offsetBytes + countSc.bits * elemBytes := by omega
                        obtain ⟨msg, herr⟩ := annealMemCopy_dst_oob_err
                          (st := { m with stack := ⟨#[tf₃]⟩ })
                          ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr srcId + UInt64.ofNat srcPtr.offsetBytes),
                            some (.concrete srcId srcBorTag)⟩
                          dstId dstBorTag dstPtr.offsetBytes
                          dstLA hid_d hoff_d hbase_d hfind_d hpos hle hoobD
                        have hm_err : copyMiriStmtAction body srcIdx dstIdx countOp m =
                            .error (.undefinedBehavior msg) { m with stack := ⟨#[tf₃]⟩ } := by
                          rw [hm_mem]; exact herr
                        refine mk_ub ?_ hm_err
                        rw [ha_red]; unfold evalCopyNonOverlappingWithCount
                        rw [copyPrecheck_eq _ _ _ hopS hpt.wb.anneal_size hpt.anneal_align]
                        simp only [hle, hs_al, hd_al, Bool.and_self, hz, ↓reduceIte]
                        rw [lookupCopyBorrowChecked_root hlook_s hdecl_s hrig_s,
                          lookupCopyBorrowChecked_root hlook_d hdecl_d hrig_d]
                        simp only [hinS, hinD, ↓reduceIte]
                    · -- Source OOB (`elemBytes < srcPtr.offsetBytes + total`).
                      have hoobS : srcLA.allocation.byteSize.bytes.toNat <
                          srcPtr.offsetBytes + countSc.bits * elemBytes := by omega
                      obtain ⟨msg, herr⟩ := annealMemCopy_src_oob_err
                        (st := { m with stack := ⟨#[tf₃]⟩ }) srcId srcBorTag srcPtr.offsetBytes
                        srcLA
                        ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr dstId + UInt64.ofNat dstPtr.offsetBytes),
                          some (.concrete dstId dstBorTag)⟩
                        hid_s hoff_s hbase_s hfind_s hpos hle hoobS
                      have hm_err : copyMiriStmtAction body srcIdx dstIdx countOp m =
                          .error (.undefinedBehavior msg) { m with stack := ⟨#[tf₃]⟩ } := by
                        rw [hm_mem]; exact herr
                      refine mk_ub ?_ hm_err
                      rw [ha_red]; unfold evalCopyNonOverlappingWithCount
                      rw [copyPrecheck_eq _ _ _ hopS hpt.wb.anneal_size hpt.anneal_align]
                      simp only [hle, hs_al, hd_al, Bool.and_self, hz, ↓reduceIte]
                      rw [lookupCopyBorrowChecked_root hlook_s hdecl_s hrig_s]
                      simp only [hinS, ↓reduceIte]
    · -- Size overflow (`¬ countSc.bits * elemBytes ≤ isizeMaxBytes`).
      simp only [hle, ↓reduceIte] at hm_red
      refine mk_ub ?_ hm_red
      rw [ha_red]; unfold evalCopyNonOverlappingWithCount
      rw [copyPrecheck_eq _ _ _ hopS hpt.wb.anneal_size hpt.anneal_align]
      simp [hle]

/-- **`step_intrinsic_copyNonOverlapping_simulation` (`LM-4.2`)**: existential
`allocMap'` packaging of `step_intrinsic_copyNonOverlapping_simulation_explicit`
for `StatementKind.intrinsic (.copyNonOverlapping (.copy ⟨srcIdx, []⟩)
(.copy ⟨dstIdx, []⟩) countOp)`. -/
theorem step_intrinsic_copyNonOverlapping_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {srcIdx dstIdx : Local} {countOp : MirAst.Operand} {span : String}
    {srcDecl dstDecl : LocalDecl} {srcMut dstMut : Mutability} {pointeeTy countTy : Ty}
    {ptId : Miri.MIR.TyId} {elemBytes elemAlign : Nat}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.intrinsic (.copyNonOverlapping (.copy ⟨srcIdx, []⟩) (.copy ⟨dstIdx, []⟩) countOp),
        span⟩)
    (hsrcDecl : get? body.localDecls srcIdx = some srcDecl)
    (hsrcTy : srcDecl.ty.kind = .rawPtr srcMut pointeeTy.kind)
    (hsrcImm : ∀ tf, m.stack.frames = #[tf] → IsImmediateFrameLocal tf srcIdx)
    (hdstDecl : get? body.localDecls dstIdx = some dstDecl)
    (hdstTy : dstDecl.ty.kind = .rawPtr dstMut pointeeTy.kind)
    (hdstImm : ∀ tf, m.stack.frames = #[tf] → IsImmediateFrameLocal tf dstIdx)
    (hcountInt : IsIntegralTy countTy .usize)
    (hcountOp : ∀ tf, m.stack.frames = #[tf] → WellTypedScalarOperand body tf countOp countTy)
    (hpt : CopyPointee body.layouts pointeeTy.kind ptId elemBytes elemAlign)
    (hsrc_tgt : ∀ srcPtr e_s decl_s,
      get? s.frame.locals srcIdx = some (.init (.ptr srcPtr 8)) →
      e_s ∈ allocMap → e_s.tag = srcPtr.tag →
      get? body.localDecls e_s.localIdx = some decl_s →
      0 < elemBytes → decl_s.ty.kind = pointeeTy.kind)
    (hdst_tgt : ∀ dstPtr e_d decl_d,
      get? s.frame.locals dstIdx = some (.init (.ptr dstPtr 8)) →
      e_d ∈ allocMap → e_d.tag = dstPtr.tag →
      get? body.localDecls e_d.localIdx = some decl_d →
      0 < elemBytes → decl_d.ty.kind = pointeeTy.kind)
    (hlive_ok : ∀ srcPtr dstPtr countSc e_s e_d,
      get? s.frame.locals srcIdx = some (.init (.ptr srcPtr 8)) →
      get? s.frame.locals dstIdx = some (.init (.ptr dstPtr 8)) →
      WriteBytesScalarPreVal s.frame.locals countOp countSc →
      0 < countSc.bits * elemBytes →
      countSc.bits * elemBytes ≤ isizeMaxBytes →
      e_s ∈ allocMap → e_s.tag = srcPtr.tag →
      e_d ∈ allocMap → e_d.tag = dstPtr.tag →
      srcPtr.offsetBytes + countSc.bits * elemBytes ≤ elemBytes →
      dstPtr.offsetBytes + countSc.bits * elemBytes ≤ elemBytes →
      get? s.frame.locals e_s.localIdx ≠ some .dead →
      get? s.frame.locals e_d.localIdx ≠ some .dead →
      e_s.perm ≠ .disabled ∧
        (e_d.perm = .active ∨ e_d.perm = .reserved) ∧
        get? s.frame.locals e_s.localIdx ≠ some .uninit) :
    ∃ allocMap',
      StepRelLM3_1 body m allocMap'
        (stepMirFn body s)
        (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  ⟨copyNextAllocMap s.frame.locals allocMap dstIdx countOp elemBytes,
    step_intrinsic_copyNonOverlapping_simulation_explicit hstate hphase hbb hstmt
      hsrcDecl hsrcTy hsrcImm hdstDecl hdstTy hdstImm hcountInt hcountOp hpt
      hsrc_tgt hdst_tgt hlive_ok⟩

private theorem ptrValueAligned_of_offset_zero {elemAlign : Nat}
    (hal : ValidCopyAlign elemAlign) {p : ProvenancePtr} (hoff : p.offsetBytes = 0) :
    ptrValueAligned elemAlign (.ptr p 8) = true := by
  dsimp only [ptrValueAligned]
  rw [hoff]
  rcases hal with rfl | rfl | rfl | rfl | rfl <;> rfl

/-- Shared reduction for the `CopyNonOverlapping` divergence theorems (`count = 1`
at root offset `0` on live primitive-scalar stack locals): reduces Anneal's
`stepMirFn` to the Tree Borrows permission table + `evalCopySingleDirect` and
proves `lean-miri`'s `Step.step` returns `(m', .ok true)` whenever `slot_s = .uninit`
or `e_s.localIdx ≠ e_d.localIdx`. -/
private theorem copyDivergence_core
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {srcIdx dstIdx : Local} {countOp : MirAst.Operand} {span : String}
    {srcDecl dstDecl : LocalDecl} {srcMut dstMut : Mutability} {pointeeTy countTy : Ty}
    {ptId : Miri.MIR.TyId} {elemBytes elemAlign : Nat}
    {srcPtr dstPtr : ProvenancePtr} {countSc : MirAst.ScalarInt}
    {e_s e_d : AllocMapEntry}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.intrinsic (.copyNonOverlapping (.copy ⟨srcIdx, []⟩) (.copy ⟨dstIdx, []⟩) countOp),
        span⟩)
    (hsrcDecl : get? body.localDecls srcIdx = some srcDecl)
    (hsrcTy : srcDecl.ty.kind = .rawPtr srcMut pointeeTy.kind)
    (hsrcImm : ∀ tf, m.stack.frames = #[tf] → IsImmediateFrameLocal tf srcIdx)
    (hdstDecl : get? body.localDecls dstIdx = some dstDecl)
    (hdstTy : dstDecl.ty.kind = .rawPtr dstMut pointeeTy.kind)
    (hdstImm : ∀ tf, m.stack.frames = #[tf] → IsImmediateFrameLocal tf dstIdx)
    (hcountInt : IsIntegralTy countTy .usize)
    (hcountOp : ∀ tf, m.stack.frames = #[tf] → WellTypedScalarOperand body tf countOp countTy)
    (hpt : CopyPointee body.layouts pointeeTy.kind ptId elemBytes elemAlign)
    (hsrc_val : get? s.frame.locals srcIdx = some (.init (.ptr srcPtr 8)))
    (hdst_val : get? s.frame.locals dstIdx = some (.init (.ptr dstPtr 8)))
    (hoff0_s : srcPtr.offsetBytes = 0)
    (hoff0_d : dstPtr.offsetBytes = 0)
    (hcnt_pre : WriteBytesScalarPreVal s.frame.locals countOp countSc)
    (hcnt1 : countSc.bits = 1)
    (he_s : e_s ∈ allocMap) (het_s : e_s.tag = srcPtr.tag)
    (he_d : e_d ∈ allocMap) (het_d : e_d.tag = dstPtr.tag)
    (hsrc_tgt : ∀ decl_s, get? body.localDecls e_s.localIdx = some decl_s →
      decl_s.ty.kind = pointeeTy.kind)
    (hdst_tgt : ∀ decl_d, get? body.localDecls e_d.localIdx = some decl_d →
      decl_d.ty.kind = pointeeTy.kind)
    (hsrc_live : get? s.frame.locals e_s.localIdx ≠ some .dead)
    (hdst_live : get? s.frame.locals e_d.localIdx ≠ some .dead)
    (hun_or_dist : get? s.frame.locals e_s.localIdx = some .uninit ∨
      e_s.localIdx ≠ e_d.localIdx) :
    stepMirFn body s =
      (match e_s.perm, e_d.perm with
      | .disabled, _ => MirStepNode.fail .ub
      | _, .frozen => MirStepNode.fail .ub
      | _, .disabled => MirStepNode.fail .ub
      | _, _ =>
        evalCopySingleDirect s (.copy ⟨srcIdx, []⟩) (.copy ⟨dstIdx, []⟩)
          body.localDecls body.layouts srcPtr dstPtr
          e_s.toBorrowEntry e_d.toBorrowEntry s.frame.locals) ∧
    ∃ m',
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .ok true) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, _, _⟩ := id hstate
  have hanneal_step : stepMirFn body s =
      evalCopyNonOverlapping s (.copy ⟨srcIdx, []⟩) (.copy ⟨dstIdx, []⟩) countOp
        body.localDecls body.layouts := by
    rw [stepMirFn_eq_of_not_other body s hcal hphase]
    simp only [hbb, hstmt]; rfl
  have ha₁ : evalOperand s.frame.locals (.copy ⟨srcIdx, []⟩) s.memory.borrows s.memory.globals
      body.layouts s.memory.callerLocals = .ok (.ptr srcPtr 8) s.frame.locals := by
    rw [evalOperand_copy_local_eq, hsrc_val]
  have ha₂ : evalOperand s.frame.locals (.copy ⟨dstIdx, []⟩) s.memory.borrows s.memory.globals
      body.layouts s.memory.callerLocals = .ok (.ptr dstPtr 8) s.frame.locals := by
    rw [evalOperand_copy_local_eq, hdst_val]
  have ha₃ : evalOperand s.frame.locals countOp s.memory.borrows s.memory.globals
      body.layouts s.memory.callerLocals = .ok (.scalar countSc) s.frame.locals := by
    rcases hcnt_pre with ⟨cc, rfl, hv⟩ | ⟨idx, rfl, hsl⟩
    · unfold evalOperand; dsimp only; rw [hv]; rfl
    · rw [evalOperand_copy_local_eq, hsl]
  -- Evaluate `src`, `dst`, and `countOp` directly against the known `.init` slots.
  rcases annealEvalOperand_rawPtr_lm3_1 hstate hframes hsrcDecl hsrcTy (hsrcImm tf hframes) with
    ⟨hd, _⟩ | ⟨_, hun, _⟩ | ⟨_, _, _, hsc, _⟩ |
    ⟨srcPtr', mptr_s, tf₁, hsrc_ptr, hptrRel_s, hm₁, hstate₁, hvals₁⟩
  · rw [hsrc_val] at hd; cases hd
  · rw [hsrc_val] at hun; cases hun
  · rw [hsrc_val] at hsc; cases hsc
  · rw [hsrc_val] at hsrc_ptr
    cases hsrc_ptr
    rcases annealEvalOperand_rawPtr_lm3_1 hstate₁ rfl hdstDecl hdstTy
        (IsImmediateFrameLocal.of_values_eq hvals₁ (hdstImm tf hframes)) with
      ⟨hd, _⟩ | ⟨_, hun, _⟩ | ⟨_, _, _, hsc, _⟩ |
      ⟨dstPtr', mptr_d, tf₂, hdst_ptr, hptrRel_d, hm₂, hstate₂, hvals₂⟩
    · rw [hdst_val] at hd; cases hd
    · rw [hdst_val] at hun; cases hun
    · rw [hdst_val] at hsc; cases hsc
    · rw [hdst_val] at hdst_ptr
      cases hdst_ptr
      have himm₂ : ∀ j, IsImmediateFrameLocal tf j → IsImmediateFrameLocal tf₂ j :=
        fun j hj => IsImmediateFrameLocal.of_values_eq hvals₂
          (IsImmediateFrameLocal.of_values_eq hvals₁ hj)
      rcases annealEvalOperand_scalar_lm3_1 hstate₂ rfl ((hcountOp tf hframes).mono_immediate himm₂)
          hcountInt.prim with
        ⟨_, _, ha₃', _⟩ | ⟨_, ha₃', _⟩ |
        ⟨countSc', mcount, tf₃, ha₃', hm₃, hstate₃, hrelI_c, _⟩
      · rw [ha₃] at ha₃'; cases ha₃'
      · rw [ha₃] at ha₃'; cases ha₃'
      · rw [ha₃] at ha₃'
        cases ha₃'
        obtain ⟨tf₃', hframes₃, _, _, hfr₃, _, _, _, _, _, halloc, _⟩ := id hstate₃
        cases hframes₃
        obtain ⟨hrelC, hszC⟩ := copyImmediateRel_of_integral hcountInt hrelI_c
        obtain ⟨decl_s, hdecl_s, hprim_s⟩ := halloc.target_decl e_s he_s
        obtain ⟨decl_d, hdecl_d, hprim_d⟩ := halloc.target_decl e_d he_d
        obtain ⟨hrig_s, htr_s, hvalid_sz⟩ :=
          primScalar_size_of_writeBytesPointee hprim_s ((hsrc_tgt decl_s hdecl_s).symm ▸ hpt.wb)
        obtain ⟨hrig_d, htr_d, _⟩ :=
          primScalar_size_of_writeBytesPointee hprim_d ((hdst_tgt decl_d hdecl_d).symm ▸ hpt.wb)
        have helem_pos : 0 < elemBytes := by
          rcases hvalid_sz with rfl | rfl | rfl | rfl | rfl <;> omega
        have hle1 : elemBytes ≤ isizeMaxBytes := by
          unfold isizeMaxBytes; rcases hvalid_sz with rfl | rfl | rfl | rfl | rfl <;> omega
        have hle : countSc.bits * elemBytes ≤ isizeMaxBytes := by simpa [hcnt1] using hle1
        have halS := ptrValueAligned_of_offset_zero hpt.align_pair.validCopyAlign hoff0_s
        have halD := ptrValueAligned_of_offset_zero hpt.align_pair.validCopyAlign hoff0_d
        have hlook_s : lookupBorrow s.memory.borrows srcPtr.tag = some e_s.toBorrowEntry := by
          rw [← het_s]; exact (halloc.borrow_sync e_s he_s).2
        have hlook_d : lookupBorrow s.memory.borrows dstPtr.tag = some e_d.toBorrowEntry := by
          rw [← het_d]; exact (halloc.borrow_sync e_d he_d).2
        have hopS := operandPointeeTy_copy_rawPtr (layouts := body.layouts) hsrcDecl hsrcTy
        -- Anneal side reduction.
        have ha_eq : stepMirFn body s =
            match e_s.perm, e_d.perm with
            | .disabled, _ => MirStepNode.fail .ub
            | _, .frozen => MirStepNode.fail .ub
            | _, .disabled => MirStepNode.fail .ub
            | _, _ =>
              evalCopySingleDirect s (.copy ⟨srcIdx, []⟩) (.copy ⟨dstIdx, []⟩)
                body.localDecls body.layouts srcPtr dstPtr
                e_s.toBorrowEntry e_d.toBorrowEntry s.frame.locals := by
          rw [hanneal_step]
          unfold evalCopyNonOverlapping
          rw [ha₁]; dsimp only; rw [ha₂]; dsimp only; rw [ha₃]; dsimp only
          rw [hcnt1]
          exact evalCopyNonOverlappingWithCount_of_perm_or_single hopS
            hpt.wb.anneal_size hpt.anneal_align hle1 helem_pos halS halD
            hlook_s hdecl_s hrig_s hoff0_s hlook_d hdecl_d hrig_d hoff0_d
        refine ⟨ha_eq, ?_⟩
        -- `lean-miri` side reduction.
        have hchkS := annealCheckPtrAlign_stackPtr hstate₃ rfl hpt.align_pair hptrRel_s
        rw [halS] at hchkS; simp only [↓reduceIte] at hchkS
        have hchkD := annealCheckPtrAlign_stackPtr hstate₃ rfl hpt.align_pair hptrRel_d
        rw [halD] at hchkD; simp only [↓reduceIte] at hchkD
        have hpt_m := annealPointeeTypeOf_rawPtr (ly := body.layouts) hsrcTy hpt.wb.encoded_eq
        have hm_ev := copyAnnealCopyEval_init (countLay := translateTy countTy body.layouts)
          { m with stack := ⟨#[tf₃]⟩ }
          (hpt_m _) hpt.wb.miri_size hpt.wb.lt_u64
          (copyIntrinsicPointer_fromPointer mptr_s (translateTy srcDecl.ty body.layouts) _)
          (copyIntrinsicPointer_fromPointer mptr_d (translateTy dstDecl.ty body.layouts) _)
          hrelC hszC
        simp only [hle, ↓reduceIte] at hm_ev
        have hm_mem : copyMiriStmtAction body srcIdx dstIdx countOp m =
            annealMemCopy mptr_s.withOptionalProvenance mptr_d.withOptionalProvenance
              (Miri.ABI.Size.ofBytes (UInt64.ofNat elemBytes)) true
              { m with stack := ⟨#[tf₃]⟩ } := by
          unfold copyMiriStmtAction
          rw [EStateM.bind_eq_ok hm₁, EStateM.bind_eq_ok hm₂, EStateM.bind_eq_ok hm₃,
            hm_ev, EStateM.bind_eq_ok hchkS, EStateM.bind_eq_ok hchkD, hcnt1, Nat.one_mul]
        -- Unpack `PtrRel` and identify `e_s' = e_s` and `e_d' = e_d` by `tags_nodup`.
        rcases hptrRel_s with
          ⟨srcId, srcBorTag, hprov_s, hid_s, _, haddr_s, e_s', he_s', het_s', hea_s'⟩
        rcases hptrRel_d with
          ⟨dstId, dstBorTag, hprov_d, hid_d, _, haddr_d, e_d', he_d', het_d', hea_d'⟩
        have hes_eq : e_s' = e_s := by
          have hl1 := copyLookupAllocMapByTag_of_mem_nodup halloc.tags_nodup he_s' het_s'
          have hl2 := copyLookupAllocMapByTag_of_mem_nodup halloc.tags_nodup he_s het_s
          exact Option.some.inj (hl1.symm.trans hl2)
        have hed_eq : e_d' = e_d := by
          have hl1 := copyLookupAllocMapByTag_of_mem_nodup halloc.tags_nodup he_d' het_d'
          have hl2 := copyLookupAllocMapByTag_of_mem_nodup halloc.tags_nodup he_d het_d
          exact Option.some.inj (hl1.symm.trans hl2)
        rw [hes_eq] at hea_s'
        rw [hed_eq] at hea_d'
        have hp_s_eq : mptr_s.withOptionalProvenance =
            ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr srcId + UInt64.ofNat 0),
              some (.concrete srcId srcBorTag)⟩ := by
          rcases mptr_s with ⟨o, pr⟩
          dsimp only [Miri.Memory.Pointer.withOptionalProvenance] at haddr_s hprov_s ⊢
          subst haddr_s hprov_s; rw [hoff0_s]
        have hp_d_eq : mptr_d.withOptionalProvenance =
            ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr dstId + UInt64.ofNat 0),
              some (.concrete dstId dstBorTag)⟩ := by
          rcases mptr_d with ⟨o, pr⟩
          dsimp only [Miri.Memory.Pointer.withOptionalProvenance] at haddr_d hprov_d ⊢
          subst haddr_d hprov_d; rw [hoff0_d]
        rw [hp_s_eq, hp_d_eq] at hm_mem
        have hbase_s : m.machine.lookupBaseAddr srcId = some (annealStackBaseAddr srcId) := by
          rw [← hea_s']; exact (halloc.base_addr_valid e_s he_s).2.2
        have hbase_d : m.machine.lookupBaseAddr dstId = some (annealStackBaseAddr dstId) := by
          rw [← hea_d']; exact (halloc.base_addr_valid e_d he_d).2.2
        obtain ⟨slot_s, mls_s, _, _, hslot_s, hmls_s, _, hloc_s⟩ := hfr₃.lookup_local hdecl_s
        obtain ⟨slot_d, _, _, _, hslot_d, _, _, _⟩ := hfr₃.lookup_local hdecl_d
        have hd_s : slot_s ≠ .dead := by
          intro h; exact hsrc_live (hslot_s.trans (congrArg some h))
        have hd_d : slot_d ≠ .dead := by
          intro h; exact hdst_live (hslot_d.trans (congrArg some h))
        obtain ⟨⟨lay_s, hlay_s⟩, hsc_only_s, hshape_fn_s⟩ :=
          (halloc.local_alloc_sync tf₃ rfl e_s he_s).1 slot_s hslot_s hd_s
        obtain ⟨srcLA, hfind_s', _, _, hshape_s'⟩ := hshape_fn_s decl_s hdecl_s
        have hfind_s : m.machine.memory.live.find? (fun x => x.1 == srcId) =
            some (srcId, srcLA) := by rw [← hea_s']; exact hfind_s'
        have hshape_s : StackScalarAllocShape (translateSizeBytes elemBytes)
            srcLA.allocation := htr_s ▸ hshape_s'
        obtain ⟨_, _, hshape_fn_d⟩ :=
          (halloc.local_alloc_sync tf₃ rfl e_d he_d).1 slot_d hslot_d hd_d
        obtain ⟨dstLA, hfind_d', _, _, hshape_d'⟩ := hshape_fn_d decl_d hdecl_d
        have hfind_d : m.machine.memory.live.find? (fun x => x.1 == dstId) =
            some (dstId, dstLA) := by rw [← hea_d']; exact hfind_d'
        have hshape_d : StackScalarAllocShape (translateSizeBytes elemBytes)
            dstLA.allocation := htr_d ▸ hshape_d'
        have hts_nat : (translateSizeBytes elemBytes).bytes.toNat = elemBytes := by
          rcases hvalid_sz with rfl | rfl | rfl | rfl | rfl <;> rfl
        have hmls_s_eq : mls_s = ⟨.live (.indirect (stackAllocPlace e_s.allocId)), lay_s⟩ := by
          rw [hlay_s] at hmls_s; exact Option.some.inj hmls_s.symm
        have hnz_sz_s : (translateTy decl_s.ty body.layouts).layout.size ≠
            Miri.ABI.Size.ZERO := by
          rw [htr_s]; intro h
          have := congrArg (fun z : Miri.ABI.Size => z.bytes.toNat) h
          rw [hts_nat] at this; change elemBytes = 0 at this; omega
        obtain ⟨hun_spec, hsc_spec⟩ := hloc_s.indirect_stackAllocPlace_spec hmls_s_eq
          (halloc.base_addr_valid e_s he_s).2.2 hfind_s'
          (halloc.live_key_unique e_s he_s) hnz_sz_s
        -- Either `slot_s = .uninit` or `slot_s = .init (.scalar sc_s)` with `e_s.localIdx ≠ e_d.localIdx`.
        have hm_copy : ∃ mach', copyMiriStmtAction body srcIdx dstIdx countOp m =
            .ok () { stack := ⟨#[tf₃]⟩, machine := mach' } := by
          cases hs_case : slot_s with
          | dead => exact absurd hs_case hd_s
          | uninit =>
            have hni := hun_spec hs_case
            rw [htr_s] at hni
            have hmask_false : srcLA.allocation.initializationMask =
                Miri.Memory.InitMask.new (translateSizeBytes elemBytes) false := by
              obtain ⟨_, _, _, _, bS, hmaskS⟩ := hshape_s
              cases bS with
              | false => exact hmaskS
              | true =>
                exfalso; apply hni; rw [hmaskS]
                rcases hvalid_sz with rfl | rfl | rfl | rfl | rfl <;> rfl
            obtain ⟨mach', hmc⟩ := annealMemCopy_live_uninit_ok
              (st := { m with stack := ⟨#[tf₃]⟩ }) hvalid_sz srcId srcBorTag srcLA
              dstId dstBorTag dstLA hid_s hbase_s hfind_s hshape_s hmask_false
              hid_d hbase_d hfind_d hshape_d
            exact ⟨mach', by rw [hm_mem]; exact hmc⟩
          | init v_s =>
            rcases hun_or_dist with hun_s | hne_loc
            · rw [hslot_s, hs_case] at hun_s; cases hun_s
            · obtain ⟨sc_s, rfl⟩ := hsc_only_s v_s hs_case
              obtain ⟨_, _, _, msc_s, _, hread_s⟩ := hsc_spec sc_s hs_case
              rw [htr_s] at hread_s
              have hne_id : srcId ≠ dstId := by
                intro hid
                apply hne_loc
                exact halloc.alloc_to_local_injective e_s he_s e_d he_d
                  (hea_s'.trans (hid.trans hea_d'.symm))
              have hsz_la_s : srcLA.allocation.byteSize.bytes.toNat = elemBytes := by
                rw [hshape_s.byteSize_eq, hts_nat]
              have hsz_la_d : dstLA.allocation.byteSize.bytes.toNat = elemBytes := by
                rw [hshape_d.byteSize_eq, hts_nat]
              obtain ⟨alloc', hcopy_ok, _, _, _, _⟩ :=
                hshape_s.copyRepeatedly_init_distinct hvalid_sz hshape_d hread_s
              have hmc := annealMemCopy_live_distinct_ok
                (st := { m with stack := ⟨#[tf₃]⟩ }) hvalid_sz srcId srcBorTag srcLA
                dstId dstBorTag dstLA alloc' hne_id hid_s hbase_s hfind_s hsz_la_s
                hid_d hbase_d hfind_d hsz_la_d hcopy_ok
              exact ⟨_, by rw [hm_mem]; exact hmc⟩
        obtain ⟨mach', hm_act⟩ := hm_copy
        exact ⟨_, copyStep_miri_ok hframes hfr.body_eq hfr.location_eq hfr₃.location_eq
          hbb hstmt hm_act⟩

/-- **Characterized divergence (`LM-4.2`)**: copying `count = 1` element from an
uninitialized (`.uninit`) live primitive-scalar stack local into a live
primitive-scalar destination local:

* Anneal's typed `evalCopySingleDirect` rejects reading `.uninit` for a
  non-union scalar local (`stepMirFn body s = MirStepNode.fail .ub`);
* `lean-miri`'s untyped `Allocation.copyRepeatedly` copies uninitialized bytes
  (`initialized.noBytesInit`) and returns `.ok true`. -/
theorem step_intrinsic_copyNonOverlapping_uninit_src_divergence
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {srcIdx dstIdx : Local} {countOp : MirAst.Operand} {span : String}
    {srcDecl dstDecl : LocalDecl} {srcMut dstMut : Mutability} {pointeeTy countTy : Ty}
    {ptId : Miri.MIR.TyId} {elemBytes elemAlign : Nat}
    {srcPtr dstPtr : ProvenancePtr} {countSc : MirAst.ScalarInt}
    {e_s e_d : AllocMapEntry}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.intrinsic (.copyNonOverlapping (.copy ⟨srcIdx, []⟩) (.copy ⟨dstIdx, []⟩) countOp),
        span⟩)
    (hsrcDecl : get? body.localDecls srcIdx = some srcDecl)
    (hsrcTy : srcDecl.ty.kind = .rawPtr srcMut pointeeTy.kind)
    (hsrcImm : ∀ tf, m.stack.frames = #[tf] → IsImmediateFrameLocal tf srcIdx)
    (hdstDecl : get? body.localDecls dstIdx = some dstDecl)
    (hdstTy : dstDecl.ty.kind = .rawPtr dstMut pointeeTy.kind)
    (hdstImm : ∀ tf, m.stack.frames = #[tf] → IsImmediateFrameLocal tf dstIdx)
    (hcountInt : IsIntegralTy countTy .usize)
    (hcountOp : ∀ tf, m.stack.frames = #[tf] → WellTypedScalarOperand body tf countOp countTy)
    (hpt : CopyPointee body.layouts pointeeTy.kind ptId elemBytes elemAlign)
    (hsrc_val : get? s.frame.locals srcIdx = some (.init (.ptr srcPtr 8)))
    (hdst_val : get? s.frame.locals dstIdx = some (.init (.ptr dstPtr 8)))
    (hoff0_s : srcPtr.offsetBytes = 0)
    (hoff0_d : dstPtr.offsetBytes = 0)
    (hcnt_pre : WriteBytesScalarPreVal s.frame.locals countOp countSc)
    (hcnt1 : countSc.bits = 1)
    (he_s : e_s ∈ allocMap) (het_s : e_s.tag = srcPtr.tag)
    (he_d : e_d ∈ allocMap) (het_d : e_d.tag = dstPtr.tag)
    (hsrc_tgt : ∀ decl_s, get? body.localDecls e_s.localIdx = some decl_s →
      decl_s.ty.kind = pointeeTy.kind)
    (hdst_tgt : ∀ decl_d, get? body.localDecls e_d.localIdx = some decl_d →
      decl_d.ty.kind = pointeeTy.kind)
    (huninit_s : get? s.frame.locals e_s.localIdx = some .uninit)
    (hdst_live : get? s.frame.locals e_d.localIdx ≠ some .dead) :
    stepMirFn body s = MirStepNode.fail .ub ∧
    ∃ m',
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .ok true) := by
  have hsrc_live : get? s.frame.locals e_s.localIdx ≠ some .dead := by
    rw [huninit_s]; nofun
  obtain ⟨ha_eq, hm_ok⟩ := copyDivergence_core hstate hphase hbb hstmt
    hsrcDecl hsrcTy hsrcImm hdstDecl hdstTy hdstImm hcountInt hcountOp hpt
    hsrc_val hdst_val hoff0_s hoff0_d hcnt_pre hcnt1 he_s het_s he_d het_d
    hsrc_tgt hdst_tgt hsrc_live hdst_live (Or.inl huninit_s)
  refine ⟨?_, hm_ok⟩
  rw [ha_eq]
  have hsd := evalCopySingleDirect_uninit_src_ub (s := s) (src := .copy ⟨srcIdx, []⟩)
    (dst := .copy ⟨dstIdx, []⟩) (localDecls := body.localDecls) (layouts := body.layouts)
    (srcPtr := srcPtr) (dstPtr := dstPtr) (e_s := e_s) (e_d := e_d) huninit_s
  cases e_s.perm <;> cases e_d.perm <;> first | rfl | exact hsd

/-- **Characterized divergence (`LM-4.2`)**: copying `count = 1` element between
distinct live primitive-scalar stack locals when `e_s.perm = .disabled` or
`e_d.perm` is `.frozen` / `.disabled`:

* Anneal enforces Tree Borrows read permission on `src` and write permission on
  `dst` (`stepMirFn body s = MirStepNode.fail .ub`);
* `lean-miri` under `annealMemoryCopyHooks` (which tracks no Tree Borrows state
  in `LM-3.1`) checks only allocation mutability and returns `.ok true`. -/
theorem step_intrinsic_copyNonOverlapping_perm_divergence
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {srcIdx dstIdx : Local} {countOp : MirAst.Operand} {span : String}
    {srcDecl dstDecl : LocalDecl} {srcMut dstMut : Mutability} {pointeeTy countTy : Ty}
    {ptId : Miri.MIR.TyId} {elemBytes elemAlign : Nat}
    {srcPtr dstPtr : ProvenancePtr} {countSc : MirAst.ScalarInt}
    {e_s e_d : AllocMapEntry}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.intrinsic (.copyNonOverlapping (.copy ⟨srcIdx, []⟩) (.copy ⟨dstIdx, []⟩) countOp),
        span⟩)
    (hsrcDecl : get? body.localDecls srcIdx = some srcDecl)
    (hsrcTy : srcDecl.ty.kind = .rawPtr srcMut pointeeTy.kind)
    (hsrcImm : ∀ tf, m.stack.frames = #[tf] → IsImmediateFrameLocal tf srcIdx)
    (hdstDecl : get? body.localDecls dstIdx = some dstDecl)
    (hdstTy : dstDecl.ty.kind = .rawPtr dstMut pointeeTy.kind)
    (hdstImm : ∀ tf, m.stack.frames = #[tf] → IsImmediateFrameLocal tf dstIdx)
    (hcountInt : IsIntegralTy countTy .usize)
    (hcountOp : ∀ tf, m.stack.frames = #[tf] → WellTypedScalarOperand body tf countOp countTy)
    (hpt : CopyPointee body.layouts pointeeTy.kind ptId elemBytes elemAlign)
    (hsrc_val : get? s.frame.locals srcIdx = some (.init (.ptr srcPtr 8)))
    (hdst_val : get? s.frame.locals dstIdx = some (.init (.ptr dstPtr 8)))
    (hoff0_s : srcPtr.offsetBytes = 0)
    (hoff0_d : dstPtr.offsetBytes = 0)
    (hcnt_pre : WriteBytesScalarPreVal s.frame.locals countOp countSc)
    (hcnt1 : countSc.bits = 1)
    (he_s : e_s ∈ allocMap) (het_s : e_s.tag = srcPtr.tag)
    (he_d : e_d ∈ allocMap) (het_d : e_d.tag = dstPtr.tag)
    (hne_loc : e_s.localIdx ≠ e_d.localIdx)
    (hsrc_tgt : ∀ decl_s, get? body.localDecls e_s.localIdx = some decl_s →
      decl_s.ty.kind = pointeeTy.kind)
    (hdst_tgt : ∀ decl_d, get? body.localDecls e_d.localIdx = some decl_d →
      decl_d.ty.kind = pointeeTy.kind)
    (hsrc_live : get? s.frame.locals e_s.localIdx ≠ some .dead)
    (hdst_live : get? s.frame.locals e_d.localIdx ≠ some .dead)
    (hperm_bad : e_s.perm = .disabled ∨ e_d.perm = .frozen ∨ e_d.perm = .disabled) :
    stepMirFn body s = MirStepNode.fail .ub ∧
    ∃ m',
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .ok true) := by
  obtain ⟨ha_eq, hm_ok⟩ := copyDivergence_core hstate hphase hbb hstmt
    hsrcDecl hsrcTy hsrcImm hdstDecl hdstTy hdstImm hcountInt hcountOp hpt
    hsrc_val hdst_val hoff0_s hoff0_d hcnt_pre hcnt1 he_s het_s he_d het_d
    hsrc_tgt hdst_tgt hsrc_live hdst_live (Or.inr hne_loc)
  refine ⟨?_, hm_ok⟩
  rw [ha_eq]
  cases hpS : e_s.perm <;> cases hpD : e_d.perm <;>
    first | rfl | (simp [hpS, hpD] at hperm_bad)

end LeanMiriSpec.Correspondence
