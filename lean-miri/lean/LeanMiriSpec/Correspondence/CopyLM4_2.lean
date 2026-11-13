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

> **Anneal side of §2–§7 is the pre-Stage-1 reference model, not Stage-1
> `Trusted`.** Every `StepRelLM3_1` theorem below whose Anneal side is
> `stepMirFnLM4_2` (`evalCopyNonOverlappingLM4_2` /
> `evalCopyNonOverlappingWithCountLM4_2` / `evalCopyRootIntScalars`, defined in
> `CallLM4_2.lean`) relates `lean-miri` to that reference model only. Stage-1
> `evalCopyNonOverlapping` (`Statements.lean:1739`) disagrees with it on (at least)
> zero-count misaligned copies, out-of-bounds distinct-local copies, same-local
> disjoint sub-range copies, and cross-type single-element copies, each of which
> `WitLM4_2.lean` §6 certifies as a concrete Stage-1 divergence from `lean-miri`.
> §8 holds the only Stage-1 statement of this file, an Anneal-side evaluation
> lemma (no Stage-1 lockstep simulation for `copy_nonoverlapping` exists yet).

One-step correspondence between the pre-Stage-1 reference model's
`evalCopyNonOverlappingLM4_2` and `lean-miri`'s
`Miri.Interpreter.Step.step` (`Intrinsics.evalNondiverging (.CopyNonOverlapping ...)` /
`annealCopyEval` / `annealCheckPtrAlign` / `annealMemCopy`) from `StateRelLM3_1`:

* `step_intrinsic_copyNonOverlapping_simulation` (and its explicit-`allocMap'`
  counterpart `step_intrinsic_copyNonOverlapping_simulation_explicit`) proves
  `StepRelLM3_1` lockstep (reference model vs `lean-miri`) across:
  1. uninitialized or dead `src`, `dst`, or `count` operands (UB in both);
  2. `count * size_of::<T>() > isize::MAX` (`isizeMaxBytes`) overflow (UB in
     both);
  3. misaligned `src` or `dst` (`offset % align_of::<T>() ≠ 0`), including when
     `count = 0` or `size_of::<T>() = 0` (UB in both; Stage-1 instead steps when
     `count = 0`);
  4. aligned zero-byte copy (`count * size_of::<T>() = 0`), including on
     provenance-free, dead, or out-of-bounds pointers (no-op step preserving
     `StateRelLM3_1` in both);
  5. positive-byte copy with provenance-free `.scalar` `src` or `dst`, dead
     source or destination stack local, or out-of-bounds byte range (UB in
     both; Stage-1 instead steps on out-of-bounds distinct-local copies);
  6. positive-byte copy on overlapping byte ranges of the same live initialized
     allocation (`e_src.localIdx = e_dst.localIdx` with
     `srcStart < dstStart + total` and `dstStart < srcStart + total`): overlap UB
     (`AllocError.copyRangesOverlap`) in both;
  7. positive-byte copy across arbitrary in-bounds byte ranges (`CopyTargetCompatible`:
     cross-type integer byte copies such as `*const u8 -> *mut u64`, multi-element
     counts `count > 1`, non-zero byte offsets, partial sub-local byte splices,
     whole-local `.uninit` destination initialization, disjoint byte sub-ranges
     of the same local, and `.bool` / `.char` same-type copies) with valid
     Tree Borrows permissions: copies `rawBytes`, `InitMask`, and
     `ProvenanceMap` byte-for-byte, invalidates conflicting borrows on `dst`,
     and preserves `StateRelLM3_1` (Stage-1 instead rejects same-tag disjoint
     sub-ranges and copies whole source values across pointee types).
* Characterized real-step divergences (which persist on Stage-1, see
  `WitLM4_2.lean` §6):
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
(`rigidTyKindByteSize`, `rigidTyKindAlignBytes`) and `lean-miri`
(`rawPtrPointeeEncodedTyId?`, `layoutOfEncodedTyId`). -/
structure CopyPointee (ly : LayoutTable) (pointeeKind : RigidTy)
    (ptId : Miri.MIR.TyId) (elemBytes elemAlign : Nat) : Prop where
  wb : WriteBytesPointee ly pointeeKind ptId elemBytes
  anneal_align : rigidTyKindAlignBytes pointeeKind = some elemAlign
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

/-- The `layoutIdx` assigned by `operandPointeeTy` to the pointee of `.copy ⟨ptrIdx, []⟩`. -/
def operandPointeeLayoutIdx (localDecls : List LocalDecl) (layouts : LayoutTable)
    (ptrIdx : Local) : Nat :=
  match operandPointeeTy localDecls layouts (.copy ⟨ptrIdx, []⟩) with
  | some pt => pt.layoutIdx
  | none => 0

private theorem operandPointeeTy_copy_rawPtr_exists {localDecls : List LocalDecl}
    {layouts : LayoutTable} {ptrIdx : Local} {ptrDecl : LocalDecl}
    {mutability : Mutability} {pointeeKind : RigidTy}
    (hdecl : get? localDecls ptrIdx = some ptrDecl)
    (hty : ptrDecl.ty.kind = .rawPtr mutability pointeeKind) :
    ∃ idx, operandPointeeTy localDecls layouts (.copy ⟨ptrIdx, []⟩) =
      some { kind := pointeeKind, layoutIdx := idx } := by
  unfold operandPointeeTy operandTy placeTy
  dsimp only
  rw [hdecl]
  dsimp only [resolveProjectedTy, pointeeTyOf]
  rw [hty]
  dsimp only
  cases LayoutTable.lookup layouts ptrDecl.ty.layoutIdx with
  | none => exact ⟨0, rfl⟩
  | some ptrLayout =>
    dsimp only
    split <;> exact ⟨_, rfl⟩

/-- Anneal's `operandPointeeTy` on a copy of an unprojected raw-pointer local. -/
theorem operandPointeeTy_copy_rawPtr {localDecls : List LocalDecl} {layouts : LayoutTable}
    {ptrIdx : Local} {ptrDecl : LocalDecl} {mutability : Mutability} {pointeeKind : RigidTy}
    (hdecl : get? localDecls ptrIdx = some ptrDecl)
    (hty : ptrDecl.ty.kind = .rawPtr mutability pointeeKind) :
    operandPointeeTy localDecls layouts (.copy ⟨ptrIdx, []⟩) =
      some { kind := pointeeKind,
             layoutIdx := operandPointeeLayoutIdx localDecls layouts ptrIdx } := by
  obtain ⟨idx, h⟩ := operandPointeeTy_copy_rawPtr_exists (layouts := layouts) hdecl hty
  unfold operandPointeeLayoutIdx; rw [h]

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

/-! ### 4b. Byte-range `Allocation.copyRepeatedly` lemmas -/

private theorem copyIte_pos {P : Prop} [Decidable P] {α : Type _} {a b : α} (h : P) :
    (if P then a else b) = a := by simp [h]

private theorem copyIte_neg {P : Prop} [Decidable P] {α : Type _} {a b : α} (h : ¬ P) :
    (if P then a else b) = b := by simp [h]

private def copyLe_pointerSize (layout : Miri.ABI.TargetDataLayout) : Miri.ABI.Size :=
  Miri.ABI.Size.fromBits layout.pointerWidth.bits

private def copyLe_readTargetUInt (layout : Miri.ABI.TargetDataLayout)
    (bytes : Array UInt8) : Except Miri.Memory.AllocError Miri.ABI.U128 := do
  if bytes.size > 16 then
    throw (.scalarBytesTooWide (Miri.ABI.Size.ofBytes (UInt64.ofNat bytes.size)))
  let mut value := 0
  for index in [:bytes.size] do
    let some byte := bytes[index]? | throw (.invalidSliceEndpoints index (index + 1) bytes.size)
    let valueIndex := if layout.endian == .little then index else bytes.size - index - 1
    value := value + byte.toNat * 2 ^ (8 * valueIndex)
  return BitVec.ofNat 128 value

private def copyLe_readScalar {P E : Type} [DecidableEq P] [Miri.Memory.PointerProvenance P]
    (allocation : Miri.Memory.Allocation P E) (layout : Miri.ABI.TargetDataLayout)
    (range : Miri.Memory.AllocRange) (readProvenance : Bool) :
    Except Miri.Memory.AllocError (Miri.Memory.Scalar P) := do
  match ← (allocation.initializationMask.isRangeInitialized range).mapError
      Miri.Memory.AllocError.memory with
  | .error bad => throw (.invalidUninitBytes (some ⟨range, bad⟩))
  | .ok () => pure ()
  let bytes ← Miri.Memory.Allocation.getBytesUnchecked allocation range
  let bits ← copyLe_readTargetUInt layout bytes
  if readProvenance then
    let targetSize := copyLe_pointerSize layout
    if range.size != targetSize then
      throw (.scalarPointerNotTargetSized range.size targetSize)
    let provenance ← match allocation.provenanceMap.readPtr range.start targetSize with
      | .ok provenance => pure provenance
      | .error (.readPartialPointer offset) => throw (.readPartialPointer offset)
      | .error reason => throw (.provenance reason)
    match provenance with
    | some provenance =>
      if bits.toNat > 18446744073709551615 then
        throw (.pointerBitsDoNotFitOffset bits)
      return Miri.Memory.Scalar.fromPointer layout
        (Miri.Memory.Pointer.new provenance (Miri.ABI.Size.ofBytes (UInt64.ofNat bits.toNat)))
    | none =>
      let scalar ← (Miri.Memory.Scalar.fromUInt bits range.size).mapError
        Miri.Memory.AllocError.scalar
      return scalar
  else
    if Miri.Memory.PointerProvenance.offsetIsAddr (Prov := P) then
      let scalar ← (Miri.Memory.Scalar.fromUInt bits range.size).mapError
        Miri.Memory.AllocError.scalar
      return scalar
    let isEmpty ←
      (allocation.provenanceMap.rangeEmpty range (copyLe_pointerSize layout)).mapError
        Miri.Memory.AllocError.provenance
    if isEmpty then
      let scalar ← (Miri.Memory.Scalar.fromUInt bits range.size).mapError
        Miri.Memory.AllocError.scalar
      return scalar
    throw (.readPointerAsInt none)

private theorem copyLe_readScalar_eq {P E : Type} [DecidableEq P]
    [Miri.Memory.PointerProvenance P]
    (allocation : Miri.Memory.Allocation P E) (layout : Miri.ABI.TargetDataLayout)
    (range : Miri.Memory.AllocRange) (readProvenance : Bool) :
    allocation.readScalar layout range readProvenance =
      copyLe_readScalar allocation layout range readProvenance := rfl

private def copyLe_bytes (x n : Nat) : Array UInt8 :=
  ((List.range' 0 n).map fun i => UInt8.ofNat ((x / 2 ^ (8 * i)) % 256)).toArray

private theorem copyLe_bytes_size (x n : Nat) : (copyLe_bytes x n).size = n := by
  simp [copyLe_bytes]

private def copyLe_sum (x k : Nat) : Nat → Nat
  | 0 => 0
  | m + 1 => x / 2 ^ (8 * k) % 256 * 2 ^ (8 * k) + copyLe_sum x (k + 1) m

private theorem copyLe_sum_spec (x : Nat) :
    ∀ m k, x % 2 ^ (8 * k) + copyLe_sum x k m = x % 2 ^ (8 * (k + m)) := by
  intro m
  induction m with
  | zero => intro k; simp [copyLe_sum]
  | succ m ih =>
    intro k
    have hstep : x % 2 ^ (8 * k) + x / 2 ^ (8 * k) % 256 * 2 ^ (8 * k) =
        x % 2 ^ (8 * (k + 1)) := by
      rw [show 8 * (k + 1) = 8 * k + 8 by omega, Nat.pow_add, Nat.mod_mul]
      simp only [show (2 : Nat) ^ 8 = 256 by rfl]
      rw [Nat.mul_comm (2 ^ (8 * k))]
    simp only [copyLe_sum]
    rw [← Nat.add_assoc, hstep, ih (k + 1), show k + 1 + m = k + (m + 1) by omega]

private theorem copyLe_decode_loop (x n : Nat)
    (f : Nat → Nat → Except Miri.Memory.AllocError (ForInStep Nat))
    (hf : ∀ index s, index < n →
      f index s = .ok (.yield (s + x / 2 ^ (8 * index) % 256 * 2 ^ (8 * index)))) :
    ∀ m k acc, k + m ≤ n →
      forIn (List.range' k m) acc f = .ok (acc + copyLe_sum x k m) := by
  intro m
  induction m with
  | zero => intro k acc _; simp [copyLe_sum, pure, Except.pure]
  | succ m ih =>
    intro k acc hkm
    rw [List.range'_succ, List.forIn_cons, hf k acc (by omega)]
    simp only [copyLe_sum]
    rw [show (Except.ok (ForInStep.yield (acc + x / 2 ^ (8 * k) % 256 * 2 ^ (8 * k))) :
        Except Miri.Memory.AllocError (ForInStep Nat)) = pure (ForInStep.yield _) from rfl,
      pure_bind]
    simp only
    rw [ih (k + 1) _ (by omega), Nat.add_assoc]

private theorem copyLe_readTargetUInt_bytes (x n : Nat) (hn : n ≤ 16) :
    copyLe_readTargetUInt annealTargetDataLayout (copyLe_bytes x n) =
      .ok (BitVec.ofNat 128 (x % 2 ^ (8 * n))) := by
  have small : ¬ n > 16 := by omega
  have hendian : (annealTargetDataLayout.endian == Miri.ABI.Endian.little) = true := rfl
  have hlsize : (copyLe_bytes x n).size = n := copyLe_bytes_size x n
  unfold copyLe_readTargetUInt
  simp only [hlsize, small, ↓reduceIte, Std.Legacy.Range.forIn_eq_forIn_range',
    hendian, Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  rw [copyLe_decode_loop x n _ ?hf n 0 0 (by omega)]
  · have := copyLe_sum_spec x n 0
    simp only [Nat.mul_zero, Nat.pow_zero, Nat.mod_one, Nat.zero_add] at this
    simp [this, pure, Except.pure, bind, Except.bind]
  · intro index s hi
    have hb : (x / 2 ^ (8 * index) % 256) < 256 := Nat.mod_lt _ (by decide)
    simp [copyLe_bytes, hi, pure, Except.pure, Nat.mod_eq_of_lt hb]

private theorem copyScalarModulus_eq_two_pow (sz : Nat) :
    scalarModulus sz = 2 ^ (8 * sz) := by
  induction sz with
  | zero => rfl
  | succ k ih =>
    show 256 * scalarModulus k = 2 ^ (8 * (k + 1))
    rw [ih, show 8 * (k + 1) = 8 * k + 8 by omega, Nat.pow_add, Nat.mul_comm]

private theorem copyScalarModulus_pos (sz : Nat) : 0 < scalarModulus sz := by
  rw [copyScalarModulus_eq_two_pow]; exact Nat.two_pow_pos _

private theorem copyWrapScalarBits_lt (bits sz : Nat) :
    wrapScalarBits bits (scalarModulus sz) < scalarModulus sz := by
  unfold wrapScalarBits
  cases hble : (scalarModulus sz).ble bits
  · dsimp only
    exact Nat.lt_of_not_ge (fun hle => Bool.noConfusion ((Nat.ble_eq.mpr hle).symm.trans hble))
  · dsimp only
    exact Nat.mod_lt _ (copyScalarModulus_pos sz)

private theorem copyWrapScalarBits_eq_of_lt {bits sz : Nat} (h : bits < scalarModulus sz) :
    wrapScalarBits bits (scalarModulus sz) = bits := by
  unfold wrapScalarBits
  have hble : (scalarModulus sz).ble bits = false := by
    cases hb : (scalarModulus sz).ble bits
    · rfl
    · exact absurd (Nat.ble_eq.mp hb) (Nat.not_le_of_lt h)
  rw [hble]

private theorem copyFromUInt {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    (hrel : ScalarRel sc msc) :
    Miri.Memory.Scalar.fromUInt (Prov := AnnealProv) (BitVec.ofNat 128 sc.bits)
        (translateSizeBytes sc.sizeBytes) = .ok (Miri.Memory.Scalar.fromScalarInt msc) := by
  obtain ⟨msc', htry, hrel'⟩ := tryFromUInt_of_valid_canonical hrel.validBytes hrel.canonical
  have heq : msc' = msc := by
    cases msc'; cases msc
    have hd := hrel'.data_eq.trans hrel.data_eq.symm
    have hs := hrel'.size_eq.trans hrel.size_eq.symm
    simp only [Miri.Memory.ScalarInt.data, Miri.Memory.ScalarInt.size] at hd hs
    subst hd hs; rfl
  subst heq
  unfold Miri.Memory.Scalar.fromUInt
  simp [htry, Except.mapError, bind, Except.bind, pure, Except.pure]

private def copyFromLeBytes : List UInt8 → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * copyFromLeBytes bs

private theorem copyFromLeBytes_lt :
    ∀ l : List UInt8, copyFromLeBytes l < 2 ^ (8 * l.length)
  | [] => by simp [copyFromLeBytes]
  | b :: bs => by
    have ih := copyFromLeBytes_lt bs
    have hb := b.toNat_lt
    simp only [copyFromLeBytes, List.length_cons]
    rw [show 8 * (bs.length + 1) = 8 + 8 * bs.length by omega, Nat.pow_add]
    have hle : copyFromLeBytes bs + 1 ≤ 2 ^ (8 * bs.length) := ih
    have hmul : 256 * (copyFromLeBytes bs + 1) ≤ 2 ^ 8 * 2 ^ (8 * bs.length) :=
      Nat.mul_le_mul_left 256 hle
    omega

private theorem copyFromLeBytes_byte :
    ∀ (l : List UInt8) (i : Nat) (hi : i < l.length),
      (copyFromLeBytes l / 2 ^ (8 * i)) % 256 = (l[i]'hi).toNat
  | [], _, hi => absurd hi (Nat.not_lt_zero _)
  | b :: bs, 0, _ => by
    have hb := b.toNat_lt
    show (b.toNat + 256 * copyFromLeBytes bs) / 1 % 256 = b.toNat
    omega
  | b :: bs, j + 1, hi => by
    have hb := b.toNat_lt
    have hj : j < bs.length := by simp at hi; omega
    have hpow : 2 ^ (8 * (j + 1)) = 256 * 2 ^ (8 * j) := by
      rw [show 8 * (j + 1) = 8 + 8 * j by omega, Nat.pow_add]
    have hdiv : (b.toNat + 256 * copyFromLeBytes bs) / (256 * 2 ^ (8 * j)) =
        copyFromLeBytes bs / 2 ^ (8 * j) := by
      rw [← Nat.div_div_eq_div_mul]
      have h1 : (b.toNat + 256 * copyFromLeBytes bs) / 256 = copyFromLeBytes bs := by omega
      rw [h1]
    show (b.toNat + 256 * copyFromLeBytes bs) / 2 ^ (8 * (j + 1)) % 256 = bs[j].toNat
    rw [hpow, hdiv]
    exact copyFromLeBytes_byte bs j hj

private theorem copyLe_bytes_fromLeBytes (bytes : Array UInt8) :
    copyLe_bytes (copyFromLeBytes bytes.toList) bytes.size = bytes := by
  apply Array.ext
  · simp [copyLe_bytes]
  · intro i hi₁ hi₂
    have hi_list : i < bytes.toList.length := by simpa using hi₂
    have hbyte := copyFromLeBytes_byte bytes.toList i hi_list
    simp [copyLe_bytes, hbyte]

private theorem copyLe_decode_readScalar {E : Type} {n : Nat}
    (hn : ValidScalarBytes n) {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    (hrel : ScalarRel sc msc) (hsz : sc.sizeBytes = n)
    {A : Miri.Memory.Allocation AnnealProv E}
    (hshape : StackScalarAllocShape (translateSizeBytes n) A)
    (hread : A.readScalar annealTargetDataLayout
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes n)) false =
      .ok (.fromScalarInt msc)) :
    A.initializationMask = Miri.Memory.InitMask.new (translateSizeBytes n) true ∧
    copyAlloc_raw A = copyLe_bytes sc.bits n := by
  have hold_can : sc.bits < scalarModulus n := hsz ▸ hrel.canonical
  have hn_eq : (translateSizeBytes n).bytes.toNat = n := by
    rcases hn with rfl | rfl | rfl | rfl | rfl <;> rfl
  have hn16 : n ≤ 16 := by rcases hn with rfl | rfl | rfl | rfl | rfl <;> omega
  have hn16_tr : (translateSizeBytes n).bytes.toNat ≤ 16 := by rw [hn_eq]; exact hn16
  have hend_full := copyAlloc_allocRange_end (translateSizeBytes n)
  have hinitA : A.initializationMask.isRangeInitialized
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes n)) = .ok (.ok ()) :=
    Classical.byContradiction fun hni => by
      obtain ⟨_, herr⟩ := hshape.uninit_readScalar_err hni false
      rw [hread] at herr
      cases herr
  have hmask_true : A.initializationMask = Miri.Memory.InitMask.new (translateSizeBytes n) true := by
    obtain ⟨b, hb⟩ := hshape.initMask_lazy
    cases b with
    | true => exact hb
    | false =>
      rw [hb] at hinitA
      rcases hn with rfl | rfl | rfl | rfl | rfl <;> cases hinitA
  refine ⟨hmask_true, ?_⟩
  have hraw_sz : (copyAlloc_raw A).size = n := hshape.len_eq.trans hn_eq
  let x := copyFromLeBytes (copyAlloc_raw A).toList
  have hx_can : x < scalarModulus n := by
    rw [copyScalarModulus_eq_two_pow]
    have hlt := copyFromLeBytes_lt (copyAlloc_raw A).toList
    have hlen_l : (copyAlloc_raw A).toList.length = n := by simpa using hraw_sz
    rw [hlen_l] at hlt
    exact hlt
  obtain ⟨xmsc, _, hx_rel⟩ := tryFromUInt_of_valid_canonical (sc := ⟨x, n⟩) hn hx_can
  have hraw_x : copyAlloc_raw A = copyLe_bytes x n := by
    have := copyLe_bytes_fromLeBytes (copyAlloc_raw A)
    rw [hraw_sz] at this
    exact this.symm
  have hslice_A : copyAlloc_checkedSlice A
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes n)) =
      .ok (copyLe_bytes x (translateSizeBytes n).bytes.toNat) := by
    have hrawsize : (copyAlloc_raw A).size = (translateSizeBytes n).bytes.toNat := hshape.len_eq
    unfold copyAlloc_checkedSlice
    simp only [hrawsize, hshape.byteSize_eq, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
      hend_full, Except.mapError, bind, Except.bind]
    simp [Miri.Memory.allocRange, Miri.ABI.Size.ZERO, pure, Except.pure, hraw_x, hn_eq,
      copyLe_bytes_size]
  have hoff_addr : Miri.Memory.PointerProvenance.offsetIsAddr AnnealProv = true := rfl
  have hx_mod : x % 2 ^ (8 * (translateSizeBytes n).bytes.toNat) = x := by
    rw [hn_eq, ← copyScalarModulus_eq_two_pow]
    exact Nat.mod_eq_of_lt hx_can
  have hrange_sz :
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes n)).size =
        translateSizeBytes n := rfl
  have hread_x : A.readScalar annealTargetDataLayout
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes n)) false =
      .ok (Miri.Memory.Scalar.fromScalarInt xmsc) := by
    rw [copyLe_readScalar_eq]
    unfold copyLe_readScalar
    rw [hinitA]
    simp only [Except.mapError, bind, Except.bind]
    rw [copyAlloc_getBytesUnchecked_eq, hslice_A]
    simp only []
    rw [copyLe_readTargetUInt_bytes _ _ hn16_tr, hx_mod]
    simp only [Bool.false_eq_true, ↓reduceIte, hoff_addr, hrange_sz, copyFromUInt hx_rel]
  have hsc_eq : Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) xmsc =
      Miri.Memory.Scalar.fromScalarInt msc :=
    Except.ok.inj (hread_x.symm.trans hread)
  have hdata_eq : BitVec.ofNat 128 x = BitVec.ofNat 128 sc.bits := by
    unfold Miri.Memory.Scalar.fromScalarInt at hsc_eq
    injection hsc_eq with hpay _
    injection hpay with hmsc_eq
    exact hx_rel.data_eq.symm.trans ((congrArg Miri.Memory.ScalarInt.data hmsc_eq).trans
      hrel.data_eq)
  have hx_eq : x = sc.bits := by
    have hpow128 : scalarModulus n ≤ 2 ^ 128 := by
      rw [copyScalarModulus_eq_two_pow]
      exact Nat.pow_le_pow_right (by decide) (by omega)
    have h1 : (BitVec.ofNat 128 x).toNat = x := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hx_can hpow128)
    have h2 : (BitVec.ofNat 128 sc.bits).toNat = sc.bits := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hold_can hpow128)
    rw [← h1, ← h2, hdata_eq]
  rw [hraw_x, hx_eq]

private theorem copyLe_encode_readScalar {E : Type} {n : Nat}
    (hn : ValidScalarBytes n) {bits : Nat} (hcan : bits < scalarModulus n)
    {A : Miri.Memory.Allocation AnnealProv E}
    (hshape : StackScalarAllocShape (translateSizeBytes n) A)
    (hmask : A.initializationMask = Miri.Memory.InitMask.new (translateSizeBytes n) true)
    (hraw : copyAlloc_raw A = copyLe_bytes bits n) :
    ∃ msc : Miri.Memory.ScalarInt,
      ScalarRel ⟨bits, n⟩ msc ∧
      A.initializationMask.isRangeInitialized
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes n)) = .ok (.ok ()) ∧
      A.readScalar annealTargetDataLayout
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes n)) false =
        .ok (.fromScalarInt msc) := by
  obtain ⟨msc, _, hrel⟩ := tryFromUInt_of_valid_canonical (sc := ⟨bits, n⟩) hn hcan
  have hn_eq : (translateSizeBytes n).bytes.toNat = n := by
    rcases hn with rfl | rfl | rfl | rfl | rfl <;> rfl
  have hn16 : n ≤ 16 := by rcases hn with rfl | rfl | rfl | rfl | rfl <;> omega
  have hn16_tr : (translateSizeBytes n).bytes.toNat ≤ 16 := by rw [hn_eq]; exact hn16
  have hend_full := copyAlloc_allocRange_end (translateSizeBytes n)
  have hinit : A.initializationMask.isRangeInitialized
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes n)) = .ok (.ok ()) := by
    rw [hmask]; rcases hn with rfl | rfl | rfl | rfl | rfl <;> rfl
  refine ⟨msc, hrel, hinit, ?_⟩
  have hraw_le : copyAlloc_raw A = copyLe_bytes bits (translateSizeBytes n).bytes.toNat := by
    rw [hraw, hn_eq]
  have hslice_read : copyAlloc_checkedSlice A
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes n)) =
      .ok (copyLe_bytes bits (translateSizeBytes n).bytes.toNat) := by
    have hrawsize : (copyAlloc_raw A).size = (translateSizeBytes n).bytes.toNat := hshape.len_eq
    unfold copyAlloc_checkedSlice
    simp only [hrawsize, hshape.byteSize_eq, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
      hend_full, Except.mapError, bind, Except.bind]
    simp [Miri.Memory.allocRange, Miri.ABI.Size.ZERO, pure, Except.pure, hraw_le, copyLe_bytes_size]
  have hoff_addr : Miri.Memory.PointerProvenance.offsetIsAddr AnnealProv = true := rfl
  have hmod : bits % 2 ^ (8 * (translateSizeBytes n).bytes.toNat) = bits := by
    rw [hn_eq, ← copyScalarModulus_eq_two_pow]
    exact Nat.mod_eq_of_lt hcan
  have hrange_sz :
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes n)).size =
        translateSizeBytes n := rfl
  rw [copyLe_readScalar_eq]
  unfold copyLe_readScalar
  rw [hinit]
  simp only [Except.mapError, bind, Except.bind]
  rw [copyAlloc_getBytesUnchecked_eq, hslice_read]
  simp only []
  rw [copyLe_readTargetUInt_bytes _ _ hn16_tr, hmod]
  simp only [Bool.false_eq_true, ↓reduceIte, hoff_addr, hrange_sz, copyFromUInt hrel]

private theorem copyByte_of_split {a b k i : Nat} (ha : a < 2 ^ (8 * k)) :
    ((a + b * 2 ^ (8 * k)) / 2 ^ (8 * i)) % 256 =
      if i < k then (a / 2 ^ (8 * i)) % 256 else (b / 2 ^ (8 * (i - k))) % 256 := by
  by_cases hik : i < k
  · simp only [hik, ↓reduceIte]
    have hpow : 2 ^ (8 * k) = (256 * 2 ^ (8 * (k - i - 1))) * 2 ^ (8 * i) := by
      rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_add, ← Nat.pow_add]
      exact congrArg (2 ^ ·) (by omega)
    have hmul : b * 2 ^ (8 * k) = (b * 2 ^ (8 * (k - i - 1)) * 256) * 2 ^ (8 * i) := by
      rw [hpow]; ac_rfl
    rw [hmul, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.add_mul_mod_self_right]
  · simp only [hik, ↓reduceIte]
    have hpow : 2 ^ (8 * i) = 2 ^ (8 * k) * 2 ^ (8 * (i - k)) := by
      rw [← Nat.pow_add]
      exact congrArg (2 ^ ·) (by omega)
    rw [hpow, ← Nat.div_div_eq_div_mul, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _),
      Nat.div_eq_of_lt ha, Nat.zero_add]

theorem sliceScalarBytes_lt_scalarModulus (srcBits srcBytes srcStart total : Nat) :
    sliceScalarBytes srcBits srcBytes srcStart total < scalarModulus total :=
  Nat.mod_lt _ (copyScalarModulus_pos total)

theorem sliceScalarBytes_byte {srcBits srcBytes srcStart total i : Nat}
    (hsrc : srcBits < scalarModulus srcBytes) (hi : i < total) :
    (sliceScalarBytes srcBits srcBytes srcStart total / 2 ^ (8 * i)) % 256 =
      (srcBits / 2 ^ (8 * (srcStart + i))) % 256 := by
  let y := srcBits / 2 ^ (8 * srcStart)
  have hwrap := copyWrapScalarBits_eq_of_lt hsrc
  have hmod_s := copyScalarModulus_eq_two_pow srcStart
  have hmod_t := copyScalarModulus_eq_two_pow total
  have hsl : sliceScalarBytes srcBits srcBytes srcStart total = y % 2 ^ (8 * total) := by
    change (wrapScalarBits srcBits (scalarModulus srcBytes) / scalarModulus srcStart) %
      scalarModulus total = _
    rw [hwrap, hmod_s, hmod_t]
  have hy_lt : y % 2 ^ (8 * total) < 2 ^ (8 * total) := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hy_decomp : y = y % 2 ^ (8 * total) + (y / 2 ^ (8 * total)) * 2 ^ (8 * total) := by
    have h := (Nat.mod_add_div y (2 ^ (8 * total))).symm
    rwa [Nat.mul_comm (2 ^ (8 * total))] at h
  have hsplit := copyByte_of_split (i := i) hy_lt (b := y / 2 ^ (8 * total))
  rw [← hy_decomp, copyIte_pos hi] at hsplit
  rw [hsl, ← hsplit]
  dsimp only [y]
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_add, ← Nat.mul_add]

private theorem copyLe_extract_eq_slice {srcBits srcBytes srcStart total : Nat}
    (hsrc : srcBits < scalarModulus srcBytes) (hinS : srcStart + total ≤ srcBytes) :
    (copyLe_bytes srcBits srcBytes).extract srcStart (srcStart + total) =
      copyLe_bytes (sliceScalarBytes srcBits srcBytes srcStart total) total := by
  apply Array.ext
  · simp only [Array.size_extract, copyLe_bytes_size]; omega
  · intro i hi₁ hi₂
    have hi_tot : i < total := by rw [copyLe_bytes_size] at hi₂; exact hi₂
    rw [Array.getElem_extract]
    simp [copyLe_bytes, sliceScalarBytes_byte hsrc hi_tot]

theorem spliceScalarBytes_lt_scalarModulus (dstBits : Nat) {chunk dstStart total dstBytes : Nat}
    (hchunk : chunk < scalarModulus total) (hinD : dstStart + total ≤ dstBytes) :
    spliceScalarBytes dstBits chunk dstStart total dstBytes < scalarModulus dstBytes := by
  unfold spliceScalarBytes
  have hlow_pos := copyScalarModulus_pos dstStart
  have hmod_lt : wrapScalarBits dstBits (scalarModulus dstBytes) % scalarModulus dstStart <
      scalarModulus dstStart := Nat.mod_lt _ hlow_pos
  have hhigh_eq : scalarModulus (Nat.add dstStart total) =
      scalarModulus total * scalarModulus dstStart := by
    simp only [Nat.add_eq, copyScalarModulus_eq_two_pow]
    rw [show 8 * (dstStart + total) = 8 * total + 8 * dstStart by omega, Nat.pow_add]
  have hmid_lt :
      wrapScalarBits dstBits (scalarModulus dstBytes) % scalarModulus dstStart +
        chunk * scalarModulus dstStart <
      scalarModulus (Nat.add dstStart total) := by
    have hmul_le : chunk * scalarModulus dstStart + scalarModulus dstStart ≤
        scalarModulus total * scalarModulus dstStart := by
      rw [← Nat.succ_mul]
      exact Nat.mul_le_mul_right _ hchunk
    rw [hhigh_eq]; omega
  have hold_lt := copyWrapScalarBits_lt dstBits dstBytes
  have htop_eq : scalarModulus dstBytes =
      scalarModulus (dstBytes - (dstStart + total)) * scalarModulus (Nat.add dstStart total) := by
    simp only [Nat.add_eq, copyScalarModulus_eq_two_pow]
    rw [← Nat.pow_add,
      show 8 * (dstBytes - (dstStart + total)) + 8 * (dstStart + total) = 8 * dstBytes by omega]
  have hhigh_pos := copyScalarModulus_pos (Nat.add dstStart total)
  have hdiv_lt : wrapScalarBits dstBits (scalarModulus dstBytes) /
      scalarModulus (Nat.add dstStart total) <
      scalarModulus (dstBytes - (dstStart + total)) := by
    rw [Nat.div_lt_iff_lt_mul hhigh_pos, ← htop_eq]
    exact hold_lt
  have htop_le :
      (wrapScalarBits dstBits (scalarModulus dstBytes) /
        scalarModulus (Nat.add dstStart total)) *
        scalarModulus (Nat.add dstStart total) + scalarModulus (Nat.add dstStart total) ≤
      scalarModulus dstBytes := by
    calc (wrapScalarBits dstBits (scalarModulus dstBytes) /
            scalarModulus (Nat.add dstStart total)) *
            scalarModulus (Nat.add dstStart total) + scalarModulus (Nat.add dstStart total)
        = (wrapScalarBits dstBits (scalarModulus dstBytes) /
            scalarModulus (Nat.add dstStart total) + 1) *
            scalarModulus (Nat.add dstStart total) := by rw [← Nat.succ_mul]
      _ ≤ scalarModulus (dstBytes - (dstStart + total)) *
            scalarModulus (Nat.add dstStart total) := Nat.mul_le_mul_right _ hdiv_lt
      _ = scalarModulus dstBytes := htop_eq.symm
  change (wrapScalarBits dstBits (scalarModulus dstBytes) % scalarModulus dstStart) +
    (chunk * scalarModulus dstStart +
      (wrapScalarBits dstBits (scalarModulus dstBytes) /
        scalarModulus (Nat.add dstStart total)) *
        scalarModulus (Nat.add dstStart total)) < scalarModulus dstBytes
  omega

theorem spliceScalarBytes_byte {dstBits chunk dstStart total dstBytes i : Nat}
    (hdst : dstBits < scalarModulus dstBytes) (hchunk : chunk < scalarModulus total)
    (_hinD : dstStart + total ≤ dstBytes) (_hi : i < dstBytes) :
    (spliceScalarBytes dstBits chunk dstStart total dstBytes / 2 ^ (8 * i)) % 256 =
      if dstStart ≤ i ∧ i < dstStart + total then
        (chunk / 2 ^ (8 * (i - dstStart))) % 256
      else
        (dstBits / 2 ^ (8 * i)) % 256 := by
  have hwrap := copyWrapScalarBits_eq_of_lt hdst
  have hlow_eq := copyScalarModulus_eq_two_pow dstStart
  have hhigh_eq : scalarModulus (Nat.add dstStart total) = 2 ^ (8 * (dstStart + total)) :=
    copyScalarModulus_eq_two_pow (dstStart + total)
  have hlow_lt : dstBits % 2 ^ (8 * dstStart) < 2 ^ (8 * dstStart) :=
    Nat.mod_lt _ (Nat.two_pow_pos _)
  have hchunk_lt : chunk < 2 ^ (8 * total) := by
    rwa [← copyScalarModulus_eq_two_pow]
  have hmid_lt :
      dstBits % 2 ^ (8 * dstStart) + chunk * 2 ^ (8 * dstStart) <
        2 ^ (8 * (dstStart + total)) := by
    have hpow : 2 ^ (8 * (dstStart + total)) = 2 ^ (8 * total) * 2 ^ (8 * dstStart) := by
      rw [← Nat.pow_add, show 8 * total + 8 * dstStart = 8 * (dstStart + total) by omega]
    have hle : chunk * 2 ^ (8 * dstStart) + 2 ^ (8 * dstStart) ≤
        2 ^ (8 * total) * 2 ^ (8 * dstStart) := by
      rw [← Nat.succ_mul]
      exact Nat.mul_le_mul_right _ hchunk_lt
    rw [hpow]; omega
  have hsum :
      spliceScalarBytes dstBits chunk dstStart total dstBytes =
        (dstBits % 2 ^ (8 * dstStart) + chunk * 2 ^ (8 * dstStart)) +
          (dstBits / 2 ^ (8 * (dstStart + total))) * 2 ^ (8 * (dstStart + total)) := by
    change wrapScalarBits dstBits (scalarModulus dstBytes) % scalarModulus dstStart +
        (chunk * scalarModulus dstStart +
          (wrapScalarBits dstBits (scalarModulus dstBytes) /
            scalarModulus (Nat.add dstStart total)) *
            scalarModulus (Nat.add dstStart total)) = _
    rw [hwrap, hlow_eq, hhigh_eq, ← Nat.add_assoc]
  rw [hsum, copyByte_of_split hmid_lt]
  by_cases hhi : i < dstStart + total
  · simp only [hhi, and_true, ↓reduceIte, copyByte_of_split hlow_lt]
    by_cases hlo : i < dstStart
    · have hnot_ge : ¬ (dstStart ≤ i) := by omega
      simp only [hlo, hnot_ge, ↓reduceIte]
      have hold_decomp : dstBits =
          dstBits % 2 ^ (8 * dstStart) + (dstBits / 2 ^ (8 * dstStart)) * 2 ^ (8 * dstStart) := by
        have h := (Nat.mod_add_div dstBits (2 ^ (8 * dstStart))).symm
        rwa [Nat.mul_comm (2 ^ (8 * dstStart))] at h
      conv => rhs; rw [hold_decomp]
      rw [copyByte_of_split hlow_lt]
      simp [hlo]
    · have hge : dstStart ≤ i := by omega
      simp [hlo, hge]
  · simp only [hhi, and_false, ↓reduceIte]
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_add,
      show 8 * (dstStart + total) + 8 * (i - (dstStart + total)) = 8 * i by omega]

private theorem copyLe_bytes_getElem (bits n i : Nat) (hi : i < (copyLe_bytes bits n).size) :
    (copyLe_bytes bits n)[i]'hi = UInt8.ofNat (bits / 2 ^ (8 * i) % 256) := by
  simp [copyLe_bytes]

private theorem copyLe_overwrite_eq_splice {dstBits chunk dstStart total dstBytes : Nat}
    (hdst : dstBits < scalarModulus dstBytes) (hchunk : chunk < scalarModulus total)
    (hinD : dstStart + total ≤ dstBytes) :
    (copyLe_bytes dstBits dstBytes).extract 0 dstStart ++ copyLe_bytes chunk total ++
      (copyLe_bytes dstBits dstBytes).extract (dstStart + total)
        (copyLe_bytes dstBits dstBytes).size =
      copyLe_bytes (spliceScalarBytes dstBits chunk dstStart total dstBytes) dstBytes := by
  have hsz_pre : ((copyLe_bytes dstBits dstBytes).extract 0 dstStart).size = dstStart := by
    simp only [Array.size_extract, copyLe_bytes_size]; omega
  have hsz_mid : (copyLe_bytes chunk total).size = total := copyLe_bytes_size chunk total
  have hsz_left :
      ((copyLe_bytes dstBits dstBytes).extract 0 dstStart ++ copyLe_bytes chunk total).size =
        dstStart + total := by
    rw [Array.size_append, hsz_pre, hsz_mid]
  apply Array.ext
  · simp only [Array.size_append, Array.size_extract, copyLe_bytes_size]; omega
  · intro i hi₁ hi₂
    have hi_dst : i < dstBytes := by rw [copyLe_bytes_size] at hi₂; exact hi₂
    have hs := spliceScalarBytes_byte hdst hchunk hinD hi_dst
    rw [copyLe_bytes_getElem _ _ i hi₂]
    by_cases hlt_hi : i < dstStart + total
    · rw [Array.getElem_append_left (by omega)]
      by_cases hlt_lo : i < dstStart
      · have hnot : ¬ (dstStart ≤ i ∧ i < dstStart + total) := by omega
        rw [Array.getElem_append_left (by omega), Array.getElem_extract,
          copyLe_bytes_getElem _ _ (0 + i) (by rw [copyLe_bytes_size]; omega),
          Nat.zero_add, hs, copyIte_neg hnot]
      · have hcond : dstStart ≤ i ∧ i < dstStart + total := by omega
        rw [Array.getElem_append_right (by omega),
          copyLe_bytes_getElem _ _ (i - ((copyLe_bytes dstBits dstBytes).extract 0 dstStart).size)
            (by rw [copyLe_bytes_size, hsz_pre]; omega),
          hsz_pre, hs, copyIte_pos hcond]
    · have hnot : ¬ (dstStart ≤ i ∧ i < dstStart + total) := by omega
      rw [Array.getElem_append_right (by omega), Array.getElem_extract,
        copyLe_bytes_getElem _ _
          (dstStart + total +
            (i - ((copyLe_bytes dstBits dstBytes).extract 0 dstStart ++
              copyLe_bytes chunk total).size))
          (by rw [copyLe_bytes_size, hsz_left]; omega),
        hsz_left, show dstStart + total + (i - (dstStart + total)) = i by omega,
        hs, copyIte_neg hnot]

private theorem copySize_mul_one (s : Miri.ABI.Size) : s.mul 1 = .ok s := by
  cases s with
  | mk b =>
    simp [Miri.ABI.Size.mul, Miri.ABI.Size.ofBytes, UInt64.mul_one, UInt64.div_one]

private theorem copyRange_endExclusive {off total : Nat} (hlt : off + total < 2 ^ 64) :
    (Miri.Memory.allocRange (Miri.ABI.Size.ofBytes (UInt64.ofNat off))
      (Miri.ABI.Size.ofBytes (UInt64.ofNat total))).endExclusive =
      .ok (Miri.ABI.Size.ofBytes (UInt64.ofNat (off + total))) := by
  have hsum : UInt64.ofNat off + UInt64.ofNat total = UInt64.ofNat (off + total) :=
    (UInt64.ofNat_add off total).symm
  have hoff_lt : off < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.le_add_right off total) hlt
  have h1 : (UInt64.ofNat off).toNat = off := UInt64.toNat_ofNat_of_lt hoff_lt
  have h2 : (UInt64.ofNat (off + total)).toNat = off + total := UInt64.toNat_ofNat_of_lt hlt
  have hnot_lt : ¬ (UInt64.ofNat (off + total) < UInt64.ofNat off) := by
    rw [UInt64.lt_iff_toNat_lt, h1, h2]; omega
  unfold Miri.Memory.AllocRange.endExclusive Miri.Memory.AllocRange.end Miri.Memory.allocRange
    Miri.ABI.Size.add Miri.ABI.Size.ofBytes
  simp only [hsum, hnot_lt, ↓reduceIte, Except.mapError]

private theorem copyRange_zero_endExclusive (s : Miri.ABI.Size) :
    (Miri.Memory.allocRange s Miri.ABI.Size.ZERO).endExclusive = .ok s := by
  cases s
  simp [Miri.Memory.AllocRange.endExclusive, Miri.Memory.AllocRange.end, Miri.Memory.allocRange,
    Miri.ABI.Size.ZERO, Miri.ABI.Size.add, Miri.ABI.Size.ofBytes, UInt64.add_zero, Except.mapError]

private theorem copyCheckedSlice_range {P E : Type} {n off total : Nat}
    (hn : ValidScalarBytes n) (hinb : off + total ≤ n)
    {A : Miri.Memory.Allocation P E}
    (hsz : A.byteSize = translateSizeBytes n)
    (hlen : (copyAlloc_raw A).size = (translateSizeBytes n).bytes.toNat) :
    Miri.Memory.Allocation.getBytesUnchecked A
      (Miri.Memory.allocRange (Miri.ABI.Size.ofBytes (UInt64.ofNat off))
        (Miri.ABI.Size.ofBytes (UInt64.ofNat total))) =
      .ok ((copyAlloc_raw A).extract off (off + total)) := by
  have hn_eq : (translateSizeBytes n).bytes.toNat = n := by
    rcases hn with rfl | rfl | rfl | rfl | rfl <;> rfl
  have hn64 : n < 2 ^ 64 := by rcases hn with rfl | rfl | rfl | rfl | rfl <;> omega
  have hlt64 : off + total < 2 ^ 64 := Nat.lt_of_le_of_lt hinb hn64
  have hoff64 : off < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.le_add_right off total) hlt64
  rw [copyAlloc_getBytesUnchecked_eq]; unfold copyAlloc_checkedSlice
  have hend := copyRange_endExclusive hlt64
  have hoff_u64 : (UInt64.ofNat off).toNat = off := UInt64.toNat_ofNat_of_lt hoff64
  have hend_u64 : (UInt64.ofNat (off + total)).toNat = off + total :=
    UInt64.toNat_ofNat_of_lt hlt64
  have hnot_gt1 : ¬ (UInt64.ofNat off > UInt64.ofNat (off + total)) := by
    rw [gt_iff_lt, UInt64.lt_iff_toNat_lt, hoff_u64, hend_u64]; omega
  have hnot_gt2 : ¬ (UInt64.ofNat (off + total) > (translateSizeBytes n).bytes) := by
    rw [gt_iff_lt, UInt64.lt_iff_toNat_lt, hend_u64, hn_eq]; omega
  have hcond_false :
      (decide (UInt64.ofNat off > UInt64.ofNat (off + total)) ||
        decide (UInt64.ofNat (off + total) > (translateSizeBytes n).bytes)) = false := by
    rw [Bool.or_eq_false_iff, decide_eq_false_iff_not, decide_eq_false_iff_not]
    exact ⟨hnot_gt1, hnot_gt2⟩
  rw [hend]
  simp only [hlen, hsz, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
    Except.mapError, bind, Except.bind, Miri.Memory.allocRange, Miri.ABI.Size.ofBytes]
  erw [hcond_false]
  simp only [Bool.false_eq_true, ↓reduceIte, hoff_u64, hend_u64, pure, Except.pure]

private theorem copyRangePtrs_new_eq_empty (range : Miri.Memory.AllocRange)
    {finish : Miri.ABI.Size} (hend : range.endExclusive = .ok finish) :
    (Miri.Memory.ProvenanceMap.new (Prov := AnnealProv)).rangePtrs range (Miri.ABI.Size.ofBytes 8) =
      .ok #[] := by
  unfold Miri.Memory.ProvenanceMap.rangePtrs
  simp only [bind, Except.bind]
  with_unfolding_all (conv => lhs; whnf)
  split
  · next r hv =>
    with_unfolding_all (conv at hv => lhs; whnf)
    rw [hend] at hv
    cases hv
  · next v hv =>
    with_unfolding_all (conv at hv => lhs; whnf)
    rw [hend] at hv
    cases hv
    with_unfolding_all rfl

private theorem copyProv_prepareCopy_new_range {off total : Nat} (hlt : off + total < 2 ^ 64)
    (raw : Array UInt8) :
    (Miri.Memory.ProvenanceMap.new (Prov := AnnealProv)).prepareCopy
      (Miri.Memory.allocRange (Miri.ABI.Size.ofBytes (UInt64.ofNat off))
        (Miri.ABI.Size.ofBytes (UInt64.ofNat total)))
      raw (Miri.ABI.Size.ofBytes 8) = .ok ⟨#[], #[]⟩ := by
  have hend := copyRange_endExclusive hlt
  have hrp1 := copyRangePtrs_new_eq_empty
    (Miri.Memory.allocRange (Miri.ABI.Size.ofBytes (UInt64.ofNat off)) Miri.ABI.Size.ZERO)
    (copyRange_zero_endExclusive _)
  have hrp2 := copyRangePtrs_new_eq_empty
    (Miri.Memory.allocRange (Miri.ABI.Size.ofBytes (UInt64.ofNat (off + total))) Miri.ABI.Size.ZERO)
    (copyRange_zero_endExclusive _)
  have htot_lt : total < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.le_add_left total off) hlt
  have htot_nat : (UInt64.ofNat total).toNat = total := UInt64.toNat_ofNat_of_lt htot_lt
  have hend_nat : (UInt64.ofNat (off + total)).toNat = off + total := UInt64.toNat_ofNat_of_lt hlt
  unfold Miri.Memory.ProvenanceMap.prepareCopy
  have hpz : ((Miri.ABI.Size.ofBytes 8).bytes == 0) = false := rfl
  simp only [hpz, Bool.false_eq_true, ↓reduceIte, bind, Except.bind]
  have hre : (Miri.Memory.allocRange (Miri.ABI.Size.ofBytes (UInt64.ofNat off))
      (Miri.ABI.Size.ofBytes (UInt64.ofNat total))).endExclusive.mapError
      Miri.Memory.ProvenanceMapError.memory =
      .ok (Miri.ABI.Size.ofBytes (UInt64.ofNat (off + total))) := by
    rw [hend]; rfl
  split
  · next e hv =>
    have h2 : Except.error e =
        Except.ok (Miri.ABI.Size.ofBytes (UInt64.ofNat (off + total))) :=
      hv.symm.trans (by with_unfolding_all exact hre)
    cases h2
  · next finish hv =>
    have h2 : Except.ok finish =
        Except.ok (Miri.ABI.Size.ofBytes (UInt64.ofNat (off + total))) :=
      hv.symm.trans (by with_unfolding_all exact hre)
    injection h2 with hfin; subst hfin
    simp only [pure, Except.pure,
      Miri.Memory.allocRange, Miri.ABI.Size.ofBytes] at hrp1 hrp2 ⊢
    by_cases hge8 : UInt64.ofNat total ≥ 8
    · have hlt7 : ¬ (UInt64.ofNat (off + total) < 7) := by
        have hle8 : (8 : UInt64) ≤ UInt64.ofNat total := hge8
        rw [UInt64.le_iff_toNat_le, htot_nat] at hle8
        rw [UInt64.lt_iff_toNat_lt, hend_nat]
        change ¬ (off + total < 7)
        change 8 ≤ total at hle8
        omega
      simp only [hge8, ↓reduceIte]
      have hsub_ok :
          (Miri.ABI.Size.sub { bytes := UInt64.ofNat (off + total) }
            { bytes := (8 : UInt64) - 1 }).mapError
            (Miri.Memory.ProvenanceMapError.memory ∘ Miri.Memory.MemoryError.sizeError) =
            .ok (Miri.ABI.Size.ofBytes (UInt64.ofNat (off + total) - 7)) := by
        simp only [Miri.ABI.Size.sub, Miri.ABI.Size.ofBytes,
          show ((8 : UInt64) - 1) = 7 from rfl, hlt7, ↓reduceIte, Except.mapError]
      split
      · next e' hv' =>
        have h3 : Except.error e' = .ok (Miri.ABI.Size.ofBytes (UInt64.ofNat (off + total) - 7)) :=
          hv'.symm.trans (by with_unfolding_all exact hsub_ok)
        cases h3
      · next adj hv' =>
        have h3 : Except.ok adj = .ok (Miri.ABI.Size.ofBytes (UInt64.ofNat (off + total) - 7)) :=
          hv'.symm.trans (by with_unfolding_all exact hsub_ok)
        injection h3 with hadj; subst hadj
        erw [hrp1, hrp2]
        with_unfolding_all rfl
    · simp only [hge8, ↓reduceIte]
      erw [hrp1, hrp2]
      with_unfolding_all rfl

private theorem copyInitMask_prepareCopy_true_range {n off total : Nat}
    (hn : ValidScalarBytes n) (hpos : 0 < total) (hinb : off + total ≤ n) :
    (Miri.Memory.InitMask.new (translateSizeBytes n) true).prepareCopy
      (Miri.Memory.allocRange (Miri.ABI.Size.ofBytes (UInt64.ofNat off))
        (Miri.ABI.Size.ofBytes (UInt64.ofNat total))) =
      .ok ⟨true, #[UInt64.ofNat total]⟩ := by
  have hn_eq : (translateSizeBytes n).bytes.toNat = n := by
    rcases hn with rfl | rfl | rfl | rfl | rfl <;> rfl
  have hn64 : n < 2 ^ 64 := by rcases hn with rfl | rfl | rfl | rfl | rfl <;> omega
  have hlt64 : off + total < 2 ^ 64 := Nat.lt_of_le_of_lt hinb hn64
  have hoff64 : off < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.le_add_right off total) hlt64
  have htot64 : total < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.le_add_left total off) hlt64
  have hend := copyRange_endExclusive hlt64
  have hoff_nat : (UInt64.ofNat off).toNat = off := UInt64.toNat_ofNat_of_lt hoff64
  have htot_nat : (UInt64.ofNat total).toNat = total := UInt64.toNat_ofNat_of_lt htot64
  have hend_nat : (UInt64.ofNat (off + total)).toNat = off + total := UInt64.toNat_ofNat_of_lt hlt64
  have hnz : (UInt64.ofNat total == 0) = false := by
    cases hb : (UInt64.ofNat total == 0)
    · rfl
    · have := eq_of_beq hb; rw [this] at htot_nat; simp at htot_nat; omega
  have hnot_oob : ¬ (UInt64.ofNat (off + total) > (translateSizeBytes n).bytes) := by
    rw [gt_iff_lt, UInt64.lt_iff_toNat_lt, hend_nat, hn_eq]; omega
  have hlt_sf : UInt64.ofNat off < UInt64.ofNat (off + total) := by
    rw [UInt64.lt_iff_toNat_lt, hoff_nat, hend_nat]; omega
  have hnot_gt_sf : ¬ (UInt64.ofNat off > UInt64.ofNat (off + total)) := by
    rw [gt_iff_lt, UInt64.lt_iff_toNat_lt, hoff_nat, hend_nat]; omega
  have hnot_le_fs : ¬ (UInt64.ofNat (off + total) ≤ UInt64.ofNat off) := by
    rw [UInt64.le_iff_toNat_le, hoff_nat, hend_nat]; omega
  have hfuel : (UInt64.ofNat (off + total)).toNat - (UInt64.ofNat off).toNat + 1 = total + 1 := by
    omega
  have hsub_u64 : UInt64.ofNat (off + total) - UInt64.ofNat off = UInt64.ofNat total := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_of_lt hlt_sf), hend_nat, hoff_nat, htot_nat]
    omega
  unfold Miri.Memory.InitMask.prepareCopy Miri.Memory.InitMask.rangeAsInitChunks
  rw [hend]
  have hlen_new : (Miri.Memory.InitMask.new (translateSizeBytes n) true).len =
      translateSizeBytes n := rfl
  simp only [Miri.Memory.allocRange, Miri.ABI.Size.ofBytes, hlen_new,
    hnz, Bool.false_eq_true, ↓reduceIte, hnot_oob, hlt_sf, Miri.Memory.InitMask.lazy_get,
    bind, Except.bind, pure, Except.pure]
  have hcond1 :
      (decide (UInt64.ofNat off > UInt64.ofNat (off + total)) ||
        decide (UInt64.ofNat (off + total) > (translateSizeBytes n).bytes)) = false := by
    rw [Bool.or_eq_false_iff, decide_eq_false_iff_not, decide_eq_false_iff_not]
    exact ⟨hnot_gt_sf, hnot_oob⟩
  have hcond2 :
      (decide (UInt64.ofNat (off + total) > UInt64.ofNat (off + total)) ||
        decide (UInt64.ofNat (off + total) > (translateSizeBytes n).bytes)) = false := by
    rw [Bool.or_eq_false_iff, decide_eq_false_iff_not, decide_eq_false_iff_not]
    exact ⟨UInt64.lt_irrefl _, hnot_oob⟩
  have hiter0 : (Miri.Memory.InitChunkIter.mk
      (Miri.Memory.InitMask.new (translateSizeBytes n) true) true
      ⟨UInt64.ofNat off⟩ ⟨UInt64.ofNat (off + total)⟩).next? =
      .ok (some (.Init ⟨UInt64.ofNat off⟩ ⟨UInt64.ofNat (off + total)⟩,
        ⟨Miri.Memory.InitMask.new (translateSizeBytes n) true, false,
          ⟨UInt64.ofNat (off + total)⟩, ⟨UInt64.ofNat (off + total)⟩⟩)) := by
    unfold Miri.Memory.InitChunkIter.next? Miri.Memory.InitMask.new
    dsimp only [bind, Except.bind, pure, Except.pure]
    erw [hcond1]
    have hnot_ge : ¬ ((UInt64.ofNat off).toNat ≥ (UInt64.ofNat (off + total)).toNat) := by
      omega
    with_unfolding_all dsimp
    simp only [↓reduceIte, hnot_le_fs]
    with_unfolding_all change
      (if (UInt64.ofNat off).toNat ≥ (UInt64.ofNat (off + total)).toNat then _ else _) = _
    rw [copyIte_neg hnot_ge]
    rfl
  have hiter1 : (Miri.Memory.InitChunkIter.mk
      (Miri.Memory.InitMask.new (translateSizeBytes n) true) false
      ⟨UInt64.ofNat (off + total)⟩ ⟨UInt64.ofNat (off + total)⟩).next? = .ok none := by
    unfold Miri.Memory.InitChunkIter.next? Miri.Memory.InitMask.new
    dsimp only [bind, Except.bind, pure, Except.pure]
    erw [hcond2]
    with_unfolding_all simp
  have htot16 : total ≤ 16 := by
    rcases hn with rfl | rfl | rfl | rfl | rfl <;> omega
  have hchunks : Miri.Memory.InitMask.collectChunks
      ⟨Miri.Memory.InitMask.new (translateSizeBytes n) true, true,
        ⟨UInt64.ofNat off⟩, ⟨UInt64.ofNat (off + total)⟩⟩ =
      .ok #[.Init ⟨UInt64.ofNat off⟩ ⟨UInt64.ofNat (off + total)⟩] := by
    unfold Miri.Memory.InitMask.collectChunks
    with_unfolding_all erw [hfuel]
    match total, hpos, htot16 with
    | 1, _, _ | 2, _, _ | 3, _, _ | 4, _, _ | 5, _, _ | 6, _, _ | 7, _, _ | 8, _, _
    | 9, _, _ | 10, _, _ | 11, _, _ | 12, _, _ | 13, _, _ | 14, _, _ | 15, _, _ | 16, _, _ =>
      with_unfolding_all (conv => lhs; whnf)
      with_unfolding_all erw [hiter0]
      dsimp only [bind, Except.bind, pure, Except.pure]
      with_unfolding_all (conv => lhs; whnf)
      with_unfolding_all erw [hiter1]
      rfl
    | k + 17, _, hle => omega
  rw [hchunks]
  have hnot_lt_fs : ¬ (UInt64.ofNat (off + total) < UInt64.ofNat off) := hnot_gt_sf
  have hcr : (Miri.Memory.InitChunk.Init ⟨UInt64.ofNat off⟩ ⟨UInt64.ofNat (off + total)⟩).range =
      .ok ⟨⟨UInt64.ofNat off⟩, ⟨UInt64.ofNat total⟩⟩ := by
    unfold Miri.Memory.InitChunk.range Miri.Memory.AllocRange.fromEndpoints Miri.ABI.Size.sub
    simp only [hnot_lt_fs, ↓reduceIte, hsub_u64, Except.mapError, bind, Except.bind,
      pure, Except.pure, Miri.ABI.Size.ofBytes]
  simp only [List.forIn_toArray, List.forIn_cons, List.forIn_nil, hcr,
    Miri.Memory.InitChunk.isInit, bind, Except.bind, pure, Except.pure]
  rfl

private theorem copyInitMask_setRange_true_range {off total n : Nat} (hn : ValidScalarBytes n)
    (hinb : off + total ≤ n) :
    (Miri.Memory.InitMask.new (translateSizeBytes n) true).setRange
      (Miri.Memory.allocRange (Miri.ABI.Size.ofBytes (UInt64.ofNat off))
        (Miri.ABI.Size.ofBytes (UInt64.ofNat total))) true =
      .ok (Miri.Memory.InitMask.new (translateSizeBytes n) true) := by
  have hn_eq : (translateSizeBytes n).bytes.toNat = n := by
    rcases hn with rfl | rfl | rfl | rfl | rfl <;> rfl
  have hn64 : n < 2 ^ 64 := by rcases hn with rfl | rfl | rfl | rfl | rfl <;> omega
  have hlt64 : off + total < 2 ^ 64 := Nat.lt_of_le_of_lt hinb hn64
  have hend := copyRange_endExclusive hlt64
  have hend_nat : (UInt64.ofNat (off + total)).toNat = off + total :=
    UInt64.toNat_ofNat_of_lt hlt64
  have hle_bytes : UInt64.ofNat (off + total) ≤ (translateSizeBytes n).bytes := by
    rw [UInt64.le_iff_toNat_le, hend_nat, hn_eq]; exact hinb
  have hnot_gt : ¬ ((UInt64.ofNat (off + total)) > (translateSizeBytes n).bytes) := by
    rw [gt_iff_lt, UInt64.lt_iff_toNat_lt, hend_nat, hn_eq]; omega
  unfold Miri.Memory.InitMask.setRange Miri.Memory.InitMask.new
  rw [hend]
  dsimp only [bind, Except.bind, Miri.Memory.allocRange, Miri.ABI.Size.ofBytes]
  by_cases hfull : UInt64.ofNat off = 0 ∧ (translateSizeBytes n).bytes ≤ UInt64.ofNat (off + total)
  · have hsz_eq : (⟨UInt64.ofNat (off + total)⟩ : Miri.ABI.Size) = translateSizeBytes n := by
      cases hs : translateSizeBytes n with
      | mk nb =>
        rw [hs] at hle_bytes hfull
        exact congrArg Miri.ABI.Size.mk (UInt64.le_antisymm hle_bytes hfull.2)
    rw [copyIte_pos hfull, hsz_eq]
    rfl
  · rw [copyIte_neg hfull]
    simp only [beq_self_eq_true, ↓reduceIte, hnot_gt, pure, Except.pure]

private theorem copyInitMask_setRange_full_true {n : Nat} (hn : ValidScalarBytes n) (bD : Bool) :
    (Miri.Memory.InitMask.new (translateSizeBytes n) bD).setRange
      (Miri.Memory.allocRange (Miri.ABI.Size.ofBytes (UInt64.ofNat 0))
        (Miri.ABI.Size.ofBytes (UInt64.ofNat n))) true =
      .ok (Miri.Memory.InitMask.new (translateSizeBytes n) true) := by
  have hts : Miri.ABI.Size.ofBytes (UInt64.ofNat n) = translateSizeBytes n := by
    rcases hn with rfl | rfl | rfl | rfl | rfl <;> rfl
  have hz : Miri.ABI.Size.ofBytes (UInt64.ofNat 0) = Miri.ABI.Size.ZERO := rfl
  rw [hz, hts]
  exact Miri.Memory.InitMask.full_overwrite_stays_lazy (translateSizeBytes n)
    (translateSizeBytes n) bD true _ (copyAlloc_allocRange_end _) rfl (UInt64.le_refl _)

private theorem copyInitMask_applyCopy_true_range {off total n : Nat}
    (hn : ValidScalarBytes n) (hpos : 0 < total) (hinb : off + total ≤ n) :
    (Miri.Memory.InitMask.new (translateSizeBytes n) true).applyCopy
      ⟨true, #[UInt64.ofNat total]⟩
      (Miri.Memory.allocRange (Miri.ABI.Size.ofBytes (UInt64.ofNat off))
        (Miri.ABI.Size.ofBytes (UInt64.ofNat total))) 1 =
      .ok (Miri.Memory.InitMask.new (translateSizeBytes n) true) := by
  have hn64 : n < 2 ^ 64 := by rcases hn with rfl | rfl | rfl | rfl | rfl <;> omega
  have htot64 : total < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.le_add_left total off)
    (Nat.lt_of_le_of_lt hinb hn64)
  have htot_nat : (UInt64.ofNat total).toNat = total := UInt64.toNat_ofNat_of_lt htot64
  have hnz : (UInt64.ofNat total == 0) = false := by
    cases hb : (UInt64.ofNat total == 0)
    · rfl
    · have := eq_of_beq hb; rw [this] at htot_nat; simp at htot_nat; omega
  have hany : (#[UInt64.ofNat total].isEmpty || #[UInt64.ofNat total].any (· == 0)) = false := by
    simp [hnz]
  have hmul := copySize_mul_one (Miri.ABI.Size.ofBytes (UInt64.ofNat total))
  unfold Miri.Memory.InitMask.applyCopy
  erw [hany]
  simp only [Bool.false_eq_true, ↓reduceIte, List.size_toArray, List.length_cons,
    List.length_nil, Nat.zero_add, Nat.le_refl, Miri.Memory.allocRange, hmul,
    Except.mapError, bind, Except.bind]
  exact copyInitMask_setRange_true_range hn hinb

/-- Same-allocation (`sameAllocation = true`, `nonoverlapping = true`,
`repeatCount = 1`) byte-range `Allocation.copyRepeatedly` on an initialized
`StackScalarAllocShape` allocation fails with `AllocError.copyRangesOverlap`
whenever the positive byte ranges `[srcStart, srcStart + total)` and
`[dstStart, dstStart + total)` overlap. -/
theorem StackScalarAllocShape.copyRepeatedly_range_overlap_err {E : Type} {n : Nat}
    (hn : ValidScalarBytes n) {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    (hrel : ScalarRel sc msc) (hsz : sc.sizeBytes = n)
    {srcStart dstStart total : Nat}
    (hpos : 0 < total) (hinS : srcStart + total ≤ n) (hinD : dstStart + total ≤ n)
    (hoverlap : ¬ (srcStart + total ≤ dstStart ∨ dstStart + total ≤ srcStart))
    {S : Miri.Memory.Allocation AnnealProv E}
    (hshapeS : StackScalarAllocShape (translateSizeBytes n) S)
    (hreadS : S.readScalar annealTargetDataLayout
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes n)) false =
      .ok (.fromScalarInt msc)) :
    ∃ S' : Miri.Memory.Allocation AnnealProv E,
      Miri.Memory.Allocation.copyRepeatedly S
        (Miri.Memory.allocRange (Miri.ABI.Size.ofBytes (UInt64.ofNat srcStart))
          (Miri.ABI.Size.ofBytes (UInt64.ofNat total)))
        (Miri.ABI.Size.ofBytes (UInt64.ofNat dstStart)) 1 (Miri.ABI.Size.ofBytes 8)
        true true S = .error .copyRangesOverlap S' := by
  obtain ⟨hmaskS, _⟩ := copyLe_decode_readScalar hn hrel hsz hshapeS hreadS
  have hn64 : n < 2 ^ 64 := by rcases hn with rfl | rfl | rfl | rfl | rfl <;> omega
  have hltS : srcStart + total < 2 ^ 64 := Nat.lt_of_le_of_lt hinS hn64
  have hltD : dstStart + total < 2 ^ 64 := Nat.lt_of_le_of_lt hinD hn64
  have hs64 : srcStart < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hltS
  have hd64 : dstStart < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hltD
  have ht64 : total < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.le_add_left _ _) hltS
  have hsliceS := copyCheckedSlice_range hn hinS hshapeS.byteSize_eq hshapeS.len_eq
  have hsliceD := copyCheckedSlice_range hn hinD hshapeS.byteSize_eq hshapeS.len_eq
  unfold Miri.Memory.Allocation.getBytesUnchecked at hsliceS hsliceD
  have hmul := copySize_mul_one (Miri.ABI.Size.ofBytes (UInt64.ofNat total))
  have hprov_prep := copyProv_prepareCopy_new_range hltS (copyAlloc_raw S)
  have hmask_prep := copyInitMask_prepareCopy_true_range hn hpos hinS
  have hmask_set := copyInitMask_setRange_true_range hn hinD
  have hendS := copyRange_endExclusive hltS
  have hendD := copyRange_endExclusive hltD
  have hclear := Miri.Memory.ProvenanceMap.clear_new (P := AnnealProv)
    (Miri.Memory.allocRange (Miri.ABI.Size.ofBytes (UInt64.ofNat dstStart))
      (Miri.ABI.Size.ofBytes (UInt64.ofNat total)))
    (copyAlloc_raw S) (Miri.ABI.Size.ofBytes 8) _ (by decide) hendD
  have hnz_tot : (UInt64.ofNat total == 0) = false := by
    have ht : (UInt64.ofNat total).toNat = total := UInt64.toNat_ofNat_of_lt ht64
    cases hb : (UInt64.ofNat total == 0)
    · rfl
    · have := eq_of_beq hb; rw [this] at ht; simp at ht; omega
  have hov_cond :
      (decide (UInt64.ofNat srcStart < UInt64.ofNat (dstStart + total)) &&
        decide (UInt64.ofNat dstStart < UInt64.ofNat (srcStart + total))) = true := by
    rw [Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff,
      UInt64.lt_iff_toNat_lt, UInt64.lt_iff_toNat_lt]
    erw [UInt64.toNat_ofNat_of_lt hs64, UInt64.toNat_ofNat_of_lt hltD,
      UInt64.toNat_ofNat_of_lt hd64, UInt64.toNat_ofNat_of_lt hltS]
    omega
  have h1 : (1 : UInt64).toNat = 1 := rfl
  rcases hshapeS with ⟨hszS, hlenS, hmutS, hprovS, _⟩
  cases S with | _ rawS szS provS maskS alignS mutS extraS nbS =>
  change szS = _ at hszS; change rawS.size = _ at hlenS
  change mutS = _ at hmutS; change provS = _ at hprovS; change maskS = _ at hmaskS
  subst hszS hmutS hprovS hmaskS
  unfold Miri.Memory.Allocation.copyRepeatedly
  rw [hsliceS]; dsimp only [bind, Pure.pure, pure, copyAlloc_raw] at hprov_prep hclear ⊢
  erw [hmul]; dsimp only [bind, Pure.pure, pure]
  rw [hsliceD, hprov_prep, hmask_prep]
  simp only [Miri.Memory.InitCopy.noBytesInit, Bool.not_true, Bool.false_and, Bool.and_false,
    Bool.false_eq_true, ↓reduceIte, prov_applyCopy_empty_fn,
    show ((1 : UInt64) == 0) = false from rfl,
    h1, Array.empty_append,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one,
    List.range'_succ, List.range'_zero, List.forIn_cons, List.forIn_nil, Id.run]
  split
  · next afterClear _ =>
    have hendD' :
        (Miri.Memory.allocRange (Miri.ABI.Size.ofBytes (UInt64.ofNat dstStart))
          (Miri.Memory.allocRange (Miri.ABI.Size.ofBytes (UInt64.ofNat srcStart))
            (Miri.ABI.Size.ofBytes (UInt64.ofNat total))).size).endExclusive =
          .ok (Miri.ABI.Size.ofBytes (UInt64.ofNat (dstStart + total))) := hendD
    dsimp only [bind, Bind.bind, pure, Pure.pure]
    simp only [Bool.and_self, ↓reduceIte, hendS, hendD']
    dsimp only [Miri.Memory.allocRange, Miri.ABI.Size.ofBytes]
    erw [hov_cond]
    exact ⟨_, rfl⟩
  · next reason updated hprep =>
    simp only [Miri.Memory.allocRange, Miri.ABI.Size.ofBytes] at hmask_set hclear
    with_unfolding_all (conv at hprep => lhs; whnf)
    with_unfolding_all erw [hsliceD] at hprep
    simp only [Miri.Memory.allocRange, Miri.ABI.Size.ofBytes, hnz_tot, bne_self_eq_false,
      Bool.false_eq_true, ↓reduceIte] at hprep
    split at hprep
    · next initialized heq =>
      with_unfolding_all (conv at heq => lhs; whnf)
      rw [hmask_set] at heq
      with_unfolding_all (conv at heq => lhs; whnf)
      injection heq with hinit_eq
      subst hinit_eq
      dsimp only [bind, Bind.bind, pure, Pure.pure] at hprep
      with_unfolding_all erw [hclear] at hprep
      with_unfolding_all cases hprep
    · next _ heq =>
      with_unfolding_all (conv at heq => lhs; whnf)
      rw [hmask_set] at heq
      with_unfolding_all (conv at heq => lhs; whnf)
      cases heq

/-- Distinct-allocation (`sameAllocation = false`) byte-range
`Allocation.copyRepeatedly` copying `dstBytes` bytes from `[srcStart, srcStart + dstBytes)`
of an initialized `srcBytes`-byte `StackScalarAllocShape` allocation `S` into
`[0, dstBytes)` of a `dstBytes`-byte `StackScalarAllocShape` allocation `D`
(whether `D` was `.init` or `.uninit`) initializes all of `D`, preserves
`StackScalarAllocShape`, and stores `sliceScalarBytes srcSc.bits srcBytes srcStart dstBytes`. -/
theorem StackScalarAllocShape.copyRepeatedly_range_whole_dst {E : Type}
    {srcBytes dstBytes : Nat}
    (hnS : ValidScalarBytes srcBytes) (hnD : ValidScalarBytes dstBytes)
    {srcSc : MirAst.ScalarInt} {srcMsc : Miri.Memory.ScalarInt}
    (hrelS : ScalarRel srcSc srcMsc) (hszSc : srcSc.sizeBytes = srcBytes)
    {srcStart : Nat} (hinS : srcStart + dstBytes ≤ srcBytes)
    {S D : Miri.Memory.Allocation AnnealProv E}
    (hshapeS : StackScalarAllocShape (translateSizeBytes srcBytes) S)
    (hshapeD : StackScalarAllocShape (translateSizeBytes dstBytes) D)
    (hreadS : S.readScalar annealTargetDataLayout
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes srcBytes)) false =
      .ok (.fromScalarInt srcMsc)) :
    ∃ (alloc' : Miri.Memory.Allocation AnnealProv E) (msc' : Miri.Memory.ScalarInt),
      Miri.Memory.Allocation.copyRepeatedly S
        (Miri.Memory.allocRange (Miri.ABI.Size.ofBytes (UInt64.ofNat srcStart))
          (Miri.ABI.Size.ofBytes (UInt64.ofNat dstBytes)))
        (Miri.ABI.Size.ofBytes (UInt64.ofNat 0)) 1 (Miri.ABI.Size.ofBytes 8)
        false true D = .ok () alloc' ∧
      ScalarRel ⟨sliceScalarBytes srcSc.bits srcBytes srcStart dstBytes, dstBytes⟩ msc' ∧
      alloc'.align = D.align ∧
      StackScalarAllocShape (translateSizeBytes dstBytes) alloc' ∧
      alloc'.initializationMask.isRangeInitialized
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes dstBytes)) = .ok (.ok ()) ∧
      alloc'.readScalar annealTargetDataLayout
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes dstBytes)) false =
        .ok (.fromScalarInt msc') := by
  obtain ⟨hmaskS, hrawS_eq⟩ := copyLe_decode_readScalar hnS hrelS hszSc hshapeS hreadS
  have hsrc_can : srcSc.bits < scalarModulus srcBytes := hszSc ▸ hrelS.canonical
  have hposD : 0 < dstBytes := by rcases hnD with rfl | rfl | rfl | rfl | rfl <;> omega
  have hd_eq : (translateSizeBytes dstBytes).bytes.toNat = dstBytes := by
    rcases hnD with rfl | rfl | rfl | rfl | rfl <;> rfl
  have hs64 : srcBytes < 2 ^ 64 := by rcases hnS with rfl | rfl | rfl | rfl | rfl <;> omega
  have hd64 : dstBytes < 2 ^ 64 := by rcases hnD with rfl | rfl | rfl | rfl | rfl <;> omega
  have hltS : srcStart + dstBytes < 2 ^ 64 := Nat.lt_of_le_of_lt hinS hs64
  have hltD : 0 + dstBytes < 2 ^ 64 := by simpa using hd64
  have hsliceS := copyCheckedSlice_range hnS hinS hshapeS.byteSize_eq hshapeS.len_eq
  have hsliceD := copyCheckedSlice_range (off := 0) (total := dstBytes) hnD (by omega)
    hshapeD.byteSize_eq hshapeD.len_eq
  unfold Miri.Memory.Allocation.getBytesUnchecked at hsliceS hsliceD
  have hmul := copySize_mul_one (Miri.ABI.Size.ofBytes (UInt64.ofNat dstBytes))
  have hprov_prep := copyProv_prepareCopy_new_range hltS (copyAlloc_raw S)
  have hmask_prep := copyInitMask_prepareCopy_true_range hnS hposD hinS
  have hendD := copyRange_endExclusive hltD
  have hmask_app := copyInitMask_applyCopy_true_range (off := 0) hnD hposD (by omega)
  have hnz_tot : (UInt64.ofNat dstBytes == 0) = false := by
    have ht : (UInt64.ofNat dstBytes).toNat = dstBytes := UInt64.toNat_ofNat_of_lt hd64
    cases hb : (UInt64.ofNat dstBytes == 0)
    · rfl
    · have := eq_of_beq hb; rw [this] at ht; simp at ht; omega
  have h1 : (1 : UInt64).toNat = 1 := rfl
  let chunk := sliceScalarBytes srcSc.bits srcBytes srcStart dstBytes
  have hex_slice : (copyAlloc_raw S).extract srcStart (srcStart + dstBytes) =
      copyLe_bytes chunk dstBytes := by
    rw [hrawS_eq]; exact copyLe_extract_eq_slice hsrc_can hinS
  obtain ⟨alloc', hcopy, halign', hshape', hmask', hraw'⟩ :
      ∃ alloc' : Miri.Memory.Allocation AnnealProv E,
        Miri.Memory.Allocation.copyRepeatedly S
          (Miri.Memory.allocRange (Miri.ABI.Size.ofBytes (UInt64.ofNat srcStart))
            (Miri.ABI.Size.ofBytes (UInt64.ofNat dstBytes)))
          (Miri.ABI.Size.ofBytes (UInt64.ofNat 0)) 1 (Miri.ABI.Size.ofBytes 8)
          false true D = .ok () alloc' ∧
        alloc'.align = D.align ∧
        StackScalarAllocShape (translateSizeBytes dstBytes) alloc' ∧
        alloc'.initializationMask = Miri.Memory.InitMask.new (translateSizeBytes dstBytes) true ∧
        copyAlloc_raw alloc' = copyLe_bytes chunk dstBytes := by
    rcases hshapeS with ⟨hszS, hlenS, hmutS, hprovS, _⟩
    rcases hshapeD with ⟨hszD, hlenD, hmutD, hprovD, ⟨bD, hmaskD⟩⟩
    have hmask_set := copyInitMask_setRange_full_true hnD bD
    have hclear := Miri.Memory.ProvenanceMap.clear_new (P := AnnealProv)
      (Miri.Memory.allocRange (Miri.ABI.Size.ofBytes (UInt64.ofNat 0))
        (Miri.ABI.Size.ofBytes (UInt64.ofNat dstBytes)))
      (copyAlloc_raw D) (Miri.ABI.Size.ofBytes 8) _ (by decide) hendD
    cases S with | _ rawS szS provS maskS alignS mutS extraS nbS =>
    cases D with | _ rawD szD provD maskD alignD mutD extraD nbD =>
    change szS = _ at hszS; change rawS.size = _ at hlenS
    change mutS = _ at hmutS; change provS = _ at hprovS; change maskS = _ at hmaskS
    change szD = _ at hszD; change rawD.size = _ at hlenD
    change mutD = _ at hmutD; change provD = _ at hprovD; change maskD = _ at hmaskD
    subst hszS hmutS hprovS hmaskS hszD hmutD hprovD hmaskD
    dsimp only [copyAlloc_raw] at hprov_prep hclear hex_slice
    have hex0 : rawD.extract 0 0 = #[] := array_extract_zero_zero rawD
    have hexN : rawD.extract dstBytes rawD.size = #[] :=
      array_extract_self_size rawD dstBytes (hlenD.trans hd_eq)
    have hd_nat : (UInt64.ofNat dstBytes).toNat = dstBytes :=
      UInt64.toNat_ofNat_of_lt hd64
    have h0_nat : (UInt64.ofNat 0).toNat = 0 := rfl
    unfold Miri.Memory.Allocation.copyRepeatedly
    rw [hsliceS]; dsimp only [bind, Pure.pure, pure]
    erw [hmul]; dsimp only [bind, Pure.pure, pure]
    rw [hsliceD, hprov_prep, hmask_prep]
    simp only [Miri.Memory.InitCopy.noBytesInit, Bool.not_true, Bool.false_and, Bool.and_false,
      Bool.false_eq_true, ↓reduceIte, prov_applyCopy_empty_fn,
      show ((1 : UInt64) == 0) = false from rfl,
      h1, Array.empty_append,
      Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one,
      List.range'_succ, List.range'_zero, List.forIn_cons, List.forIn_nil, Id.run]
    split
    · next afterClear hprep =>
      have hp := hprep
      simp only [Miri.Memory.allocRange, Miri.ABI.Size.ofBytes] at hmask_set hclear
      with_unfolding_all (conv at hp => lhs; whnf)
      with_unfolding_all erw [hsliceD] at hp
      simp only [Miri.Memory.allocRange, Miri.ABI.Size.ofBytes, hnz_tot, bne_self_eq_false,
        Bool.false_eq_true, ↓reduceIte] at hp
      split at hp
      rotate_left
      · next _ heq =>
        with_unfolding_all (conv at heq => lhs; whnf)
        rw [hmask_set] at heq
        with_unfolding_all (conv at heq => lhs; whnf)
        cases heq
      next initialized heq =>
      with_unfolding_all (conv at heq => lhs; whnf)
      rw [hmask_set] at heq
      with_unfolding_all (conv at heq => lhs; whnf)
      injection heq with hinit_eq
      subst hinit_eq
      dsimp only [bind, Bind.bind, pure, Pure.pure] at hp
      with_unfolding_all erw [hclear] at hp
      with_unfolding_all cases hp
      have h0_add : UInt64.ofNat 0 + UInt64.ofNat dstBytes = UInt64.ofNat dstBytes :=
        UInt64.zero_add _
      dsimp only [bind, Bind.bind, pure, Pure.pure]
      split
      · next afterBytes hover =>
        have ho := hover
        with_unfolding_all (conv at ho => lhs; whnf)
        dsimp only [Miri.Memory.allocRange, Miri.ABI.Size.ofBytes] at ho
        with_unfolding_all erw [h0_add, h0_nat, hd_nat, hex0, hexN, hex_slice,
          Array.empty_append, copyLe_bytes_size, bne_self_eq_false] at ho
        with_unfolding_all cases ho
        simp only [Miri.Memory.allocRange, Miri.ABI.Size.ofBytes] at hmask_app
        with_unfolding_all erw [hmask_app]
        with_unfolding_all refine ⟨_, rfl, rfl, ⟨rfl, ?_, rfl, rfl, ⟨true, rfl⟩⟩, rfl, rfl⟩
        change (copyLe_bytes chunk dstBytes).size = (translateSizeBytes dstBytes).bytes.toNat
        rw [copyLe_bytes_size, hd_eq]
      · next reason hover =>
        with_unfolding_all (conv at hover => lhs; whnf)
        dsimp only [Miri.Memory.allocRange, Miri.ABI.Size.ofBytes] at hover
        with_unfolding_all erw [h0_add, h0_nat, hd_nat, hex0, hexN, hex_slice,
          Array.empty_append, copyLe_bytes_size, bne_self_eq_false] at hover
        with_unfolding_all cases hover
    · next reason updated hprep =>
      simp only [Miri.Memory.allocRange, Miri.ABI.Size.ofBytes] at hmask_set hclear
      with_unfolding_all (conv at hprep => lhs; whnf)
      with_unfolding_all erw [hsliceD] at hprep
      simp only [Miri.Memory.allocRange, Miri.ABI.Size.ofBytes, hnz_tot, bne_self_eq_false,
        Bool.false_eq_true, ↓reduceIte] at hprep
      split at hprep
      · next initialized heq =>
        with_unfolding_all (conv at heq => lhs; whnf)
        rw [hmask_set] at heq
        with_unfolding_all (conv at heq => lhs; whnf)
        injection heq with hinit_eq
        subst hinit_eq
        dsimp only [bind, Bind.bind, pure, Pure.pure] at hprep
        with_unfolding_all erw [hclear] at hprep
        with_unfolding_all cases hprep
      · next _ heq =>
        with_unfolding_all (conv at heq => lhs; whnf)
        rw [hmask_set] at heq
        with_unfolding_all (conv at heq => lhs; whnf)
        cases heq
  obtain ⟨msc', hrel', hinit', hread'⟩ :=
    copyLe_encode_readScalar hnD (sliceScalarBytes_lt_scalarModulus _ _ _ _) hshape' hmask' hraw'
  exact ⟨alloc', msc', hcopy, hrel', halign', hshape', hinit', hread'⟩

/-- In-bounds positive byte-range `Allocation.copyRepeatedly` copying `total`
bytes from `[srcStart, srcStart + total)` of an initialized `srcBytes`-byte
`StackScalarAllocShape` allocation `S` into `[dstStart, dstStart + total)` of an
initialized `dstBytes`-byte `StackScalarAllocShape` allocation `D` (either on
distinct allocations `sameAlloc = false`, or on disjoint sub-ranges of the same
allocation `sameAlloc = true`) splices the copied bytes via `spliceScalarBytes`
and preserves `StackScalarAllocShape`. -/
theorem StackScalarAllocShape.copyRepeatedly_range_partial_dst {E : Type}
    {srcBytes dstBytes : Nat}
    (hnS : ValidScalarBytes srcBytes) (hnD : ValidScalarBytes dstBytes)
    {srcSc dstSc : MirAst.ScalarInt} {srcMsc dstMsc : Miri.Memory.ScalarInt}
    (hrelS : ScalarRel srcSc srcMsc) (hszSc : srcSc.sizeBytes = srcBytes)
    (hrelD : ScalarRel dstSc dstMsc) (hszDc : dstSc.sizeBytes = dstBytes)
    {srcStart dstStart total : Nat}
    (hpos : 0 < total) (hinS : srcStart + total ≤ srcBytes) (hinD : dstStart + total ≤ dstBytes)
    {sameAlloc : Bool}
    (hdisj : sameAlloc = true → srcStart + total ≤ dstStart ∨ dstStart + total ≤ srcStart)
    {S D : Miri.Memory.Allocation AnnealProv E}
    (hshapeS : StackScalarAllocShape (translateSizeBytes srcBytes) S)
    (hshapeD : StackScalarAllocShape (translateSizeBytes dstBytes) D)
    (hreadS : S.readScalar annealTargetDataLayout
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes srcBytes)) false =
      .ok (.fromScalarInt srcMsc))
    (hreadD : D.readScalar annealTargetDataLayout
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes dstBytes)) false =
      .ok (.fromScalarInt dstMsc)) :
    ∃ (alloc' : Miri.Memory.Allocation AnnealProv E) (msc' : Miri.Memory.ScalarInt),
      Miri.Memory.Allocation.copyRepeatedly S
        (Miri.Memory.allocRange (Miri.ABI.Size.ofBytes (UInt64.ofNat srcStart))
          (Miri.ABI.Size.ofBytes (UInt64.ofNat total)))
        (Miri.ABI.Size.ofBytes (UInt64.ofNat dstStart)) 1 (Miri.ABI.Size.ofBytes 8)
        sameAlloc true D = .ok () alloc' ∧
      ScalarRel
        ⟨spliceScalarBytes dstSc.bits (sliceScalarBytes srcSc.bits srcBytes srcStart total)
          dstStart total dstBytes, dstBytes⟩ msc' ∧
      alloc'.align = D.align ∧
      StackScalarAllocShape (translateSizeBytes dstBytes) alloc' ∧
      alloc'.initializationMask.isRangeInitialized
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes dstBytes)) = .ok (.ok ()) ∧
      alloc'.readScalar annealTargetDataLayout
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes dstBytes)) false =
        .ok (.fromScalarInt msc') := by
  obtain ⟨hmaskS, hrawS_eq⟩ := copyLe_decode_readScalar hnS hrelS hszSc hshapeS hreadS
  obtain ⟨hmaskD, hrawD_eq⟩ := copyLe_decode_readScalar hnD hrelD hszDc hshapeD hreadD
  have hsrc_can : srcSc.bits < scalarModulus srcBytes := hszSc ▸ hrelS.canonical
  have hdst_can : dstSc.bits < scalarModulus dstBytes := hszDc ▸ hrelD.canonical
  have hd_eq : (translateSizeBytes dstBytes).bytes.toNat = dstBytes := by
    rcases hnD with rfl | rfl | rfl | rfl | rfl <;> rfl
  have hs64 : srcBytes < 2 ^ 64 := by rcases hnS with rfl | rfl | rfl | rfl | rfl <;> omega
  have hd64 : dstBytes < 2 ^ 64 := by rcases hnD with rfl | rfl | rfl | rfl | rfl <;> omega
  have hltS : srcStart + total < 2 ^ 64 := Nat.lt_of_le_of_lt hinS hs64
  have hltD : dstStart + total < 2 ^ 64 := Nat.lt_of_le_of_lt hinD hd64
  have hs0_64 : srcStart < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hltS
  have hd0_64 : dstStart < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hltD
  have ht64 : total < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.le_add_left _ _) hltS
  have hsliceS := copyCheckedSlice_range hnS hinS hshapeS.byteSize_eq hshapeS.len_eq
  have hsliceD := copyCheckedSlice_range hnD hinD hshapeD.byteSize_eq hshapeD.len_eq
  unfold Miri.Memory.Allocation.getBytesUnchecked at hsliceS hsliceD
  have hmul := copySize_mul_one (Miri.ABI.Size.ofBytes (UInt64.ofNat total))
  have hprov_prep := copyProv_prepareCopy_new_range hltS (copyAlloc_raw S)
  have hmask_prep := copyInitMask_prepareCopy_true_range hnS hpos hinS
  have hmask_set := copyInitMask_setRange_true_range hnD hinD
  have hendS := copyRange_endExclusive hltS
  have hendD := copyRange_endExclusive hltD
  have hclear := Miri.Memory.ProvenanceMap.clear_new (P := AnnealProv)
    (Miri.Memory.allocRange (Miri.ABI.Size.ofBytes (UInt64.ofNat dstStart))
      (Miri.ABI.Size.ofBytes (UInt64.ofNat total)))
    (copyAlloc_raw D) (Miri.ABI.Size.ofBytes 8) _ (by decide) hendD
  have hmask_app := copyInitMask_applyCopy_true_range hnD hpos hinD
  have hnz_tot : (UInt64.ofNat total == 0) = false := by
    have ht : (UInt64.ofNat total).toNat = total := UInt64.toNat_ofNat_of_lt ht64
    cases hb : (UInt64.ofNat total == 0)
    · rfl
    · have := eq_of_beq hb; rw [this] at ht; simp at ht; omega
  have h1 : (1 : UInt64).toNat = 1 := rfl
  let chunk := sliceScalarBytes srcSc.bits srcBytes srcStart total
  let spliced := spliceScalarBytes dstSc.bits chunk dstStart total dstBytes
  have hchunk_can : chunk < scalarModulus total := sliceScalarBytes_lt_scalarModulus _ _ _ _
  have hex_slice : (copyAlloc_raw S).extract srcStart (srcStart + total) =
      copyLe_bytes chunk total := by
    rw [hrawS_eq]; exact copyLe_extract_eq_slice hsrc_can hinS
  have hover_eq : (copyAlloc_raw D).extract 0 dstStart ++ copyLe_bytes chunk total ++
      (copyAlloc_raw D).extract (dstStart + total) (copyAlloc_raw D).size =
      copyLe_bytes spliced dstBytes := by
    rw [hrawD_eq]; exact copyLe_overwrite_eq_splice hdst_can hchunk_can hinD
  obtain ⟨alloc', hcopy, halign', hshape', hmask', hraw'⟩ :
      ∃ alloc' : Miri.Memory.Allocation AnnealProv E,
        Miri.Memory.Allocation.copyRepeatedly S
          (Miri.Memory.allocRange (Miri.ABI.Size.ofBytes (UInt64.ofNat srcStart))
            (Miri.ABI.Size.ofBytes (UInt64.ofNat total)))
          (Miri.ABI.Size.ofBytes (UInt64.ofNat dstStart)) 1 (Miri.ABI.Size.ofBytes 8)
          sameAlloc true D = .ok () alloc' ∧
        alloc'.align = D.align ∧
        StackScalarAllocShape (translateSizeBytes dstBytes) alloc' ∧
        alloc'.initializationMask = Miri.Memory.InitMask.new (translateSizeBytes dstBytes) true ∧
        copyAlloc_raw alloc' = copyLe_bytes spliced dstBytes := by
    rcases hshapeS with ⟨hszS, hlenS, hmutS, hprovS, _⟩
    rcases hshapeD with ⟨hszD, hlenD, hmutD, hprovD, _⟩
    cases S with | _ rawS szS provS maskS alignS mutS extraS nbS =>
    cases D with | _ rawD szD provD maskD alignD mutD extraD nbD =>
    change szS = _ at hszS; change rawS.size = _ at hlenS
    change mutS = _ at hmutS; change provS = _ at hprovS; change maskS = _ at hmaskS
    change szD = _ at hszD; change rawD.size = _ at hlenD
    change mutD = _ at hmutD; change provD = _ at hprovD; change maskD = _ at hmaskD
    subst hszS hmutS hprovS hmaskS hszD hmutD hprovD hmaskD
    dsimp only [copyAlloc_raw] at hprov_prep hclear hex_slice hover_eq
    have hd0_nat : (UInt64.ofNat dstStart).toNat = dstStart := UInt64.toNat_ofNat_of_lt hd0_64
    have hdt_nat : (UInt64.ofNat (dstStart + total)).toNat = dstStart + total :=
      UInt64.toNat_ofNat_of_lt hltD
    unfold Miri.Memory.Allocation.copyRepeatedly
    rw [hsliceS]; dsimp only [bind, Pure.pure, pure]
    erw [hmul]; dsimp only [bind, Pure.pure, pure]
    rw [hsliceD, hprov_prep, hmask_prep]
    simp only [Miri.Memory.InitCopy.noBytesInit, Bool.not_true, Bool.false_and, Bool.and_false,
      Bool.false_eq_true, ↓reduceIte, prov_applyCopy_empty_fn,
      show ((1 : UInt64) == 0) = false from rfl,
      h1, Array.empty_append,
      Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one,
      List.range'_succ, List.range'_zero, List.forIn_cons, List.forIn_nil, Id.run]
    split
    · next afterClear hprep =>
      have hp := hprep
      simp only [Miri.Memory.allocRange, Miri.ABI.Size.ofBytes] at hmask_set hclear
      with_unfolding_all (conv at hp => lhs; whnf)
      with_unfolding_all erw [hsliceD] at hp
      simp only [Miri.Memory.allocRange, Miri.ABI.Size.ofBytes, hnz_tot, bne_self_eq_false,
        Bool.false_eq_true, ↓reduceIte] at hp
      split at hp
      rotate_left
      · next _ heq =>
        with_unfolding_all (conv at heq => lhs; whnf)
        rw [hmask_set] at heq
        with_unfolding_all (conv at heq => lhs; whnf)
        cases heq
      next initialized heq =>
      with_unfolding_all (conv at heq => lhs; whnf)
      rw [hmask_set] at heq
      with_unfolding_all (conv at heq => lhs; whnf)
      injection heq with hinit_eq
      subst hinit_eq
      dsimp only [bind, Bind.bind, pure, Pure.pure] at hp
      with_unfolding_all erw [hclear] at hp
      dsimp only [bind, Bind.bind, pure, Pure.pure]
      cases hsame : sameAlloc with
      | false =>
        simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
        with_unfolding_all cases hp
        split
        · next afterBytes hover =>
          have ho := hover
          with_unfolding_all (conv at ho => lhs; whnf)
          simp only [Miri.Memory.allocRange, Miri.ABI.Size.ofBytes] at hendD
          with_unfolding_all erw [hendD] at ho
          dsimp only [Except.mapError, bind, Except.bind, pure, Except.pure,
            Miri.Memory.allocRange, Miri.ABI.Size.ofBytes] at ho
          with_unfolding_all erw [hd0_nat, hdt_nat, hex_slice, hover_eq,
            copyLe_bytes_size, hd_eq, bne_self_eq_false] at ho
          with_unfolding_all cases ho
          simp only [Miri.Memory.allocRange, Miri.ABI.Size.ofBytes] at hmask_app
          with_unfolding_all erw [hmask_app]
          with_unfolding_all refine ⟨_, rfl, rfl, ⟨rfl, ?_, rfl, rfl, ⟨true, rfl⟩⟩, rfl, rfl⟩
          change (copyLe_bytes spliced dstBytes).size = (translateSizeBytes dstBytes).bytes.toNat
          rw [copyLe_bytes_size, hd_eq]
        · next reason hover =>
          with_unfolding_all (conv at hover => lhs; whnf)
          simp only [Miri.Memory.allocRange, Miri.ABI.Size.ofBytes] at hendD
          with_unfolding_all erw [hendD] at hover
          dsimp only [Except.mapError, bind, Except.bind, pure, Except.pure,
            Miri.Memory.allocRange, Miri.ABI.Size.ofBytes] at hover
          with_unfolding_all erw [hd0_nat, hdt_nat, hex_slice, hover_eq,
            copyLe_bytes_size, hd_eq, bne_self_eq_false] at hover
          with_unfolding_all cases hover
      | true =>
        have hov_false :
            (decide (UInt64.ofNat srcStart < UInt64.ofNat (dstStart + total)) &&
              decide (UInt64.ofNat dstStart < UInt64.ofNat (srcStart + total))) = false := by
          rw [Bool.and_eq_false_iff, decide_eq_false_iff_not, decide_eq_false_iff_not,
            UInt64.lt_iff_toNat_lt, UInt64.lt_iff_toNat_lt]
          erw [UInt64.toNat_ofNat_of_lt hs0_64, UInt64.toNat_ofNat_of_lt hltD,
            UInt64.toNat_ofNat_of_lt hd0_64, UInt64.toNat_ofNat_of_lt hltS]
          rcases hdisj hsame with hd | hd <;> omega
        have hendD' :
            (Miri.Memory.allocRange (Miri.ABI.Size.ofBytes (UInt64.ofNat dstStart))
              (Miri.Memory.allocRange (Miri.ABI.Size.ofBytes (UInt64.ofNat srcStart))
                (Miri.ABI.Size.ofBytes (UInt64.ofNat total))).size).endExclusive =
              .ok (Miri.ABI.Size.ofBytes (UInt64.ofNat (dstStart + total))) := hendD
        simp only [Bool.true_and, ↓reduceIte, hendS, hendD']
        dsimp only [Miri.Memory.allocRange, Miri.ABI.Size.ofBytes]
        erw [hov_false]
        simp only [Bool.false_eq_true, ↓reduceIte]
        with_unfolding_all cases hp
        split
        · next afterBytes hover =>
          have ho := hover
          with_unfolding_all (conv at ho => lhs; whnf)
          simp only [Miri.Memory.allocRange, Miri.ABI.Size.ofBytes] at hendD
          with_unfolding_all erw [hendD] at ho
          dsimp only [Except.mapError, bind, Except.bind, pure, Except.pure,
            Miri.Memory.allocRange, Miri.ABI.Size.ofBytes] at ho
          with_unfolding_all erw [hd0_nat, hdt_nat, hex_slice, hover_eq,
            copyLe_bytes_size, hd_eq, bne_self_eq_false] at ho
          with_unfolding_all cases ho
          simp only [Miri.Memory.allocRange, Miri.ABI.Size.ofBytes] at hmask_app
          with_unfolding_all erw [hmask_app]
          with_unfolding_all refine ⟨_, rfl, rfl, ⟨rfl, ?_, rfl, rfl, ⟨true, rfl⟩⟩, rfl, rfl⟩
          change (copyLe_bytes spliced dstBytes).size = (translateSizeBytes dstBytes).bytes.toNat
          rw [copyLe_bytes_size, hd_eq]
        · next reason hover =>
          with_unfolding_all (conv at hover => lhs; whnf)
          simp only [Miri.Memory.allocRange, Miri.ABI.Size.ofBytes] at hendD
          with_unfolding_all erw [hendD] at hover
          dsimp only [Except.mapError, bind, Except.bind, pure, Except.pure,
            Miri.Memory.allocRange, Miri.ABI.Size.ofBytes] at hover
          with_unfolding_all erw [hd0_nat, hdt_nat, hex_slice, hover_eq,
            copyLe_bytes_size, hd_eq, bne_self_eq_false] at hover
          with_unfolding_all cases hover
    · next reason updated hprep =>
      simp only [Miri.Memory.allocRange, Miri.ABI.Size.ofBytes] at hmask_set hclear
      with_unfolding_all (conv at hprep => lhs; whnf)
      with_unfolding_all erw [hsliceD] at hprep
      simp only [Miri.Memory.allocRange, Miri.ABI.Size.ofBytes, hnz_tot, bne_self_eq_false,
        Bool.false_eq_true, ↓reduceIte] at hprep
      split at hprep
      · next initialized heq =>
        with_unfolding_all (conv at heq => lhs; whnf)
        rw [hmask_set] at heq
        with_unfolding_all (conv at heq => lhs; whnf)
        injection heq with hinit_eq
        subst hinit_eq
        dsimp only [bind, Bind.bind, pure, Pure.pure] at hprep
        with_unfolding_all erw [hclear] at hprep
        with_unfolding_all cases hprep
      · next _ heq =>
        with_unfolding_all (conv at heq => lhs; whnf)
        rw [hmask_set] at heq
        with_unfolding_all (conv at heq => lhs; whnf)
        cases heq
  obtain ⟨msc', hrel', hinit', hread'⟩ :=
    copyLe_encode_readScalar hnD (spliceScalarBytes_lt_scalarModulus _ hchunk_can hinD)
      hshape' hmask' hraw'
  exact ⟨alloc', msc', hcopy, hrel', halign', hshape', hinit', hread'⟩

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
    · simp only [copySize_mul_one size, hsz, hchk]
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
    (fun _ _ => rfl) rfl hpaS (copySize_mul_one _) hpaD (fun _ => rfl)
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
  have hb := hwb.anneal_size
  have hsz : rigidTyByteSize ly ty = some elemBytes := by
    unfold rigidTyByteSize; rw [hb]
  refine ⟨hsz, ?_⟩
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
    (hsz : rigidTyKindByteSize srcPt.kind = some elemBytes)
    (hal : rigidTyKindAlignBytes srcPt.kind = some elemAlign) :
    copyPrecheck localDecls layouts src srcVal dstVal countBits =
      if countBits * elemBytes ≤ isizeMaxBytes then
        if (ptrValueAligned elemAlign srcVal && ptrValueAligned elemAlign dstVal) = true then
          if countBits * elemBytes = 0 then .zero
          else .nonZero (some (countBits * elemBytes))
        else .ub
      else .ub := by
  unfold copyPrecheck
  rw [hop]; dsimp only
  rw [hsz, hal]; dsimp only
  rw [show Nat.mul countBits elemBytes = countBits * elemBytes from rfl]
  have hmax : (9223372036854775807 : Nat) = isizeMaxBytes := rfl
  rw [hmax]
  by_cases hle : countBits * elemBytes ≤ isizeMaxBytes
  · rw [Nat.ble_eq.mpr hle]; dsimp only
    simp only [hle, ↓reduceIte]
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
        have htot0 : Nat.beq (countBits * elemBytes) 0 = false := by
          cases hb : Nat.beq (countBits * elemBytes) 0
          · rfl
          · exact absurd (Nat.eq_of_beq_eq_true hb) hz
        rw [htot0]
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

private theorem writePlaceValue_root_dead
    {locals : List LocalSlot} {borrows : List BorrowEntry} {idx : Local}
    {val : Value} {localDecls : List LocalDecl} {layouts : LayoutTable}
    (hdead : get? locals idx = some .dead) :
    writePlaceValue locals borrows { local_ := idx, projection := .nil } val localDecls layouts =
      .ub := by
  unfold writePlaceValue
  dsimp only
  rw [hdead]
  cases localDecls with
  | nil => rfl
  | cons _ _ =>
    dsimp only
    cases validateValueForTy? layouts (placeTy _ layouts { local_ := idx, projection := .nil }) val <;> rfl

private theorem writePlaceValue_root_ok
    {locals : List LocalSlot} {borrows : List BorrowEntry} {idx : Local}
    {val : Value} {localDecls : List LocalDecl} {layouts : LayoutTable}
    {slot_d : LocalSlot}
    (hval : validateValueForTy? layouts
      (placeTy localDecls layouts { local_ := idx, projection := .nil }) val = true)
    (hslot : get? locals idx = some slot_d)
    (hne : slot_d ≠ .dead) :
    writePlaceValue locals borrows { local_ := idx, projection := .nil } val localDecls layouts =
      .ok (locals.set idx (.init val)) := by
  have hlt : idx < locals.length := by
    rw [get?_eq_getElem?] at hslot
    exact (List.getElem?_eq_some_iff.mp hslot).1
  have hset := set?_eq_some_set hlt (.init val)
  unfold writePlaceValue
  dsimp only
  cases localDecls with
  | nil =>
    dsimp only; rw [hslot]
    cases slot_d with
    | dead => exact absurd rfl hne
    | uninit => dsimp only; rw [hset]
    | init _ => dsimp only; rw [hset]
  | cons _ _ =>
    dsimp only; rw [hval]; dsimp only; rw [hslot]
    cases slot_d with
    | dead => exact absurd rfl hne
    | uninit => dsimp only; rw [hset]
    | init _ => dsimp only; rw [hset]

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
    {pointeeTy : Ty} {idxS idxD : Nat}
    (_hcaller : s.memory.callerLocals = .nil)
    (hprim : IsPrimScalarTy pointeeTy)
    (hopS : operandPointeeTy localDecls layouts src = some { kind := pointeeTy.kind, layoutIdx := idxS })
    (hopD : operandPointeeTy localDecls layouts dst = some { kind := pointeeTy.kind, layoutIdx := idxD })
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
        rw [writePlaceValue_root_dead hdead_d, hdead_d]

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
    {pointeeTy : Ty} {idxS idxD : Nat} {sc_s : MirAst.ScalarInt} {slot_d : LocalSlot}
    {decl_d : LocalDecl}
    (hprim : IsPrimScalarTy pointeeTy)
    (hopS : operandPointeeTy localDecls layouts src = some { kind := pointeeTy.kind, layoutIdx := idxS })
    (hopD : operandPointeeTy localDecls layouts dst = some { kind := pointeeTy.kind, layoutIdx := idxD })
    (hne_tag : srcPtr.tag ≠ dstPtr.tag)
    (hne_loc : e_s.localIdx ≠ e_d.localIdx)
    (hslot_s : get? s.frame.locals e_s.localIdx = some (.init (.scalar sc_s)))
    (hslot_d : get? s.frame.locals e_d.localIdx = some slot_d)
    (hne_dead_d : slot_d ≠ .dead)
    (hdecl_d : get? localDecls e_d.localIdx = some decl_d)
    (hbool_d : decl_d.ty.kind = .bool → sc_s.sizeBytes = 1 ∧ (sc_s.bits = 0 ∨ sc_s.bits = 1))
    (hchar_d : decl_d.ty.kind = .char → sc_s.sizeBytes = 4 ∧ isValidCharCode sc_s.bits = true) :
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
  have hval_ok :
      validateValueForTy? layouts
        (placeTy localDecls layouts { local_ := e_d.localIdx, projection := .nil })
        (.scalar sc_s) = true := by
    unfold placeTy resolveProjectedTy
    rw [hdecl_d]
    rcases decl_d with ⟨_, ⟨kind_d, _⟩, _⟩
    dsimp only at hbool_d hchar_d ⊢
    unfold validateValueForTy?
    cases hk : kind_d with
    | bool =>
      obtain ⟨hsz, hbits⟩ := hbool_d hk
      rcases hbits with h0 | h1
      · simp [hsz, h0]
      · simp [hsz, h1]
    | char =>
      obtain ⟨hsz, hch⟩ := hchar_d hk
      simp [hsz, hch]
    | _ => rfl
  unfold evalCopySingleDirect
  dsimp only [AllocMapEntry.toBorrowEntry]
  rw [hb_tag]; dsimp only
  rw [hb_loc]; dsimp only
  rw [hslot_s]; dsimp only [readProjectedValue]
  rw [hopS, hopD]; dsimp only
  rw [sameRigidTyShape_of_primScalar hprim]; dsimp only
  rw [writePlaceValue_root_ok hval_ok hslot_d hne_dead_d]

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
    (evalCopyNonOverlappingLM4_2 s (.copy ⟨srcIdx, []⟩) (.copy ⟨dstIdx, []⟩) countOp
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
      evalCopyNonOverlappingLM4_2 s (.copy ⟨srcIdx, []⟩) (.copy ⟨dstIdx, []⟩) countOp
          body.localDecls body.layouts =
        evalCopyNonOverlappingWithCountLM4_2 s (.copy ⟨srcIdx, []⟩) (.copy ⟨dstIdx, []⟩)
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
    unfold evalCopyNonOverlappingLM4_2; rw [evalOperand_copy_local_eq, hsrc_dead]
  · -- `src` is `.uninit`.
    have ha_ub : evalCopyNonOverlappingLM4_2 s (.copy ⟨srcIdx, []⟩) (.copy ⟨dstIdx, []⟩) countOp
        body.localDecls body.layouts = MirStepNode.fail .ub := by
      unfold evalCopyNonOverlappingLM4_2; rw [evalOperand_copy_local_eq, hsrc_un]
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
      unfold evalCopyNonOverlappingLM4_2; rw [ha₁]; dsimp only
      rw [evalOperand_copy_local_eq, hdst_dead]
    · have ha_ub : evalCopyNonOverlappingLM4_2 s (.copy ⟨srcIdx, []⟩) (.copy ⟨dstIdx, []⟩) countOp
          body.localDecls body.layouts = MirStepNode.fail .ub := by
        unfold evalCopyNonOverlappingLM4_2; rw [ha₁]; dsimp only
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
        unfold evalCopyNonOverlappingLM4_2; rw [ha₁]; dsimp only; rw [ha₂]; dsimp only; rw [ha₃]
      · left; refine ⟨?_, _, _, by
          unfold copyMiriStmtAction
          rw [EStateM.bind_eq_ok hm₁, EStateM.bind_eq_ok hm₂, EStateM.bind_eq_ok hm₃]
          exact copyAnnealCopyEval_uninit_count _ _ _ _⟩
        unfold evalCopyNonOverlappingLM4_2; rw [ha₁]; dsimp only; rw [ha₂]; dsimp only; rw [ha₃]
      · obtain ⟨hrelC, hszC⟩ := copyImmediateRel_of_integral hcountInt hrelI_c
        obtain ⟨hc_opt, hc_pre⟩ := copyScalarVal?_of_evalOperand_ok hcountOp ha₃
        right
        refine ⟨.scalar sc_s, _, .scalar sc_d, _, countSc, mcount, tf₃,
          .scalar sc_s hsz8_s, .scalar sc_d hsz8_d,
          (by intro _ h; cases h), (by intro _ h; cases h),
          hrelC, hszC, hc_opt, hc_pre, ?_, ?_, hstate₃⟩
        · unfold evalCopyNonOverlappingLM4_2; rw [ha₁]; dsimp only; rw [ha₂]; dsimp only; rw [ha₃]
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
        unfold evalCopyNonOverlappingLM4_2; rw [ha₁]; dsimp only; rw [ha₂]; dsimp only; rw [ha₃]
      · left; refine ⟨?_, _, _, by
          unfold copyMiriStmtAction
          rw [EStateM.bind_eq_ok hm₁, EStateM.bind_eq_ok hm₂, EStateM.bind_eq_ok hm₃]
          exact copyAnnealCopyEval_uninit_count _ _ _ _⟩
        unfold evalCopyNonOverlappingLM4_2; rw [ha₁]; dsimp only; rw [ha₂]; dsimp only; rw [ha₃]
      · obtain ⟨hrelC, hszC⟩ := copyImmediateRel_of_integral hcountInt hrelI_c
        obtain ⟨hc_opt, hc_pre⟩ := copyScalarVal?_of_evalOperand_ok hcountOp ha₃
        right
        refine ⟨.scalar sc_s, _, .ptr dstPtr 8, _, countSc, mcount, tf₃,
          .scalar sc_s hsz8_s, .ptr dstPtr mptr_d hptrRel_d,
          (by intro _ h; cases h),
          (by intro p h; injection h with h1 _; subst h1; exact hdst_ptr),
          hrelC, hszC, hc_opt, hc_pre, ?_, ?_, hstate₃⟩
        · unfold evalCopyNonOverlappingLM4_2; rw [ha₁]; dsimp only; rw [ha₂]; dsimp only; rw [ha₃]
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
      unfold evalCopyNonOverlappingLM4_2; rw [ha₁]; dsimp only
      rw [evalOperand_copy_local_eq, hdst_dead]
    · have ha_ub : evalCopyNonOverlappingLM4_2 s (.copy ⟨srcIdx, []⟩) (.copy ⟨dstIdx, []⟩) countOp
          body.localDecls body.layouts = MirStepNode.fail .ub := by
        unfold evalCopyNonOverlappingLM4_2; rw [ha₁]; dsimp only
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
        unfold evalCopyNonOverlappingLM4_2; rw [ha₁]; dsimp only; rw [ha₂]; dsimp only; rw [ha₃]
      · left; refine ⟨?_, _, _, by
          unfold copyMiriStmtAction
          rw [EStateM.bind_eq_ok hm₁, EStateM.bind_eq_ok hm₂, EStateM.bind_eq_ok hm₃]
          exact copyAnnealCopyEval_uninit_count _ _ _ _⟩
        unfold evalCopyNonOverlappingLM4_2; rw [ha₁]; dsimp only; rw [ha₂]; dsimp only; rw [ha₃]
      · obtain ⟨hrelC, hszC⟩ := copyImmediateRel_of_integral hcountInt hrelI_c
        obtain ⟨hc_opt, hc_pre⟩ := copyScalarVal?_of_evalOperand_ok hcountOp ha₃
        right
        refine ⟨.ptr srcPtr 8, _, .scalar sc_d, _, countSc, mcount, tf₃,
          .ptr srcPtr mptr_s hptrRel_s, .scalar sc_d hsz8_d,
          (by intro p h; injection h with h1 _; subst h1; exact hsrc_ptr),
          (by intro _ h; cases h),
          hrelC, hszC, hc_opt, hc_pre, ?_, ?_, hstate₃⟩
        · unfold evalCopyNonOverlappingLM4_2; rw [ha₁]; dsimp only; rw [ha₂]; dsimp only; rw [ha₃]
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
        unfold evalCopyNonOverlappingLM4_2; rw [ha₁]; dsimp only; rw [ha₂]; dsimp only; rw [ha₃]
      · left; refine ⟨?_, _, _, by
          unfold copyMiriStmtAction
          rw [EStateM.bind_eq_ok hm₁, EStateM.bind_eq_ok hm₂, EStateM.bind_eq_ok hm₃]
          exact copyAnnealCopyEval_uninit_count _ _ _ _⟩
        unfold evalCopyNonOverlappingLM4_2; rw [ha₁]; dsimp only; rw [ha₂]; dsimp only; rw [ha₃]
      · obtain ⟨hrelC, hszC⟩ := copyImmediateRel_of_integral hcountInt hrelI_c
        obtain ⟨hc_opt, hc_pre⟩ := copyScalarVal?_of_evalOperand_ok hcountOp ha₃
        right
        refine ⟨.ptr srcPtr 8, _, .ptr dstPtr 8, _, countSc, mcount, tf₃,
          .ptr srcPtr mptr_s hptrRel_s, .ptr dstPtr mptr_d hptrRel_d,
          (by intro p h; injection h with h1 _; subst h1; exact hsrc_ptr),
          (by intro p h; injection h with h1 _; subst h1; exact hdst_ptr),
          hrelC, hszC, hc_opt, hc_pre, ?_, ?_, hstate₃⟩
        · unfold evalCopyNonOverlappingLM4_2; rw [ha₁]; dsimp only; rw [ha₂]; dsimp only; rw [ha₃]
        · unfold copyMiriStmtAction
          rw [EStateM.bind_eq_ok hm₁, EStateM.bind_eq_ok hm₂, EStateM.bind_eq_ok hm₃]
          exact copyAnnealCopyEval_init _ (hpt_m _) hpt.wb.miri_size hpt.wb.lt_u64 (hsrcP _)
            (copyIntrinsicPointer_fromPointer mptr_d (translateTy dstDecl.ty body.layouts) _)
            hrelC hszC

/-- Target-local compatibility for `copy_nonoverlapping::<T>` on tracked
primitive-scalar stack allocations: either both `src` and `dst` point to
integral stack locals (`i8..i128` / `isize` / `u8..u128` / `usize` of any
widths, supporting cross-type byte copies such as `*const u8 -> *mut u64`,
multi-element counts, non-zero byte offsets, partial byte splices, whole-local
`.uninit` initialization, and disjoint sub-ranges of the same local), or both
point to stack locals of the exact pointee type `pointeeKind` (including `.bool`
and `.char`). -/
def CopyTargetCompatible (decl_s decl_d : LocalDecl) (pointeeKind : RigidTy) : Prop :=
  ((∃ srcKind, IsIntegralTy decl_s.ty srcKind) ∧
    (∃ dstKind, IsIntegralTy decl_d.ty dstKind)) ∨
  (decl_s.ty.kind = pointeeKind ∧ decl_d.ty.kind = pointeeKind)

private theorem IsIntegralTy.size_spec {ty : Ty} {kind : Miri.MIR.IntegerKind}
    (ly : LayoutTable) (h : IsIntegralTy ty kind) :
    rigidTyByteSize ly ty = some (integerKindByteWidth kind) ∧
    (translateTy ty ly).layout.size = translateSizeBytes (integerKindByteWidth kind) ∧
    ValidScalarBytes (integerKindByteWidth kind) := by
  have hp := h.prim
  rw [← hp.translateTy_layoutIdx ly]
  rcases h with ⟨it, hk⟩ | ⟨ut, hk⟩
  · cases it <;>
      (simp only [rigidTyByteSize, rigidTyKindByteSize, hk, translateIntTy,
        integerKindByteWidth, translateTy, translateSizeBytes]
       exact ⟨rfl, rfl, by simp [ValidScalarBytes]⟩)
  · cases ut <;>
      (simp only [rigidTyByteSize, rigidTyKindByteSize, hk, translateUintTy,
        integerKindByteWidth, translateTy, translateSizeBytes]
       exact ⟨rfl, rfl, by simp [ValidScalarBytes]⟩)

private theorem intCastTargetBytes_eq_none_of_not_integral {ty : Ty}
    (hprim : IsPrimScalarTy ty) (hnot : ¬ ∃ k, IsIntegralTy ty k) :
    intCastTargetBytes ty.kind = none := by
  rcases hprim with hk | hk | ⟨it, hk⟩ | ⟨ut, hk⟩
  · rw [hk]; rfl
  · rw [hk]; rfl
  · exact absurd ⟨translateIntTy it, .int it hk⟩ hnot
  · exact absurd ⟨translateUintTy ut, .uint ut hk⟩ hnot

private theorem placeTy_root_eq {localDecls : List LocalDecl} {layouts : LayoutTable}
    {idx : Local} {decl : LocalDecl} (hdecl : get? localDecls idx = some decl) :
    placeTy localDecls layouts { local_ := idx, projection := .nil } = some decl.ty := by
  unfold placeTy resolveProjectedTy
  rw [hdecl]

private theorem writeCopyRootSlot_local_ok {s : MachineState} {dstPtr : ProvenancePtr}
    {dstIdx : Local} {slot_d newSlot : LocalSlot}
    (hslot_d : get? s.frame.locals dstIdx = some slot_d)
    (hne_dead : slot_d ≠ .dead) :
    writeCopyRootSlot s s.frame.locals dstPtr dstIdx newSlot =
      MirStepNode.step
        (advanceStmt s (s.frame.locals.set dstIdx newSlot)
          { s.memory with
            borrows := invalidateConflictingBorrows s.memory.borrows dstIdx
              (some dstPtr.tag) }) := by
  have hlt_d : dstIdx < s.frame.locals.length := by
    rw [get?_eq_getElem?] at hslot_d
    exact (List.getElem?_eq_some_iff.mp hslot_d).1
  have hset_d := set?_eq_some_set hlt_d newSlot
  unfold writeCopyRootSlot
  rw [hslot_d]
  cases slot_d with
  | dead => exact absurd rfl hne_dead
  | uninit => dsimp only; rw [hset_d]
  | init _ => dsimp only; rw [hset_d]

private theorem evalCopyRootIntScalars_dead_src_ub {s : MachineState}
    {srcPtr dstPtr : ProvenancePtr} {e_s e_d : AllocMapEntry}
    {srcBytes dstBytes total : Nat}
    (hdead : get? s.frame.locals e_s.localIdx = some .dead) :
    evalCopyRootIntScalars s s.frame.locals srcPtr dstPtr
      e_s.toBorrowEntry e_d.toBorrowEntry srcBytes dstBytes total =
      MirStepNode.fail .ub := by
  unfold evalCopyRootIntScalars lookupCopyRootSlot
  dsimp only [AllocMapEntry.toBorrowEntry]
  rw [hdead]

private theorem evalCopyRootIntScalars_dead_dst_ub {s : MachineState}
    {srcPtr dstPtr : ProvenancePtr} {e_s e_d : AllocMapEntry}
    {srcBytes dstBytes total : Nat} {slot_s : LocalSlot}
    (hslot_s : get? s.frame.locals e_s.localIdx = some slot_s)
    (hdead_d : get? s.frame.locals e_d.localIdx = some .dead) :
    evalCopyRootIntScalars s s.frame.locals srcPtr dstPtr
      e_s.toBorrowEntry e_d.toBorrowEntry srcBytes dstBytes total =
      MirStepNode.fail .ub := by
  unfold evalCopyRootIntScalars lookupCopyRootSlot
  dsimp only [AllocMapEntry.toBorrowEntry]
  rw [hslot_s, hdead_d]
  cases slot_s <;> rfl

private theorem evalCopyRootIntScalars_uninit_src_ub {s : MachineState}
    {srcPtr dstPtr : ProvenancePtr} {e_s e_d : AllocMapEntry}
    {srcBytes dstBytes total : Nat}
    (huninit : get? s.frame.locals e_s.localIdx = some .uninit) :
    evalCopyRootIntScalars s s.frame.locals srcPtr dstPtr
      e_s.toBorrowEntry e_d.toBorrowEntry srcBytes dstBytes total =
      MirStepNode.fail .ub := by
  have hls : lookupCopyRootSlot s s.frame.locals e_s.localIdx = some .uninit := by
    unfold lookupCopyRootSlot; rw [huninit]
  unfold evalCopyRootIntScalars
  dsimp only [AllocMapEntry.toBorrowEntry]
  rw [hls]
  cases lookupCopyRootSlot s s.frame.locals e_d.localIdx with
  | none => rfl
  | some d => cases d <;> rfl

private theorem evalCopyNonOverlappingWithCount_of_perm_or_single
    {s : MachineState} {src dst : MirAst.Operand}
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    {srcPt : Ty} {elemBytes elemAlign : Nat}
    {srcPtr dstPtr : ProvenancePtr} {e_s e_d : AllocMapEntry}
    {decl_s decl_d : LocalDecl}
    (hopS : operandPointeeTy localDecls layouts src = some srcPt)
    (hszPt : rigidTyKindByteSize srcPt.kind = some elemBytes)
    (halPt : rigidTyKindAlignBytes srcPt.kind = some elemAlign)
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
    evalCopyNonOverlappingWithCountLM4_2 s src dst localDecls layouts
        (.ptr srcPtr 8) (.ptr dstPtr 8) 1 s.frame.locals =
      match e_s.perm, e_d.perm with
      | .disabled, _ => MirStepNode.fail .ub
      | _, .frozen => MirStepNode.fail .ub
      | _, .disabled => MirStepNode.fail .ub
      | _, _ =>
        match intCastTargetBytes decl_s.ty.kind, intCastTargetBytes decl_d.ty.kind with
        | some srcBytes, some dstBytes =>
          evalCopyRootIntScalars s s.frame.locals srcPtr dstPtr
            e_s.toBorrowEntry e_d.toBorrowEntry srcBytes dstBytes elemBytes
        | _, _ =>
          evalCopySingleDirect s src dst localDecls layouts srcPtr dstPtr
            e_s.toBorrowEntry e_d.toBorrowEntry s.frame.locals := by
  have hle1 : 1 * elemBytes ≤ isizeMaxBytes := by simpa using hle
  have hnz1 : ¬ (1 * elemBytes = 0) := by omega
  have hplS := placeTy_root_eq (layouts := layouts) hdeclS
  have hplD := placeTy_root_eq (layouts := layouts) hdeclD
  unfold evalCopyNonOverlappingWithCountLM4_2
  rw [copyPrecheck_eq _ _ 1 hopS hszPt halPt]
  simp only [hle1, halS, halD, Bool.and_self, hnz1, ↓reduceIte]
  rw [lookupCopyBorrowChecked_root hlookS hdeclS hszS,
    lookupCopyBorrowChecked_root hlookD hdeclD hszD]
  simp only [Nat.one_mul, hoffS, hoffD, Nat.zero_add, Nat.le_refl, ↓reduceIte]
  dsimp only [AllocMapEntry.toBorrowEntry]
  simp only [hdeclS, hdeclD]
  cases e_s.perm <;> cases e_d.perm <;>
    (cases intCastTargetBytes decl_s.ty.kind <;> cases intCastTargetBytes decl_d.ty.kind <;>
      simp [Bool.and, hplS, hplD, hszS, hszD, Nat.beq_refl])

private theorem evalCopyNonOverlappingWithCount_int_reduce
    {s : MachineState} {src dst : MirAst.Operand}
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    {srcPt : Ty} {elemBytes elemAlign countBits srcBytes dstBytes : Nat}
    {srcPtr dstPtr : ProvenancePtr} {e_s e_d : AllocMapEntry}
    {decl_s decl_d : LocalDecl}
    (hopS : operandPointeeTy localDecls layouts src = some srcPt)
    (hszPt : rigidTyKindByteSize srcPt.kind = some elemBytes)
    (halPt : rigidTyKindAlignBytes srcPt.kind = some elemAlign)
    (hle : countBits * elemBytes ≤ isizeMaxBytes)
    (hpos : 0 < countBits * elemBytes)
    (halS : ptrValueAligned elemAlign (.ptr srcPtr 8) = true)
    (halD : ptrValueAligned elemAlign (.ptr dstPtr 8) = true)
    (hlookS : lookupBorrow s.memory.borrows srcPtr.tag = some e_s.toBorrowEntry)
    (hdeclS : get? localDecls e_s.localIdx = some decl_s)
    (hszS : rigidTyByteSize layouts decl_s.ty = some srcBytes)
    (hintS : intCastTargetBytes decl_s.ty.kind = some srcBytes)
    (hlookD : lookupBorrow s.memory.borrows dstPtr.tag = some e_d.toBorrowEntry)
    (hdeclD : get? localDecls e_d.localIdx = some decl_d)
    (hszD : rigidTyByteSize layouts decl_d.ty = some dstBytes)
    (hintD : intCastTargetBytes decl_d.ty.kind = some dstBytes) :
    evalCopyNonOverlappingWithCountLM4_2 s src dst localDecls layouts
        (.ptr srcPtr 8) (.ptr dstPtr 8) countBits s.frame.locals =
      if srcPtr.offsetBytes + countBits * elemBytes ≤ srcBytes ∧
          dstPtr.offsetBytes + countBits * elemBytes ≤ dstBytes then
        match e_s.perm, e_d.perm with
        | .disabled, _ => MirStepNode.fail .ub
        | _, .frozen => MirStepNode.fail .ub
        | _, .disabled => MirStepNode.fail .ub
        | _, _ =>
          evalCopyRootIntScalars s s.frame.locals srcPtr dstPtr
            e_s.toBorrowEntry e_d.toBorrowEntry srcBytes dstBytes (countBits * elemBytes)
      else MirStepNode.fail .ub := by
  have hnz : ¬ (countBits * elemBytes = 0) := by omega
  unfold evalCopyNonOverlappingWithCountLM4_2
  rw [copyPrecheck_eq _ _ countBits hopS hszPt halPt]
  simp only [hle, halS, halD, Bool.and_self, hnz, ↓reduceIte]
  rw [lookupCopyBorrowChecked_root hlookS hdeclS hszS,
    lookupCopyBorrowChecked_root hlookD hdeclD hszD]
  by_cases hinS : srcPtr.offsetBytes + countBits * elemBytes ≤ srcBytes
  · by_cases hinD : dstPtr.offsetBytes + countBits * elemBytes ≤ dstBytes
    · simp only [hinS, hinD, and_self, ↓reduceIte]
      dsimp only [AllocMapEntry.toBorrowEntry]
      cases e_s.perm <;> cases e_d.perm <;> simp [hdeclS, hdeclD, hintS, hintD]
    · simp [hinS, hinD]
  · simp [hinS]

private theorem evalCopyNonOverlappingWithCount_nonint_dead_ub
    {s : MachineState} {src dst : MirAst.Operand}
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    {srcPt : Ty} {elemBytes elemAlign countBits : Nat}
    {srcPtr dstPtr : ProvenancePtr} {e_s e_d : AllocMapEntry}
    {decl_s decl_d : LocalDecl}
    (hopS : operandPointeeTy localDecls layouts src = some srcPt)
    (hszPt : rigidTyKindByteSize srcPt.kind = some elemBytes)
    (halPt : rigidTyKindAlignBytes srcPt.kind = some elemAlign)
    (hle : countBits * elemBytes ≤ isizeMaxBytes)
    (hpos : 0 < countBits * elemBytes)
    (halS : ptrValueAligned elemAlign (.ptr srcPtr 8) = true)
    (halD : ptrValueAligned elemAlign (.ptr dstPtr 8) = true)
    (hlookS : lookupBorrow s.memory.borrows srcPtr.tag = some e_s.toBorrowEntry)
    (hdeclS : get? localDecls e_s.localIdx = some decl_s)
    (hszS : rigidTyByteSize layouts decl_s.ty = some elemBytes)
    (hnonS : intCastTargetBytes decl_s.ty.kind = none)
    (hlookD : lookupBorrow s.memory.borrows dstPtr.tag = some e_d.toBorrowEntry)
    (hdeclD : get? localDecls e_d.localIdx = some decl_d)
    (hszD : rigidTyByteSize layouts decl_d.ty = some elemBytes)
    (hsingle : srcPtr.offsetBytes = 0 → dstPtr.offsetBytes = 0 → countBits = 1 →
      evalCopySingleDirect s src dst localDecls layouts srcPtr dstPtr
        e_s.toBorrowEntry e_d.toBorrowEntry s.frame.locals = MirStepNode.fail .ub) :
    evalCopyNonOverlappingWithCountLM4_2 s src dst localDecls layouts
        (.ptr srcPtr 8) (.ptr dstPtr 8) countBits s.frame.locals =
      MirStepNode.fail .ub := by
  have hnz : ¬ (countBits * elemBytes = 0) := by omega
  have hplS := placeTy_root_eq (layouts := layouts) hdeclS
  have hplD := placeTy_root_eq (layouts := layouts) hdeclD
  unfold evalCopyNonOverlappingWithCountLM4_2
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
        | (simp only [hdeclS, hdeclD, hnonS, hplS, hplD, hszS, hszD,
             hoffS, hoffD, hcnt1, Nat.one_mul, Nat.beq_refl, Bool.and_self]
           exact hsd)
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
  locals, out-of-bounds offsets/counts, or overlapping byte ranges on the same
  stack allocation (UB in both);
* positive-byte copies across arbitrary `CopyTargetCompatible` primitive-scalar
  stack byte ranges (cross-type integer copies, `count > 1`, non-zero offsets,
  partial byte splices, whole-local `.uninit` initialization, same-local
  disjoint sub-ranges, and `.bool`/`.char` same-type copies) with valid Tree
  Borrows permissions (copies the scalar & raw bytes and preserves
  `StateRelLM3_1` under `copyNextAllocMap`). -/
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
    (htgt_compat : ∀ srcPtr dstPtr e_s e_d decl_s decl_d,
      get? s.frame.locals srcIdx = some (.init (.ptr srcPtr 8)) →
      get? s.frame.locals dstIdx = some (.init (.ptr dstPtr 8)) →
      e_s ∈ allocMap → e_s.tag = srcPtr.tag →
      e_d ∈ allocMap → e_d.tag = dstPtr.tag →
      get? body.localDecls e_s.localIdx = some decl_s →
      get? body.localDecls e_d.localIdx = some decl_d →
      0 < elemBytes →
      CopyTargetCompatible decl_s decl_d pointeeTy.kind)
    (hlive_ok : ∀ srcPtr dstPtr countSc e_s e_d decl_s decl_d srcBytes dstBytes,
      get? s.frame.locals srcIdx = some (.init (.ptr srcPtr 8)) →
      get? s.frame.locals dstIdx = some (.init (.ptr dstPtr 8)) →
      WriteBytesScalarPreVal s.frame.locals countOp countSc →
      0 < countSc.bits * elemBytes →
      countSc.bits * elemBytes ≤ isizeMaxBytes →
      e_s ∈ allocMap → e_s.tag = srcPtr.tag →
      e_d ∈ allocMap → e_d.tag = dstPtr.tag →
      get? body.localDecls e_s.localIdx = some decl_s →
      get? body.localDecls e_d.localIdx = some decl_d →
      rigidTyByteSize body.layouts decl_s.ty = some srcBytes →
      rigidTyByteSize body.layouts decl_d.ty = some dstBytes →
      srcPtr.offsetBytes + countSc.bits * elemBytes ≤ srcBytes →
      dstPtr.offsetBytes + countSc.bits * elemBytes ≤ dstBytes →
      get? s.frame.locals e_s.localIdx ≠ some .dead →
      get? s.frame.locals e_d.localIdx ≠ some .dead →
      e_s.perm ≠ .disabled ∧
        (e_d.perm = .active ∨ e_d.perm = .reserved) ∧
        get? s.frame.locals e_s.localIdx ≠ some .uninit ∧
        ((dstPtr.offsetBytes = 0 ∧ countSc.bits * elemBytes = dstBytes) ∨
          get? s.frame.locals e_d.localIdx ≠ some .uninit)) :
    StepRelLM3_1 body m
      (copyNextAllocMap s.frame.locals allocMap dstIdx countOp elemBytes)
      (stepMirFnLM4_2 body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, _, _⟩ := id hstate
  have hanneal_step : stepMirFnLM4_2 body s =
      evalCopyNonOverlappingLM4_2 s (.copy ⟨srcIdx, []⟩) (.copy ⟨dstIdx, []⟩) countOp
        body.localDecls body.layouts := by
    rw [stepMirFnLM4_2_eq_of_not_other body s hcal hphase]
    simp only [hbb, hstmt]; rfl
  have mk_ub : ∀ {m' msg},
      evalCopyNonOverlappingLM4_2 s (.copy ⟨srcIdx, []⟩) (.copy ⟨dstIdx, []⟩) countOp
        body.localDecls body.layouts = MirStepNode.fail .ub →
      copyMiriStmtAction body srcIdx dstIdx countOp m = .error (.undefinedBehavior msg) m' →
      StepRelLM3_1 body m
        (copyNextAllocMap s.frame.locals allocMap dstIdx countOp elemBytes)
        (stepMirFnLM4_2 body s)
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
        rw [ha_red]; unfold evalCopyNonOverlappingWithCountLM4_2
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
          rw [ha_red]; unfold evalCopyNonOverlappingWithCountLM4_2
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
          · have ha_zero : evalCopyNonOverlappingLM4_2 s (.copy ⟨srcIdx, []⟩) (.copy ⟨dstIdx, []⟩)
                countOp body.localDecls body.layouts =
                MirStepNode.step (advanceStmt s s.frame.locals) := by
              rw [ha_red]; unfold evalCopyNonOverlappingWithCountLM4_2
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
              rw [ha_red]; unfold evalCopyNonOverlappingWithCountLM4_2
              rw [copyPrecheck_eq _ _ _ hopS hpt.wb.anneal_size hpt.anneal_align]
              simp [hle, hs_al, hd_al, hz]
            | ptr srcPtr p_s hptrRel_s =>
              cases hargD with
              | scalar sc_d _ =>
                obtain ⟨msg, herr⟩ := annealMemCopy_dst_withoutProvenance_err
                  p_s.withOptionalProvenance (UInt64.ofNat sc_d.bits) hpos hle
                  { m with stack := ⟨#[tf₃]⟩ }
                refine mk_ub ?_ (hm_mem.trans herr)
                rw [ha_red]; unfold evalCopyNonOverlappingWithCountLM4_2
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
                have hcompat := htgt_compat srcPtr dstPtr e_s e_d decl_s decl_d
                  hsrc_loc_eq hdst_loc_eq he_s het_s he_d het_d hdecl_s hdecl_d helem_pos
                have hlook_s : lookupBorrow s.memory.borrows srcPtr.tag = some e_s.toBorrowEntry := by
                  rw [← het_s]; exact (halloc.borrow_sync e_s he_s).2
                have hlook_d : lookupBorrow s.memory.borrows dstPtr.tag = some e_d.toBorrowEntry := by
                  rw [← het_d]; exact (halloc.borrow_sync e_d he_d).2
                have hbase_s : m.machine.lookupBaseAddr srcId = some (annealStackBaseAddr srcId) := by
                  rw [← hea_s]; exact (halloc.base_addr_valid e_s he_s).2.2
                have hbase_d : m.machine.lookupBaseAddr dstId = some (annealStackBaseAddr dstId) := by
                  rw [← hea_d]; exact (halloc.base_addr_valid e_d he_d).2.2
                obtain ⟨slot_s, mls_s, _, _, hslot_s, hmls_s, _, hloc_s⟩ := hfr₃.lookup_local hdecl_s
                obtain ⟨slot_d, mls_d, _, _, hslot_d, hmls_d, _, hloc_d⟩ := hfr₃.lookup_local hdecl_d
                -- Split on integral target pair vs. non-integral same-type (`.bool` / `.char`).
                by_cases hint_pair :
                    (∃ srcKind, IsIntegralTy decl_s.ty srcKind) ∧
                    (∃ dstKind, IsIntegralTy decl_d.ty dstKind)
                · -- Case A: Integral target pair (`evalCopyRootIntScalars`).
                  obtain ⟨⟨srcKind, hsrcInt⟩, ⟨dstKind, hdstInt⟩⟩ := hint_pair
                  let srcBytes := integerKindByteWidth srcKind
                  let dstBytes := integerKindByteWidth dstKind
                  obtain ⟨hrig_s, htr_s, hvalid_s⟩ := hsrcInt.size_spec body.layouts
                  obtain ⟨hrig_d, htr_d, hvalid_d⟩ := hdstInt.size_spec body.layouts
                  have hint_s : intCastTargetBytes decl_s.ty.kind = some srcBytes :=
                    hsrcInt.intCastTargetBytes_eq
                  have hint_d : intCastTargetBytes decl_d.ty.kind = some dstBytes :=
                    hdstInt.intCastTargetBytes_eq
                  have ha_int := evalCopyNonOverlappingWithCount_int_reduce hopS
                    hpt.wb.anneal_size hpt.anneal_align hle hpos hs_al hd_al
                    hlook_s hdecl_s hrig_s hint_s hlook_d hdecl_d hrig_d hint_d
                    (dst := .copy ⟨dstIdx, []⟩)
                  -- 4a(int). Dead source local.
                  by_cases hd_s : slot_s = .dead
                  · subst hd_s
                    have hnone_s : m.machine.memory.live.find? (fun x => x.1 == srcId) = none := by
                      rw [← hea_s]; exact (halloc.local_alloc_sync tf₃ rfl e_s he_s).2 hslot_s
                    obtain ⟨msg, herr⟩ := annealMemCopy_src_dead_err
                      (st := { m with stack := ⟨#[tf₃]⟩ }) srcId srcBorTag srcPtr.offsetBytes _
                      hid_s hoff_s hbase_s hnone_s hpos hle
                    refine mk_ub ?_ (hm_mem.trans herr)
                    rw [ha_red, ha_int]
                    split
                    · cases e_s.perm <;> cases e_d.perm <;>
                        first | rfl | exact evalCopyRootIntScalars_dead_src_ub hslot_s
                    · rfl
                  · -- 4b(int). Dead destination local.
                    by_cases hd_d : slot_d = .dead
                    · subst hd_d
                      have hnone_d : m.machine.memory.live.find? (fun x => x.1 == dstId) = none := by
                        rw [← hea_d]; exact (halloc.local_alloc_sync tf₃ rfl e_d he_d).2 hslot_d
                      obtain ⟨msg, herr⟩ := annealMemCopy_dst_dead_err
                        (st := { m with stack := ⟨#[tf₃]⟩ }) _ dstId dstBorTag dstPtr.offsetBytes
                        hid_d hoff_d hbase_d hnone_d hpos hle
                      refine mk_ub ?_ (hm_mem.trans herr)
                      rw [ha_red, ha_int]
                      split
                      · cases e_s.perm <;> cases e_d.perm <;>
                          first | rfl | exact evalCopyRootIntScalars_dead_dst_ub hslot_s hslot_d
                      · rfl
                    · -- 4c(int). Both target locals are live.
                      obtain ⟨⟨lay_s, hlay_s⟩, hsc_only_s, hshape_fn_s⟩ :=
                        (halloc.local_alloc_sync tf₃ rfl e_s he_s).1 slot_s hslot_s hd_s
                      obtain ⟨srcLA, hfind_s', _, _, hshape_s'⟩ := hshape_fn_s decl_s hdecl_s
                      have hfind_s : m.machine.memory.live.find? (fun x => x.1 == srcId) =
                          some (srcId, srcLA) := by rw [← hea_s]; exact hfind_s'
                      have hshape_s : StackScalarAllocShape (translateSizeBytes srcBytes)
                          srcLA.allocation := htr_s ▸ hshape_s'
                      obtain ⟨⟨lay_d, hlay_d⟩, hsc_only_d, hshape_fn_d⟩ :=
                        (halloc.local_alloc_sync tf₃ rfl e_d he_d).1 slot_d hslot_d hd_d
                      obtain ⟨dstLA, hfind_d', hkind_d, halign_d, hshape_d'⟩ :=
                        hshape_fn_d decl_d hdecl_d
                      have hfind_d : m.machine.memory.live.find? (fun x => x.1 == dstId) =
                          some (dstId, dstLA) := by rw [← hea_d]; exact hfind_d'
                      have hshape_d : StackScalarAllocShape (translateSizeBytes dstBytes)
                          dstLA.allocation := htr_d ▸ hshape_d'
                      have hts_s : (translateSizeBytes srcBytes).bytes.toNat = srcBytes := by
                        dsimp only [srcBytes]
                        rcases hvalid_s with h0 | h0 | h0 | h0 | h0 <;> (rw [h0]; rfl)
                      have hts_d : (translateSizeBytes dstBytes).bytes.toNat = dstBytes := by
                        dsimp only [dstBytes]
                        rcases hvalid_d with h0 | h0 | h0 | h0 | h0 <;> (rw [h0]; rfl)
                      have hsz_la_s : srcLA.allocation.byteSize.bytes.toNat = srcBytes := by
                        rw [hshape_s.byteSize_eq, hts_s]
                      have hsz_la_d : dstLA.allocation.byteSize.bytes.toNat = dstBytes := by
                        rw [hshape_d.byteSize_eq, hts_d]
                      let total := countSc.bits * elemBytes
                      -- 4d(int). Source OOB.
                      by_cases hinS : srcPtr.offsetBytes + total ≤ srcBytes
                      · -- 4e(int). Destination OOB.
                        by_cases hinD : dstPtr.offsetBytes + total ≤ dstBytes
                        · -- 4f(int). Both in-bounds (`srcOff + total ≤ srcBytes` and `dstOff + total ≤ dstBytes`).
                          have hlive_s_ne : get? s.frame.locals e_s.localIdx ≠ some .dead := by
                            rw [hslot_s]; intro h; injection h with h; exact hd_s h
                          have hlive_d_ne : get? s.frame.locals e_d.localIdx ≠ some .dead := by
                            rw [hslot_d]; intro h; injection h with h; exact hd_d h
                          obtain ⟨hperm_s, hperm_d, hnot_un_s, hdst_init_cond⟩ :=
                            hlive_ok srcPtr dstPtr countSc e_s e_d decl_s decl_d srcBytes dstBytes
                              hsrc_loc_eq hdst_loc_eq hc_pre hpos hle he_s het_s he_d het_d
                              hdecl_s hdecl_d hrig_s hrig_d hinS hinD hlive_s_ne hlive_d_ne
                          have hs_init : ∃ sc_s, slot_s = .init (.scalar sc_s) := by
                            cases hs : slot_s with
                            | dead => exact absurd hs hd_s
                            | uninit => exact absurd (hslot_s.trans (congrArg some hs)) hnot_un_s
                            | init v =>
                              obtain ⟨sc_s, rfl⟩ := hsc_only_s v hs
                              exact ⟨sc_s, rfl⟩
                          obtain ⟨sc_s, rfl⟩ := hs_init
                          have hmls_s_eq : mls_s = ⟨.live (.indirect (stackAllocPlace e_s.allocId)), lay_s⟩ := by
                            rw [hlay_s] at hmls_s; exact Option.some.inj hmls_s.symm
                          have hnz_sz_s : (translateTy decl_s.ty body.layouts).layout.size ≠
                              Miri.ABI.Size.ZERO := by
                            rw [htr_s]; intro h
                            have := congrArg (fun z : Miri.ABI.Size => z.bytes.toNat) h
                            rw [hts_s] at this
                            have hs_pos : 0 < srcBytes := by
                              rcases hvalid_s with h0 | h0 | h0 | h0 | h0 <;> omega
                            change srcBytes = 0 at this; omega
                          obtain ⟨_, hsc_spec⟩ := hloc_s.indirect_stackAllocPlace_spec hmls_s_eq
                            (halloc.base_addr_valid e_s he_s).2.2 hfind_s'
                            (halloc.live_key_unique e_s he_s) hnz_sz_s
                          obtain ⟨hsz_sc_eq, _, _, msc_s, hrel_sc, hread_s⟩ := hsc_spec sc_s rfl
                          have hsc_bytes : sc_s.sizeBytes = srcBytes := by
                            have h := htr_s.symm.trans hsz_sc_eq
                            have h1 : (translateSizeBytes sc_s.sizeBytes).bytes.toNat = sc_s.sizeBytes := by
                              rcases hrel_sc.validBytes with h0 | h0 | h0 | h0 | h0 <;> (rw [h0]; rfl)
                            have h2 := congrArg (fun z : Miri.ABI.Size => z.bytes.toNat) h
                            rw [hts_s, h1] at h2
                            exact h2.symm
                          rw [htr_s] at hread_s
                          have ha_step1 : evalCopyNonOverlappingWithCountLM4_2 s (.copy ⟨srcIdx, []⟩)
                              (.copy ⟨dstIdx, []⟩) body.localDecls body.layouts
                              (.ptr srcPtr 8) (.ptr dstPtr 8) countSc.bits s.frame.locals =
                              evalCopyRootIntScalars s s.frame.locals srcPtr dstPtr
                                e_s.toBorrowEntry e_d.toBorrowEntry srcBytes dstBytes total := by
                            rw [ha_int, copyIte_pos ⟨hinS, hinD⟩]
                            rcases hperm_d with hp_d | hp_d <;> rw [hp_d] <;>
                              (cases hp_s : e_s.perm <;> first | rfl | exact absurd hp_s hperm_s)
                          have hmap_eq : copyNextAllocMap s.frame.locals allocMap dstIdx countOp
                              elemBytes =
                              updateAllocMapOnWrite allocMap e_d.localIdx (some dstPtr.tag) := by
                            unfold copyNextAllocMap writeBytesNextAllocMap
                            rw [hc_opt]
                            simp only [hz, ↓reduceIte, hdst_loc_eq,
                              copyLookupAllocMapByTag_of_mem_nodup halloc.tags_nodup he_d het_d]
                          -- 4g(int). Same-local overlapping byte ranges vs. non-overlapping.
                          by_cases hov : e_s.localIdx = e_d.localIdx ∧
                              ¬ (srcPtr.offsetBytes + total ≤ dstPtr.offsetBytes ∨
                                dstPtr.offsetBytes + total ≤ srcPtr.offsetBytes)
                          · obtain ⟨hsame, hoverlap⟩ := hov
                            have heq_id : srcId = dstId := by
                              rw [← hea_s, ← hea_d]
                              exact halloc.local_to_alloc_unique e_s he_s e_d he_d hsame
                            have hdecl_eq : decl_s = decl_d :=
                              Option.some.inj (hdecl_s.symm.trans (hsame ▸ hdecl_d))
                            have hsz_eq_sd : srcBytes = dstBytes := by
                              have h := hrig_s.symm.trans (hdecl_eq ▸ hrig_d)
                              exact Option.some.inj h
                            have hinD' : dstPtr.offsetBytes + total ≤ srcBytes := hsz_eq_sd ▸ hinD
                            obtain ⟨S', hcopy_err⟩ := hshape_s.copyRepeatedly_range_overlap_err
                              hvalid_s hrel_sc hsc_bytes hpos hinS hinD' hoverlap hread_s
                            have hm_eq := annealMemCopy_live_inbounds_eq
                              (st := { m with stack := ⟨#[tf₃]⟩ })
                              srcId srcBorTag srcPtr.offsetBytes srcLA
                              srcId dstBorTag dstPtr.offsetBytes srcLA
                              hid_s hoff_s hbase_s hfind_s (hsz_la_s ▸ hinS)
                              hid_s hoff_d hbase_s hfind_s (hsz_la_s ▸ hinD') hpos hle
                            rw [beq_self_eq_true, hcopy_err] at hm_eq
                            obtain ⟨m_err, hm_err⟩ : ∃ m_err,
                                copyMiriStmtAction body srcIdx dstIdx countOp m =
                                  .error (.undefinedBehavior
                                    "copy_nonoverlapping called on overlapping ranges") m_err :=
                              ⟨_, by rw [hm_mem, ← heq_id]; exact hm_eq⟩
                            refine mk_ub ?_ hm_err
                            have hls_ov : lookupCopyRootSlot s s.frame.locals e_s.localIdx =
                                some (.init (.scalar sc_s)) := by
                              unfold lookupCopyRootSlot; rw [hslot_s]
                            have hld_ov : lookupCopyRootSlot s s.frame.locals e_d.localIdx =
                                some slot_d := by
                              unfold lookupCopyRootSlot; rw [hslot_d]
                            rw [ha_red, ha_step1]
                            unfold evalCopyRootIntScalars
                            dsimp only [AllocMapEntry.toBorrowEntry]
                            have hov_true :
                                (Nat.beq e_s.localIdx e_d.localIdx &&
                                  !(Nat.ble (srcPtr.offsetBytes + total) dstPtr.offsetBytes ||
                                    Nat.ble (dstPtr.offsetBytes + total) srcPtr.offsetBytes)) = true := by
                              rw [hsame, Nat.beq_refl, Bool.true_and, Bool.not_eq_true',
                                Bool.or_eq_false_iff]
                              refine ⟨?_, ?_⟩
                              · exact copyBle_eq_false_of_gt (fun h => hoverlap (Or.inl h))
                              · exact copyBle_eq_false_of_gt (fun h => hoverlap (Or.inr h))
                            rw [hls_ov, hld_ov]
                            cases hd_case : slot_d with
                            | dead => exact absurd hd_case hd_d
                            | uninit | init _ =>
                              dsimp only
                              rw [hsc_bytes, Nat.beq_refl]
                              dsimp only
                              rw [show Nat.add srcPtr.offsetBytes total = srcPtr.offsetBytes + total from rfl,
                                show Nat.add dstPtr.offsetBytes total = dstPtr.offsetBytes + total from rfl,
                                show Bool.and (Nat.beq e_s.localIdx e_d.localIdx)
                                  (Bool.not (Bool.or (Nat.ble (srcPtr.offsetBytes + total) dstPtr.offsetBytes)
                                    (Nat.ble (dstPtr.offsetBytes + total) srcPtr.offsetBytes))) =
                                  (Nat.beq e_s.localIdx e_d.localIdx &&
                                    !(Nat.ble (srcPtr.offsetBytes + total) dstPtr.offsetBytes ||
                                      Nat.ble (dstPtr.offsetBytes + total) srcPtr.offsetBytes)) from rfl,
                                hov_true]
                          · -- Non-overlapping byte ranges!
                            have hov_false :
                                (Nat.beq e_s.localIdx e_d.localIdx &&
                                  !(Nat.ble (srcPtr.offsetBytes + total) dstPtr.offsetBytes ||
                                    Nat.ble (dstPtr.offsetBytes + total) srcPtr.offsetBytes)) = false := by
                              cases hb_same : Nat.beq e_s.localIdx e_d.localIdx
                              · rfl
                              · have hsame := Nat.eq_of_beq_eq_true hb_same
                                have hdisj : srcPtr.offsetBytes + total ≤ dstPtr.offsetBytes ∨
                                    dstPtr.offsetBytes + total ≤ srcPtr.offsetBytes :=
                                  Classical.byContradiction (fun hn => hov ⟨hsame, hn⟩)
                                rw [Bool.true_and, Bool.not_eq_false']
                                rcases hdisj with hd | hd
                                · rw [Nat.ble_eq.mpr hd]; rfl
                                · rw [Nat.ble_eq.mpr hd, Bool.or_true]
                            have hid_d' : e_d.allocId.value.toNat < 2 ^ 32 := hea_d.symm ▸ hid_d
                            have hbase_d' : m.machine.lookupBaseAddr e_d.allocId =
                                some (annealStackBaseAddr e_d.allocId) :=
                              (halloc.base_addr_valid e_d he_d).2.2
                            -- Split on whole-destination overwrite (`dstStart = 0 ∧ total = dstBytes`) vs. partial splice.
                            by_cases hwhole : dstPtr.offsetBytes = 0 ∧ total = dstBytes
                            · obtain ⟨hoff0_d, htot_eq⟩ := hwhole
                              have hne_loc : e_s.localIdx ≠ e_d.localIdx := by
                                intro hsame
                                have hdecl_eq : decl_s = decl_d :=
                                  Option.some.inj (hdecl_s.symm.trans (hsame ▸ hdecl_d))
                                have hsz_eq_sd : srcBytes = dstBytes :=
                                  Option.some.inj (hrig_s.symm.trans (hdecl_eq ▸ hrig_d))
                                apply hov
                                refine ⟨hsame, ?_⟩
                                intro hdisj
                                omega
                              have hne_id : srcId ≠ e_d.allocId := by
                                intro hid
                                exact hne_loc (halloc.alloc_to_local_injective e_s he_s e_d he_d
                                  (hea_s.trans hid))
                              have hinS_d : srcPtr.offsetBytes + dstBytes ≤ srcBytes := htot_eq ▸ hinS
                              obtain ⟨alloc', msc', hcopy_ok, hrel_new, halign_a', hshape_a',
                                hinit_a', hread_a'⟩ :=
                                hshape_s.copyRepeatedly_range_whole_dst hvalid_s hvalid_d
                                  hrel_sc hsc_bytes hinS_d hshape_d hread_s
                              have hm_eq := annealMemCopy_live_inbounds_eq
                                (st := { m with stack := ⟨#[tf₃]⟩ })
                                srcId srcBorTag srcPtr.offsetBytes srcLA
                                e_d.allocId dstBorTag 0 dstLA
                                hid_s hoff_s hbase_s hfind_s (hsz_la_s ▸ hinS_d)
                                hid_d' (by decide) hbase_d' hfind_d' (by omega)
                                (htot_eq ▸ hpos) (htot_eq ▸ hle)
                              rw [beq_false_of_ne hne_id, hcopy_ok] at hm_eq
                              have hm_act : copyMiriStmtAction body srcIdx dstIdx countOp m =
                                  .ok () { stack := ⟨#[tf₃]⟩, machine := { m.machine with
                                    memory := { m.machine.memory with
                                      live := (m.machine.memory.live.filter (fun x => x.1 != e_d.allocId)).push
                                        (e_d.allocId, ⟨dstLA.kind, alloc'⟩) } } } := by
                                rw [hm_mem, show countSc.bits * elemBytes = dstBytes from htot_eq,
                                  hoff0_d, ← hea_d]
                                exact hm_eq
                              let newSc : MirAst.ScalarInt :=
                                ⟨sliceScalarBytes sc_s.bits srcBytes srcPtr.offsetBytes dstBytes,
                                  dstBytes⟩
                              have ha_ok : evalCopyNonOverlappingLM4_2 s (.copy ⟨srcIdx, []⟩)
                                  (.copy ⟨dstIdx, []⟩) countOp body.localDecls body.layouts =
                                  MirStepNode.step
                                    (advanceStmt s (s.frame.locals.set e_d.localIdx (.init (.scalar newSc)))
                                      { s.memory with
                                        borrows := (updateAllocMapOnWrite allocMap e_d.localIdx
                                          (some dstPtr.tag)).map AllocMapEntry.toBorrowEntry }) := by
                                have hls_ok : lookupCopyRootSlot s s.frame.locals e_s.localIdx =
                                    some (.init (.scalar sc_s)) := by
                                  unfold lookupCopyRootSlot; rw [hslot_s]
                                have hld_ok : lookupCopyRootSlot s s.frame.locals e_d.localIdx =
                                    some slot_d := by
                                  unfold lookupCopyRootSlot; rw [hslot_d]
                                rw [ha_red, ha_step1]
                                unfold evalCopyRootIntScalars
                                dsimp only [AllocMapEntry.toBorrowEntry]
                                rw [hls_ok, hld_ok]
                                cases hd_case : slot_d with
                                | dead => exact absurd hd_case hd_d
                                | uninit | init _ =>
                                  dsimp only
                                  rw [hsc_bytes, Nat.beq_refl]
                                  dsimp only
                                  rw [show Nat.add srcPtr.offsetBytes total = srcPtr.offsetBytes + total from rfl,
                                    show Nat.add dstPtr.offsetBytes total = dstPtr.offsetBytes + total from rfl,
                                    show Bool.and (Nat.beq e_s.localIdx e_d.localIdx)
                                      (Bool.not (Bool.or (Nat.ble (srcPtr.offsetBytes + total) dstPtr.offsetBytes)
                                        (Nat.ble (dstPtr.offsetBytes + total) srcPtr.offsetBytes))) =
                                      (Nat.beq e_s.localIdx e_d.localIdx &&
                                        !(Nat.ble (srcPtr.offsetBytes + total) dstPtr.offsetBytes ||
                                          Nat.ble (dstPtr.offsetBytes + total) srcPtr.offsetBytes)) from rfl,
                                    hov_false]
                                  dsimp only
                                  simp only [hoff0_d, htot_eq, Nat.beq_refl, Bool.and_self]
                                  rw [writeCopyRootSlot_local_ok (hslot_d.trans (congrArg some hd_case)) (by nofun),
                                    hbor, copyInvalidateConflictingBorrows_eq_map_updateAllocMapOnWrite]
                              have hpost := StateRelLM3_1.advance_write_deref_scalar hstate₃ rfl
                                (fun x => x.updateOnWrite e_d.localIdx (some dstPtr.tag))
                                (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
                                he_d hdecl_d hprim_d hslot_d hd_d hfind_d' hkind_d halign_d
                                hrel_new htr_d
                                (fun h => absurd h hdstInt.ne_bool)
                                (fun h => absurd h hdstInt.ne_char)
                                halign_a' hshape_a' hinit_a' hread_a'
                              rw [hanneal_step, ha_ok, hmap_eq,
                                copyStep_miri_ok hframes hfr.body_eq hfr.location_eq hfr₃.location_eq
                                  hbb hstmt hm_act]
                              exact .step _ _ hpost
                            · -- Partial destination splice (`¬(dstStart = 0 ∧ total = dstBytes)`).
                              have hnot_un_d : get? s.frame.locals e_d.localIdx ≠ some .uninit := by
                                rcases hdst_init_cond with hw | hnu
                                · exact absurd hw hwhole
                                · exact hnu
                              have hd_init : ∃ sc_d, slot_d = .init (.scalar sc_d) := by
                                cases hd_case : slot_d with
                                | dead => exact absurd hd_case hd_d
                                | uninit => exact absurd (hslot_d.trans (congrArg some hd_case)) hnot_un_d
                                | init v =>
                                  obtain ⟨sc_d, rfl⟩ := hsc_only_d v hd_case
                                  exact ⟨sc_d, rfl⟩
                              obtain ⟨sc_d, hsd_eq⟩ := hd_init
                              have hmls_d_eq : mls_d = ⟨.live (.indirect (stackAllocPlace e_d.allocId)), lay_d⟩ := by
                                rw [hlay_d] at hmls_d; exact Option.some.inj hmls_d.symm
                              have hnz_sz_d : (translateTy decl_d.ty body.layouts).layout.size ≠
                                  Miri.ABI.Size.ZERO := by
                                rw [htr_d]; intro h
                                have := congrArg (fun z : Miri.ABI.Size => z.bytes.toNat) h
                                rw [hts_d] at this
                                have hd_pos : 0 < dstBytes := by
                                  rcases hvalid_d with h0 | h0 | h0 | h0 | h0 <;> omega
                                change dstBytes = 0 at this; omega
                              obtain ⟨_, hsc_spec_d⟩ := hloc_d.indirect_stackAllocPlace_spec hmls_d_eq
                                (halloc.base_addr_valid e_d he_d).2.2 hfind_d'
                                (halloc.live_key_unique e_d he_d) hnz_sz_d
                              obtain ⟨hsz_scd_eq, _, _, msc_d, hrel_scd, hread_d⟩ := hsc_spec_d sc_d hsd_eq
                              have hscd_bytes : sc_d.sizeBytes = dstBytes := by
                                have h := htr_d.symm.trans hsz_scd_eq
                                have h1 : (translateSizeBytes sc_d.sizeBytes).bytes.toNat = sc_d.sizeBytes := by
                                  rcases hrel_scd.validBytes with h0 | h0 | h0 | h0 | h0 <;> (rw [h0]; rfl)
                                have h2 := congrArg (fun z : Miri.ABI.Size => z.bytes.toNat) h
                                rw [hts_d, h1] at h2
                                exact h2.symm
                              rw [htr_d] at hread_d
                              have hdisj_same : (srcId == e_d.allocId) = true →
                                  srcPtr.offsetBytes + total ≤ dstPtr.offsetBytes ∨
                                  dstPtr.offsetBytes + total ≤ srcPtr.offsetBytes := by
                                intro hbeq
                                have hid_eq : e_s.allocId = e_d.allocId := hea_s.trans (eq_of_beq hbeq)
                                have hsame := halloc.alloc_to_local_injective e_s he_s e_d he_d hid_eq
                                exact Classical.byContradiction (fun hn => hov ⟨hsame, hn⟩)
                              obtain ⟨alloc', msc', hcopy_ok, hrel_new, halign_a', hshape_a',
                                hinit_a', hread_a'⟩ :=
                                hshape_s.copyRepeatedly_range_partial_dst hvalid_s hvalid_d
                                  hrel_sc hsc_bytes hrel_scd hscd_bytes hpos hinS hinD hdisj_same
                                  hshape_d hread_s hread_d
                              have hm_eq := annealMemCopy_live_inbounds_eq
                                (st := { m with stack := ⟨#[tf₃]⟩ })
                                srcId srcBorTag srcPtr.offsetBytes srcLA
                                e_d.allocId dstBorTag dstPtr.offsetBytes dstLA
                                hid_s hoff_s hbase_s hfind_s (hsz_la_s ▸ hinS)
                                hid_d' hoff_d hbase_d' hfind_d' (hsz_la_d ▸ hinD) hpos hle
                              rw [hcopy_ok] at hm_eq
                              have hm_act : copyMiriStmtAction body srcIdx dstIdx countOp m =
                                  .ok () { stack := ⟨#[tf₃]⟩, machine := { m.machine with
                                    memory := { m.machine.memory with
                                      live := (m.machine.memory.live.filter (fun x => x.1 != e_d.allocId)).push
                                        (e_d.allocId, ⟨dstLA.kind, alloc'⟩) } } } := by
                                rw [hm_mem, ← hea_d]; exact hm_eq
                              have hwhole_false :
                                  (Nat.beq dstPtr.offsetBytes 0 && Nat.beq total dstBytes) = false := by
                                cases h1 : Nat.beq dstPtr.offsetBytes 0
                                · rfl
                                · cases h2 : Nat.beq total dstBytes
                                  · rfl
                                  · exact absurd ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2⟩ hwhole
                              let newSc : MirAst.ScalarInt :=
                                ⟨spliceScalarBytes sc_d.bits
                                  (sliceScalarBytes sc_s.bits srcBytes srcPtr.offsetBytes total)
                                  dstPtr.offsetBytes total dstBytes, dstBytes⟩
                              have ha_ok : evalCopyNonOverlappingLM4_2 s (.copy ⟨srcIdx, []⟩)
                                  (.copy ⟨dstIdx, []⟩) countOp body.localDecls body.layouts =
                                  MirStepNode.step
                                    (advanceStmt s (s.frame.locals.set e_d.localIdx (.init (.scalar newSc)))
                                      { s.memory with
                                        borrows := (updateAllocMapOnWrite allocMap e_d.localIdx
                                          (some dstPtr.tag)).map AllocMapEntry.toBorrowEntry }) := by
                                have hls_ok : lookupCopyRootSlot s s.frame.locals e_s.localIdx =
                                    some (.init (.scalar sc_s)) := by
                                  unfold lookupCopyRootSlot; rw [hslot_s]
                                have hld_ok : lookupCopyRootSlot s s.frame.locals e_d.localIdx =
                                    some (.init (.scalar sc_d)) := by
                                  unfold lookupCopyRootSlot; rw [hslot_d, hsd_eq]
                                rw [ha_red, ha_step1]
                                unfold evalCopyRootIntScalars
                                dsimp only [AllocMapEntry.toBorrowEntry]
                                rw [hls_ok, hld_ok]
                                dsimp only
                                rw [hsc_bytes, Nat.beq_refl]
                                dsimp only
                                rw [show Nat.add srcPtr.offsetBytes total = srcPtr.offsetBytes + total from rfl,
                                  show Nat.add dstPtr.offsetBytes total = dstPtr.offsetBytes + total from rfl,
                                  show Bool.and (Nat.beq e_s.localIdx e_d.localIdx)
                                    (Bool.not (Bool.or (Nat.ble (srcPtr.offsetBytes + total) dstPtr.offsetBytes)
                                      (Nat.ble (dstPtr.offsetBytes + total) srcPtr.offsetBytes))) =
                                    (Nat.beq e_s.localIdx e_d.localIdx &&
                                      !(Nat.ble (srcPtr.offsetBytes + total) dstPtr.offsetBytes ||
                                        Nat.ble (dstPtr.offsetBytes + total) srcPtr.offsetBytes)) from rfl,
                                  hov_false]
                                dsimp only
                                rw [show Bool.and (Nat.beq dstPtr.offsetBytes 0) (Nat.beq total dstBytes) =
                                    (Nat.beq dstPtr.offsetBytes 0 && Nat.beq total dstBytes) from rfl,
                                  hwhole_false]
                                dsimp only
                                rw [hscd_bytes, Nat.beq_refl]
                                dsimp only
                                rw [writeCopyRootSlot_local_ok hslot_d hd_d,
                                  hbor, copyInvalidateConflictingBorrows_eq_map_updateAllocMapOnWrite]
                              have hpost := StateRelLM3_1.advance_write_deref_scalar hstate₃ rfl
                                (fun x => x.updateOnWrite e_d.localIdx (some dstPtr.tag))
                                (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
                                he_d hdecl_d hprim_d hslot_d hd_d hfind_d' hkind_d halign_d
                                hrel_new htr_d
                                (fun h => absurd h hdstInt.ne_bool)
                                (fun h => absurd h hdstInt.ne_char)
                                halign_a' hshape_a' hinit_a' hread_a'
                              rw [hanneal_step, ha_ok, hmap_eq,
                                copyStep_miri_ok hframes hfr.body_eq hfr.location_eq hfr₃.location_eq
                                  hbb hstmt hm_act]
                              exact .step _ _ hpost
                        · -- Destination OOB (`dstBytes < dstPtr.offsetBytes + total`).
                          have hoobD : dstLA.allocation.byteSize.bytes.toNat <
                              dstPtr.offsetBytes + total := by omega
                          obtain ⟨msg, herr⟩ := annealMemCopy_dst_oob_err
                            (st := { m with stack := ⟨#[tf₃]⟩ })
                            ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr srcId + UInt64.ofNat srcPtr.offsetBytes),
                              some (.concrete srcId srcBorTag)⟩
                            dstId dstBorTag dstPtr.offsetBytes
                            dstLA hid_d hoff_d hbase_d hfind_d hpos hle hoobD
                          refine mk_ub ?_ (hm_mem.trans herr)
                          rw [ha_red, ha_int, copyIte_neg (fun h => hinD h.2)]
                      · -- Source OOB (`srcBytes < srcPtr.offsetBytes + total`).
                        have hoobS : srcLA.allocation.byteSize.bytes.toNat <
                            srcPtr.offsetBytes + total := by omega
                        obtain ⟨msg, herr⟩ := annealMemCopy_src_oob_err
                          (st := { m with stack := ⟨#[tf₃]⟩ }) srcId srcBorTag srcPtr.offsetBytes
                          srcLA
                          ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr dstId + UInt64.ofNat dstPtr.offsetBytes),
                            some (.concrete dstId dstBorTag)⟩
                          hid_s hoff_s hbase_s hfind_s hpos hle hoobS
                        refine mk_ub ?_ (hm_mem.trans herr)
                        rw [ha_red, ha_int, copyIte_neg (fun h => hinS h.1)]
                · -- Case B: Non-integral target pair (`.bool` / `.char` with `decl_s.ty.kind = pointeeTy.kind = decl_d.ty.kind`).
                  have hsame_kinds : decl_s.ty.kind = pointeeTy.kind ∧ decl_d.ty.kind = pointeeTy.kind := by
                    rcases hcompat with hp | hk
                    · exact absurd hp hint_pair
                    · exact hk
                  obtain ⟨hk_s, hk_d⟩ := hsame_kinds
                  have hnot_int_s : ¬ ∃ k, IsIntegralTy decl_s.ty k := by
                    intro ⟨k, hk⟩
                    apply hint_pair
                    refine ⟨⟨k, hk⟩, ?_⟩
                    rcases hk with ⟨it, hit⟩ | ⟨ut, hut⟩
                    · exact ⟨translateIntTy it, .int it (hk_d.trans (hk_s.symm.trans hit))⟩
                    · exact ⟨translateUintTy ut, .uint ut (hk_d.trans (hk_s.symm.trans hut))⟩
                  have hnon_s := intCastTargetBytes_eq_none_of_not_integral hprim_s hnot_int_s
                  have hprim_pt := isPrimScalarTy_of_kind_eq hprim_s hk_s
                  obtain ⟨hrig_s, htr_s, hvalid_sz⟩ :=
                    primScalar_size_of_writeBytesPointee hprim_s (hk_s.symm ▸ hpt.wb)
                  obtain ⟨hrig_d, htr_d, _⟩ :=
                    primScalar_size_of_writeBytesPointee hprim_d (hk_d.symm ▸ hpt.wb)
                  -- 4a(nonint). Dead source local.
                  by_cases hd_s : slot_s = .dead
                  · subst hd_s
                    have hnone_s : m.machine.memory.live.find? (fun x => x.1 == srcId) = none := by
                      rw [← hea_s]; exact (halloc.local_alloc_sync tf₃ rfl e_s he_s).2 hslot_s
                    obtain ⟨msg, herr⟩ := annealMemCopy_src_dead_err
                      (st := { m with stack := ⟨#[tf₃]⟩ }) srcId srcBorTag srcPtr.offsetBytes _
                      hid_s hoff_s hbase_s hnone_s hpos hle
                    refine mk_ub ?_ (hm_mem.trans herr)
                    rw [ha_red]
                    exact evalCopyNonOverlappingWithCount_nonint_dead_ub hopS hpt.wb.anneal_size
                      hpt.anneal_align hle hpos hs_al hd_al hlook_s hdecl_s hrig_s hnon_s
                      hlook_d hdecl_d hrig_d (fun _ _ _ => evalCopySingleDirect_dead_src_ub hcaller hslot_s)
                  · -- 4b(nonint). Dead destination local.
                    by_cases hd_d : slot_d = .dead
                    · subst hd_d
                      have hnone_d : m.machine.memory.live.find? (fun x => x.1 == dstId) = none := by
                        rw [← hea_d]; exact (halloc.local_alloc_sync tf₃ rfl e_d he_d).2 hslot_d
                      obtain ⟨msg, herr⟩ := annealMemCopy_dst_dead_err
                        (st := { m with stack := ⟨#[tf₃]⟩ }) _ dstId dstBorTag dstPtr.offsetBytes
                        hid_d hoff_d hbase_d hnone_d hpos hle
                      refine mk_ub ?_ (hm_mem.trans herr)
                      rw [ha_red]
                      exact evalCopyNonOverlappingWithCount_nonint_dead_ub hopS hpt.wb.anneal_size
                        hpt.anneal_align hle hpos hs_al hd_al hlook_s hdecl_s hrig_s hnon_s
                        hlook_d hdecl_d hrig_d (fun _ _ _ =>
                          evalCopySingleDirect_dead_dst_ub hcaller hprim_pt hopS hopD hslot_s hslot_d)
                    · -- 4c(nonint). Both target locals are live.
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
                      by_cases hinS : srcPtr.offsetBytes + countSc.bits * elemBytes ≤ elemBytes
                      · by_cases hinD : dstPtr.offsetBytes + countSc.bits * elemBytes ≤ elemBytes
                        · obtain ⟨hoff0_s, hcnt1, _⟩ := copy_inbounds_pos_eq hpos hinS
                          obtain ⟨hoff0_d, _, _⟩ := copy_inbounds_pos_eq hpos hinD
                          have hlive_s_ne : get? s.frame.locals e_s.localIdx ≠ some .dead := by
                            rw [hslot_s]; intro h; injection h with h; exact hd_s h
                          have hlive_d_ne : get? s.frame.locals e_d.localIdx ≠ some .dead := by
                            rw [hslot_d]; intro h; injection h with h; exact hd_d h
                          obtain ⟨hperm_s, hperm_d, hnot_un_s, _⟩ :=
                            hlive_ok srcPtr dstPtr countSc e_s e_d decl_s decl_d elemBytes elemBytes
                              hsrc_loc_eq hdst_loc_eq hc_pre hpos hle he_s het_s he_d het_d
                              hdecl_s hdecl_d hrig_s hrig_d hinS hinD hlive_s_ne hlive_d_ne
                          have hs_init : ∃ sc_s, slot_s = .init (.scalar sc_s) := by
                            cases hs : slot_s with
                            | dead => exact absurd hs hd_s
                            | uninit => exact absurd (hslot_s.trans (congrArg some hs)) hnot_un_s
                            | init v =>
                              obtain ⟨sc_s, rfl⟩ := hsc_only_s v hs
                              exact ⟨sc_s, rfl⟩
                          obtain ⟨sc_s, rfl⟩ := hs_init
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
                          have ha_step1 : evalCopyNonOverlappingWithCountLM4_2 s (.copy ⟨srcIdx, []⟩)
                              (.copy ⟨dstIdx, []⟩) body.localDecls body.layouts
                              (.ptr srcPtr 8) (.ptr dstPtr 8) countSc.bits s.frame.locals =
                              evalCopySingleDirect s (.copy ⟨srcIdx, []⟩) (.copy ⟨dstIdx, []⟩)
                                body.localDecls body.layouts srcPtr dstPtr
                                e_s.toBorrowEntry e_d.toBorrowEntry s.frame.locals := by
                            rw [hcnt1, evalCopyNonOverlappingWithCount_of_perm_or_single hopS
                              hpt.wb.anneal_size hpt.anneal_align hle1 helem_pos hs_al hd_al
                              hlook_s hdecl_s hrig_s hoff0_s hlook_d hdecl_d hrig_d hoff0_d,
                              hnon_s]
                            rcases hperm_d with hp_d | hp_d <;> rw [hp_d] <;>
                              (cases hp_s : e_s.perm <;> first | rfl | exact absurd hp_s hperm_s)
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
                          · have hne_id : srcId ≠ e_d.allocId := by
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
                            have hkind_eq : decl_d.ty.kind = decl_s.ty.kind := hk_d.trans hk_s.symm
                            have hbool_d : decl_d.ty.kind = .bool →
                                sc_s.sizeBytes = 1 ∧ (sc_s.bits = 0 ∨ sc_s.bits = 1) :=
                              fun h => hbool_s (hkind_eq ▸ h)
                            have hchar_d : decl_d.ty.kind = .char →
                                sc_s.sizeBytes = 4 ∧ isValidCharCode sc_s.bits = true :=
                              fun h => hchar_s (hkind_eq ▸ h)
                            have ha_ok : evalCopyNonOverlappingLM4_2 s (.copy ⟨srcIdx, []⟩)
                                (.copy ⟨dstIdx, []⟩) countOp body.localDecls body.layouts =
                                MirStepNode.step
                                  (advanceStmt s (s.frame.locals.set e_d.localIdx (.init (.scalar sc_s)))
                                    { s.memory with
                                      borrows := (updateAllocMapOnWrite allocMap e_d.localIdx
                                        (some dstPtr.tag)).map AllocMapEntry.toBorrowEntry }) := by
                              rw [ha_red, ha_step1,
                                evalCopySingleDirect_distinct_ok hprim_pt hopS hopD hne_tag hsame
                                  hslot_s hslot_d hd_d hdecl_d hbool_d hchar_d,
                                hbor, copyInvalidateConflictingBorrows_eq_map_updateAllocMapOnWrite]
                            have hmap_eq : copyNextAllocMap s.frame.locals allocMap dstIdx countOp
                                elemBytes =
                                updateAllocMapOnWrite allocMap e_d.localIdx (some dstPtr.tag) := by
                              unfold copyNextAllocMap writeBytesNextAllocMap
                              rw [hc_opt]
                              simp only [hz, ↓reduceIte, hdst_loc_eq,
                                copyLookupAllocMapByTag_of_mem_nodup halloc.tags_nodup he_d het_d]
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
                        · have hoobD : dstLA.allocation.byteSize.bytes.toNat <
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
                          rw [ha_red]; unfold evalCopyNonOverlappingWithCountLM4_2
                          rw [copyPrecheck_eq _ _ _ hopS hpt.wb.anneal_size hpt.anneal_align]
                          simp only [hle, hs_al, hd_al, Bool.and_self, hz, ↓reduceIte]
                          rw [lookupCopyBorrowChecked_root hlook_s hdecl_s hrig_s,
                            lookupCopyBorrowChecked_root hlook_d hdecl_d hrig_d]
                          simp only [hinS, hinD, ↓reduceIte]
                      · have hoobS : srcLA.allocation.byteSize.bytes.toNat <
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
                        rw [ha_red]; unfold evalCopyNonOverlappingWithCountLM4_2
                        rw [copyPrecheck_eq _ _ _ hopS hpt.wb.anneal_size hpt.anneal_align]
                        simp only [hle, hs_al, hd_al, Bool.and_self, hz, ↓reduceIte]
                        rw [lookupCopyBorrowChecked_root hlook_s hdecl_s hrig_s]
                        simp only [hinS, ↓reduceIte]
    · -- Size overflow (`¬ countSc.bits * elemBytes ≤ isizeMaxBytes`).
      simp only [hle, ↓reduceIte] at hm_red
      refine mk_ub ?_ hm_red
      rw [ha_red]; unfold evalCopyNonOverlappingWithCountLM4_2
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
    (htgt_compat : ∀ srcPtr dstPtr e_s e_d decl_s decl_d,
      get? s.frame.locals srcIdx = some (.init (.ptr srcPtr 8)) →
      get? s.frame.locals dstIdx = some (.init (.ptr dstPtr 8)) →
      e_s ∈ allocMap → e_s.tag = srcPtr.tag →
      e_d ∈ allocMap → e_d.tag = dstPtr.tag →
      get? body.localDecls e_s.localIdx = some decl_s →
      get? body.localDecls e_d.localIdx = some decl_d →
      0 < elemBytes →
      CopyTargetCompatible decl_s decl_d pointeeTy.kind)
    (hlive_ok : ∀ srcPtr dstPtr countSc e_s e_d decl_s decl_d srcBytes dstBytes,
      get? s.frame.locals srcIdx = some (.init (.ptr srcPtr 8)) →
      get? s.frame.locals dstIdx = some (.init (.ptr dstPtr 8)) →
      WriteBytesScalarPreVal s.frame.locals countOp countSc →
      0 < countSc.bits * elemBytes →
      countSc.bits * elemBytes ≤ isizeMaxBytes →
      e_s ∈ allocMap → e_s.tag = srcPtr.tag →
      e_d ∈ allocMap → e_d.tag = dstPtr.tag →
      get? body.localDecls e_s.localIdx = some decl_s →
      get? body.localDecls e_d.localIdx = some decl_d →
      rigidTyByteSize body.layouts decl_s.ty = some srcBytes →
      rigidTyByteSize body.layouts decl_d.ty = some dstBytes →
      srcPtr.offsetBytes + countSc.bits * elemBytes ≤ srcBytes →
      dstPtr.offsetBytes + countSc.bits * elemBytes ≤ dstBytes →
      get? s.frame.locals e_s.localIdx ≠ some .dead →
      get? s.frame.locals e_d.localIdx ≠ some .dead →
      e_s.perm ≠ .disabled ∧
        (e_d.perm = .active ∨ e_d.perm = .reserved) ∧
        get? s.frame.locals e_s.localIdx ≠ some .uninit ∧
        ((dstPtr.offsetBytes = 0 ∧ countSc.bits * elemBytes = dstBytes) ∨
          get? s.frame.locals e_d.localIdx ≠ some .uninit)) :
    ∃ allocMap',
      StepRelLM3_1 body m allocMap'
        (stepMirFnLM4_2 body s)
        (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  ⟨copyNextAllocMap s.frame.locals allocMap dstIdx countOp elemBytes,
    step_intrinsic_copyNonOverlapping_simulation_explicit hstate hphase hbb hstmt
      hsrcDecl hsrcTy hsrcImm hdstDecl hdstTy hdstImm hcountInt hcountOp hpt
      htgt_compat hlive_ok⟩

private theorem ptrValueAligned_of_offset_zero {elemAlign : Nat}
    (hal : ValidCopyAlign elemAlign) {p : ProvenancePtr} (hoff : p.offsetBytes = 0) :
    ptrValueAligned elemAlign (.ptr p 8) = true := by
  dsimp only [ptrValueAligned]
  rw [hoff]
  rcases hal with rfl | rfl | rfl | rfl | rfl <;> rfl

/-- Shared reduction for the `CopyNonOverlapping` divergence theorems (`count = 1`
at root offset `0` on live primitive-scalar stack locals): reduces Anneal's
`stepMirFn` to the Tree Borrows permission table + `evalCopyRootIntScalars` /
`evalCopySingleDirect` and proves `lean-miri`'s `Step.step` returns `(m', .ok true)`
whenever `slot_s = .uninit` or `e_s.localIdx ≠ e_d.localIdx`. -/
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
    (∃ stepBody : MirStepNode,
      (stepBody = evalCopySingleDirect s (.copy ⟨srcIdx, []⟩) (.copy ⟨dstIdx, []⟩)
          body.localDecls body.layouts srcPtr dstPtr
          e_s.toBorrowEntry e_d.toBorrowEntry s.frame.locals ∨
        ∃ srcBytes dstBytes,
          stepBody = evalCopyRootIntScalars s s.frame.locals srcPtr dstPtr
            e_s.toBorrowEntry e_d.toBorrowEntry srcBytes dstBytes elemBytes) ∧
      stepMirFnLM4_2 body s =
        match e_s.perm, e_d.perm with
        | .disabled, _ => MirStepNode.fail .ub
        | _, .frozen => MirStepNode.fail .ub
        | _, .disabled => MirStepNode.fail .ub
        | _, _ => stepBody) ∧
    ∃ m',
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .ok true) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, _, _⟩ := id hstate
  have hanneal_step : stepMirFnLM4_2 body s =
      evalCopyNonOverlappingLM4_2 s (.copy ⟨srcIdx, []⟩) (.copy ⟨dstIdx, []⟩) countOp
        body.localDecls body.layouts := by
    rw [stepMirFnLM4_2_eq_of_not_other body s hcal hphase]
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
        have ha_eq : ∃ stepBody : MirStepNode,
            (stepBody = evalCopySingleDirect s (.copy ⟨srcIdx, []⟩) (.copy ⟨dstIdx, []⟩)
                body.localDecls body.layouts srcPtr dstPtr
                e_s.toBorrowEntry e_d.toBorrowEntry s.frame.locals ∨
              ∃ srcBytes dstBytes,
                stepBody = evalCopyRootIntScalars s s.frame.locals srcPtr dstPtr
                  e_s.toBorrowEntry e_d.toBorrowEntry srcBytes dstBytes elemBytes) ∧
            stepMirFnLM4_2 body s =
              match e_s.perm, e_d.perm with
              | .disabled, _ => MirStepNode.fail .ub
              | _, .frozen => MirStepNode.fail .ub
              | _, .disabled => MirStepNode.fail .ub
              | _, _ => stepBody := by
          refine ⟨match intCastTargetBytes decl_s.ty.kind, intCastTargetBytes decl_d.ty.kind with
            | some srcBytes, some dstBytes =>
              evalCopyRootIntScalars s s.frame.locals srcPtr dstPtr
                e_s.toBorrowEntry e_d.toBorrowEntry srcBytes dstBytes elemBytes
            | _, _ =>
              evalCopySingleDirect s (.copy ⟨srcIdx, []⟩) (.copy ⟨dstIdx, []⟩)
                body.localDecls body.layouts srcPtr dstPtr
                e_s.toBorrowEntry e_d.toBorrowEntry s.frame.locals, ?_, ?_⟩
          · cases intCastTargetBytes decl_s.ty.kind with
            | none => exact Or.inl rfl
            | some srcBytes =>
              cases intCastTargetBytes decl_d.ty.kind with
              | none => exact Or.inl rfl
              | some dstBytes => exact Or.inr ⟨srcBytes, dstBytes, rfl⟩
          · rw [hanneal_step]
            unfold evalCopyNonOverlappingLM4_2
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

* Anneal's typed `evalCopyRootIntScalars` / `evalCopySingleDirect` rejects reading
  `.uninit` for a non-union scalar local (`stepMirFnLM4_2 body s = MirStepNode.fail .ub`);
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
    stepMirFnLM4_2 body s = MirStepNode.fail .ub ∧
    ∃ m',
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .ok true) := by
  have hsrc_live : get? s.frame.locals e_s.localIdx ≠ some .dead := by
    rw [huninit_s]; nofun
  obtain ⟨⟨stepBody, hbody, ha_eq⟩, hm_ok⟩ := copyDivergence_core hstate hphase hbb hstmt
    hsrcDecl hsrcTy hsrcImm hdstDecl hdstTy hdstImm hcountInt hcountOp hpt
    hsrc_val hdst_val hoff0_s hoff0_d hcnt_pre hcnt1 he_s het_s he_d het_d
    hsrc_tgt hdst_tgt hsrc_live hdst_live (Or.inl huninit_s)
  refine ⟨?_, hm_ok⟩
  have hbody_ub : stepBody = MirStepNode.fail .ub := by
    rcases hbody with rfl | ⟨srcBytes, dstBytes, rfl⟩
    · exact evalCopySingleDirect_uninit_src_ub huninit_s
    · exact evalCopyRootIntScalars_uninit_src_ub huninit_s
  rw [ha_eq, hbody_ub]
  cases e_s.perm <;> cases e_d.perm <;> rfl

/-- **Characterized divergence (`LM-4.2`)**: copying `count = 1` element between
distinct live primitive-scalar stack locals when `e_s.perm = .disabled` or
`e_d.perm` is `.frozen` / `.disabled`:

* Anneal enforces Tree Borrows read permission on `src` and write permission on
  `dst` (`stepMirFnLM4_2 body s = MirStepNode.fail .ub`);
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
    stepMirFnLM4_2 body s = MirStepNode.fail .ub ∧
    ∃ m',
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .ok true) := by
  obtain ⟨⟨stepBody, _, ha_eq⟩, hm_ok⟩ := copyDivergence_core hstate hphase hbb hstmt
    hsrcDecl hsrcTy hsrcImm hdstDecl hdstTy hdstImm hcountInt hcountOp hpt
    hsrc_val hdst_val hoff0_s hoff0_d hcnt_pre hcnt1 he_s het_s he_d het_d
    hsrc_tgt hdst_tgt hsrc_live hdst_live (Or.inr hne_loc)
  refine ⟨?_, hm_ok⟩
  rw [ha_eq]
  cases hpS : e_s.perm <;> cases hpD : e_d.perm <;>
    first | rfl | (simp [hpS, hpD] at hperm_bad)


private theorem allocRange_size (st sz : Miri.ABI.Size) : (Miri.Memory.allocRange st sz).size = sz := rfl

private theorem copyInitMask_prepareCopy_false_range {n off total : Nat}
    (hn : ValidScalarBytes n) (hpos : 0 < total) (hinb : off + total ≤ n) :
    (Miri.Memory.InitMask.new (translateSizeBytes n) false).prepareCopy
      (Miri.Memory.allocRange (Miri.ABI.Size.ofBytes (UInt64.ofNat off))
        (Miri.ABI.Size.ofBytes (UInt64.ofNat total))) =
      .ok ⟨false, #[UInt64.ofNat total]⟩ := by
  have hn_eq : (translateSizeBytes n).bytes.toNat = n := by
    rcases hn with rfl | rfl | rfl | rfl | rfl <;> rfl
  have hn64 : n < 2 ^ 64 := by rcases hn with rfl | rfl | rfl | rfl | rfl <;> omega
  have hlt64 : off + total < 2 ^ 64 := Nat.lt_of_le_of_lt hinb hn64
  have hoff64 : off < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.le_add_right off total) hlt64
  have htot64 : total < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.le_add_left total off) hlt64
  have hend := copyRange_endExclusive hlt64
  have hoff_nat : (UInt64.ofNat off).toNat = off := UInt64.toNat_ofNat_of_lt hoff64
  have htot_nat : (UInt64.ofNat total).toNat = total := UInt64.toNat_ofNat_of_lt htot64
  have hend_nat : (UInt64.ofNat (off + total)).toNat = off + total := UInt64.toNat_ofNat_of_lt hlt64
  have hnz : (UInt64.ofNat total == 0) = false := by
    cases hb : (UInt64.ofNat total == 0)
    · rfl
    · have := eq_of_beq hb; rw [this] at htot_nat; simp at htot_nat; omega
  have hnot_oob : ¬ (UInt64.ofNat (off + total) > (translateSizeBytes n).bytes) := by
    rw [gt_iff_lt, UInt64.lt_iff_toNat_lt, hend_nat, hn_eq]; omega
  have hlt_sf : UInt64.ofNat off < UInt64.ofNat (off + total) := by
    rw [UInt64.lt_iff_toNat_lt, hoff_nat, hend_nat]; omega
  have hnot_gt_sf : ¬ (UInt64.ofNat off > UInt64.ofNat (off + total)) := by
    rw [gt_iff_lt, UInt64.lt_iff_toNat_lt, hoff_nat, hend_nat]; omega
  have hnot_le_fs : ¬ (UInt64.ofNat (off + total) ≤ UInt64.ofNat off) := by
    rw [UInt64.le_iff_toNat_le, hoff_nat, hend_nat]; omega
  have hfuel : (UInt64.ofNat (off + total)).toNat - (UInt64.ofNat off).toNat + 1 = total + 1 := by
    omega
  have hsub_u64 : UInt64.ofNat (off + total) - UInt64.ofNat off = UInt64.ofNat total := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_of_lt hlt_sf), hend_nat, hoff_nat, htot_nat]
    omega
  unfold Miri.Memory.InitMask.prepareCopy Miri.Memory.InitMask.rangeAsInitChunks
  rw [hend]
  have hlen_new : (Miri.Memory.InitMask.new (translateSizeBytes n) false).len =
      translateSizeBytes n := rfl
  simp only [Miri.Memory.allocRange, Miri.ABI.Size.ofBytes, hlen_new,
    hnz, Bool.false_eq_true, ↓reduceIte, hnot_oob, hlt_sf, Miri.Memory.InitMask.lazy_get,
    bind, Except.bind, pure, Except.pure]
  have hcond1 :
      (decide (UInt64.ofNat off > UInt64.ofNat (off + total)) ||
        decide (UInt64.ofNat (off + total) > (translateSizeBytes n).bytes)) = false := by
    rw [Bool.or_eq_false_iff, decide_eq_false_iff_not, decide_eq_false_iff_not]
    exact ⟨hnot_gt_sf, hnot_oob⟩
  have hcond2 :
      (decide (UInt64.ofNat (off + total) > UInt64.ofNat (off + total)) ||
        decide (UInt64.ofNat (off + total) > (translateSizeBytes n).bytes)) = false := by
    rw [Bool.or_eq_false_iff, decide_eq_false_iff_not, decide_eq_false_iff_not]
    exact ⟨UInt64.lt_irrefl _, hnot_oob⟩
  have hiter0 : (Miri.Memory.InitChunkIter.mk
      (Miri.Memory.InitMask.new (translateSizeBytes n) false) false
      ⟨UInt64.ofNat off⟩ ⟨UInt64.ofNat (off + total)⟩).next? =
      .ok (some (.Uninit ⟨UInt64.ofNat off⟩ ⟨UInt64.ofNat (off + total)⟩,
        ⟨Miri.Memory.InitMask.new (translateSizeBytes n) false, true,
          ⟨UInt64.ofNat (off + total)⟩, ⟨UInt64.ofNat (off + total)⟩⟩)) := by
    unfold Miri.Memory.InitChunkIter.next? Miri.Memory.InitMask.new
    dsimp only [bind, Except.bind, pure, Except.pure]
    erw [hcond1]
    have hnot_ge : ¬ ((UInt64.ofNat off).toNat ≥ (UInt64.ofNat (off + total)).toNat) := by
      omega
    with_unfolding_all dsimp
    simp only [↓reduceIte, hnot_le_fs]
    with_unfolding_all change
      (if (UInt64.ofNat off).toNat ≥ (UInt64.ofNat (off + total)).toNat then _ else _) = _
    rw [copyIte_neg hnot_ge]
    rfl
  have hiter1 : (Miri.Memory.InitChunkIter.mk
      (Miri.Memory.InitMask.new (translateSizeBytes n) false) true
      ⟨UInt64.ofNat (off + total)⟩ ⟨UInt64.ofNat (off + total)⟩).next? = .ok none := by
    unfold Miri.Memory.InitChunkIter.next? Miri.Memory.InitMask.new
    dsimp only [bind, Except.bind, pure, Except.pure]
    erw [hcond2]
    with_unfolding_all simp
  have htot16 : total ≤ 16 := by
    rcases hn with rfl | rfl | rfl | rfl | rfl <;> omega
  have hchunks : Miri.Memory.InitMask.collectChunks
      ⟨Miri.Memory.InitMask.new (translateSizeBytes n) false, false,
        ⟨UInt64.ofNat off⟩, ⟨UInt64.ofNat (off + total)⟩⟩ =
      .ok #[.Uninit ⟨UInt64.ofNat off⟩ ⟨UInt64.ofNat (off + total)⟩] := by
    unfold Miri.Memory.InitMask.collectChunks
    with_unfolding_all erw [hfuel]
    match total, hpos, htot16 with
    | 1, _, _ | 2, _, _ | 3, _, _ | 4, _, _ | 5, _, _ | 6, _, _ | 7, _, _ | 8, _, _
    | 9, _, _ | 10, _, _ | 11, _, _ | 12, _, _ | 13, _, _ | 14, _, _ | 15, _, _ | 16, _, _ =>
      with_unfolding_all (conv => lhs; whnf)
      with_unfolding_all erw [hiter0]
      dsimp only [bind, Except.bind, pure, Except.pure]
      with_unfolding_all (conv => lhs; whnf)
      with_unfolding_all erw [hiter1]
      rfl
    | k + 17, _, hle => omega
  rw [hchunks]
  have hnot_lt_fs : ¬ (UInt64.ofNat (off + total) < UInt64.ofNat off) := hnot_gt_sf
  have hcr : (Miri.Memory.InitChunk.Uninit ⟨UInt64.ofNat off⟩ ⟨UInt64.ofNat (off + total)⟩).range =
      .ok ⟨⟨UInt64.ofNat off⟩, ⟨UInt64.ofNat total⟩⟩ := by
    unfold Miri.Memory.InitChunk.range Miri.Memory.AllocRange.fromEndpoints Miri.ABI.Size.sub
    simp only [hnot_lt_fs, ↓reduceIte, hsub_u64, Except.mapError, bind, Except.bind,
      pure, Except.pure, Miri.ABI.Size.ofBytes]
  simp only [List.forIn_toArray, List.forIn_cons, List.forIn_nil, hcr,
    Miri.Memory.InitChunk.isInit, bind, Except.bind, pure, Except.pure]
  rfl

private theorem copyInitMask_setRange_small_ok {dstBytes dstStart total : Nat}
    (hnD : ValidScalarBytes dstBytes) (hinD : dstStart + total ≤ dstBytes)
    (m : Miri.Memory.InitMask) (hlen : m.len = translateSizeBytes dstBytes)
    (hblocks : (∃ b, m.blocks = .Lazy b) ∨ (∃ w, m.blocks = .Materialized ⟨#[w]⟩))
    (newState : Bool) :
    ∃ m' : Miri.Memory.InitMask,
      m.setRange
        (Miri.Memory.allocRange (Miri.ABI.Size.ofBytes (UInt64.ofNat dstStart))
          (Miri.ABI.Size.ofBytes (UInt64.ofNat total))) newState = .ok m' ∧
      m'.len = translateSizeBytes dstBytes ∧
      ((∃ b, m'.blocks = .Lazy b) ∨ (∃ w, m'.blocks = .Materialized ⟨#[w]⟩)) := by
  have hd_eq : (translateSizeBytes dstBytes).bytes.toNat = dstBytes := by
    rcases hnD with rfl | rfl | rfl | rfl | rfl <;> rfl
  have hd16 : dstBytes ≤ 16 := by rcases hnD with rfl | rfl | rfl | rfl | rfl <;> omega
  have hd64 : dstBytes < 2 ^ 64 := by omega
  have hlt64 : dstStart + total < 2 ^ 64 := Nat.lt_of_le_of_lt hinD hd64
  have hst64 : dstStart < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hlt64
  have hend := copyRange_endExclusive hlt64
  have hst_nat : (UInt64.ofNat dstStart).toNat = dstStart := UInt64.toNat_ofNat_of_lt hst64
  have hend_nat : (UInt64.ofNat (dstStart + total)).toNat = dstStart + total :=
    UInt64.toNat_ofNat_of_lt hlt64
  have hle_bytes : UInt64.ofNat (dstStart + total) ≤ (translateSizeBytes dstBytes).bytes := by
    rw [UInt64.le_iff_toNat_le, hend_nat, hd_eq]; exact hinD
  have hnot_gt : ¬ (UInt64.ofNat (dstStart + total) > (translateSizeBytes dstBytes).bytes) := by
    rw [gt_iff_lt, UInt64.lt_iff_toNat_lt, hend_nat, hd_eq]; omega
  have hdivA : (UInt64.ofNat dstStart).toNat / 64 = 0 := by rw [hst_nat]; omega
  have hdivB : (UInt64.ofNat (dstStart + total)).toNat / 64 = 0 := by rw [hend_nat]; omega
  cases m with
  | mk blocks len =>
  change len = _ at hlen
  subst hlen
  change (∃ b, blocks = .Lazy b) ∨ (∃ w, blocks = .Materialized ⟨#[w]⟩) at hblocks
  unfold Miri.Memory.InitMask.setRange
  rw [hend]
  dsimp only [bind, Except.bind, Miri.Memory.allocRange, Miri.ABI.Size.ofBytes]
  by_cases hfull : UInt64.ofNat dstStart = 0 ∧ (translateSizeBytes dstBytes).bytes ≤ UInt64.ofNat (dstStart + total)
  · have hsz_eq : (⟨UInt64.ofNat (dstStart + total)⟩ : Miri.ABI.Size) = translateSizeBytes dstBytes := by
      cases hs : translateSizeBytes dstBytes with
      | mk nb =>
        rw [hs] at hle_bytes hfull
        exact congrArg Miri.ABI.Size.mk (UInt64.le_antisymm hle_bytes hfull.2)
    rcases hblocks with ⟨b, rfl⟩ | ⟨w, rfl⟩
    · dsimp only
      rw [copyIte_pos hfull, hsz_eq]
      exact ⟨_, rfl, rfl, Or.inl ⟨newState, rfl⟩⟩
    · dsimp only
      rw [copyIte_pos hfull, hsz_eq]
      exact ⟨_, rfl, rfl, Or.inl ⟨newState, rfl⟩⟩
  · rcases hblocks with ⟨b, rfl⟩ | ⟨w, rfl⟩
    · dsimp only
      rw [copyIte_neg hfull]
      cases hbeq : (b == newState)
      · simp only [Bool.false_eq_true, ↓reduceIte]
        split
        · next err hm =>
          rcases hnD with rfl | rfl | rfl | rfl | rfl <;> cases b <;>
            with_unfolding_all cases hm
        · next blocks hm =>
          have hblk : ∃ w₀ : UInt64, blocks = ⟨#[w₀]⟩ := by
            rcases hnD with rfl | rfl | rfl | rfl | rfl <;> cases b <;>
              { with_unfolding_all cases hm
                exact ⟨_, rfl⟩ }
          obtain ⟨w₀, rfl⟩ := hblk
          rw [copyIte_pos hle_bytes]
          split
          · next err hs =>
            with_unfolding_all (conv at hs => lhs; whnf)
            with_unfolding_all erw [hdivA, hdivB] at hs
            with_unfolding_all cases hs
          · next v hs =>
            with_unfolding_all (conv at hs => lhs; whnf)
            with_unfolding_all erw [hdivA, hdivB] at hs
            with_unfolding_all cases hs
            exact ⟨_, rfl, rfl, Or.inr ⟨_, rfl⟩⟩
      · simp only [↓reduceIte, hnot_gt, pure, Except.pure]
        exact ⟨_, rfl, rfl, Or.inl ⟨b, rfl⟩⟩
    · dsimp only
      rw [copyIte_neg hfull, copyIte_pos hle_bytes]
      split
      · next err hs =>
        with_unfolding_all (conv at hs => lhs; whnf)
        with_unfolding_all erw [hdivA, hdivB] at hs
        with_unfolding_all cases hs
      · next v hs =>
        with_unfolding_all (conv at hs => lhs; whnf)
        with_unfolding_all erw [hdivA, hdivB] at hs
        with_unfolding_all cases hs
        exact ⟨_, rfl, rfl, Or.inr ⟨_, rfl⟩⟩

theorem StackScalarAllocShape.copyRepeatedly_range_uninit {E : Type}
    {srcBytes dstBytes : Nat}
    (hnS : ValidScalarBytes srcBytes) (hnD : ValidScalarBytes dstBytes)
    {srcStart dstStart total : Nat}
    (hpos : 0 < total) (hinS : srcStart + total ≤ srcBytes) (hinD : dstStart + total ≤ dstBytes)
    {S D : Miri.Memory.Allocation AnnealProv E}
    (hshapeS : StackScalarAllocShape (translateSizeBytes srcBytes) S)
    (huninitS : S.initializationMask = Miri.Memory.InitMask.new (translateSizeBytes srcBytes) false)
    (hshapeD : StackScalarAllocShape (translateSizeBytes dstBytes) D)
    (sameAlloc : Bool) :
    ∃ alloc' : Miri.Memory.Allocation AnnealProv E,
      Miri.Memory.Allocation.copyRepeatedly S
        (Miri.Memory.allocRange (Miri.ABI.Size.ofBytes (UInt64.ofNat srcStart))
          (Miri.ABI.Size.ofBytes (UInt64.ofNat total)))
        (Miri.ABI.Size.ofBytes (UInt64.ofNat dstStart)) 1 (Miri.ABI.Size.ofBytes 8)
        sameAlloc true D = .ok () alloc' := by
  have hs64 : srcBytes < 2 ^ 64 := by rcases hnS with rfl | rfl | rfl | rfl | rfl <;> omega
  have hd64 : dstBytes < 2 ^ 64 := by rcases hnD with rfl | rfl | rfl | rfl | rfl <;> omega
  have hltS : srcStart + total < 2 ^ 64 := Nat.lt_of_le_of_lt hinS hs64
  have hltD : dstStart + total < 2 ^ 64 := Nat.lt_of_le_of_lt hinD hd64
  have ht64 : total < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.le_add_left _ _) hltS
  have hsliceS := copyCheckedSlice_range hnS hinS hshapeS.byteSize_eq hshapeS.len_eq
  have hsliceD := copyCheckedSlice_range hnD hinD hshapeD.byteSize_eq hshapeD.len_eq
  unfold Miri.Memory.Allocation.getBytesUnchecked at hsliceS hsliceD
  have hmul := copySize_mul_one (Miri.ABI.Size.ofBytes (UInt64.ofNat total))
  have hprov_prep := copyProv_prepareCopy_new_range hltS (copyAlloc_raw S)
  have hmask_prep := copyInitMask_prepareCopy_false_range hnS hpos hinS
  have hendD := copyRange_endExclusive hltD
  have hclear := Miri.Memory.ProvenanceMap.clear_new (P := AnnealProv)
    (Miri.Memory.allocRange (Miri.ABI.Size.ofBytes (UInt64.ofNat dstStart))
      (Miri.ABI.Size.ofBytes (UInt64.ofNat total)))
    (copyAlloc_raw D) (Miri.ABI.Size.ofBytes 8) _ (by decide) hendD
  have hnz_tot : (UInt64.ofNat total == 0) = false := by
    have ht : (UInt64.ofNat total).toNat = total := UInt64.toNat_ofNat_of_lt ht64
    cases hb : (UInt64.ofNat total == 0)
    · rfl
    · have := eq_of_beq hb; rw [this] at ht; simp at ht; omega
  rcases hshapeS with ⟨hszS, hlenS, hmutS, hprovS, _⟩
  rcases hshapeD with ⟨hszD, hlenD, hmutD, hprovD, ⟨bD, hmaskD⟩⟩
  obtain ⟨m₁, hm₁, hlen₁, hbl₁⟩ := copyInitMask_setRange_small_ok hnD hinD
    (Miri.Memory.InitMask.new (translateSizeBytes dstBytes) bD) rfl (Or.inl ⟨bD, rfl⟩) true
  obtain ⟨m₂, hm₂, _, _⟩ := copyInitMask_setRange_small_ok hnD hinD m₁ hlen₁ hbl₁ false
  cases S with | _ rawS szS provS maskS alignS mutS extraS nbS =>
  cases D with | _ rawD szD provD maskD alignD mutD extraD nbD =>
  change szS = _ at hszS; change rawS.size = _ at hlenS
  change mutS = _ at hmutS; change provS = _ at hprovS; change maskS = _ at huninitS
  change szD = _ at hszD; change rawD.size = _ at hlenD
  change mutD = _ at hmutD; change provD = _ at hprovD; change maskD = _ at hmaskD
  subst hszS hmutS hprovS huninitS hszD hmutD hprovD hmaskD
  dsimp only [copyAlloc_raw] at hprov_prep hclear
  simp only [Miri.Memory.allocRange, Miri.ABI.Size.ofBytes] at hm₁ hm₂ hclear
  unfold Miri.Memory.Allocation.copyRepeatedly
  rw [hsliceS]; dsimp only [bind, Pure.pure, pure]
  erw [hmul]; dsimp only [bind, Pure.pure, pure]
  rw [hsliceD, hprov_prep, hmask_prep]
  simp only [Miri.Memory.InitCopy.noBytesInit, Bool.not_false, Bool.true_and,
    List.size_toArray, List.length_cons, List.length_nil, beq_self_eq_true,
    ↓reduceIte, Id.run]
  split
  · next afterClear hprep =>
    have hp := hprep
    with_unfolding_all (conv at hp => lhs; whnf)
    with_unfolding_all erw [hsliceD] at hp
    simp only [Miri.Memory.allocRange, Miri.ABI.Size.ofBytes, hnz_tot, bne_self_eq_false,
      Bool.false_eq_true, ↓reduceIte] at hp
    split at hp
    rotate_left
    · next _ heq =>
      with_unfolding_all (conv at heq => lhs; whnf)
      rw [hm₁] at heq
      with_unfolding_all (conv at heq => lhs; whnf)
      cases heq
    next initialized heq =>
    with_unfolding_all (conv at heq => lhs; whnf)
    rw [hm₁] at heq
    with_unfolding_all (conv at heq => lhs; whnf)
    injection heq with hinit_eq
    subst hinit_eq
    dsimp only [bind, Bind.bind, pure, Pure.pure] at hp
    with_unfolding_all erw [hclear] at hp
    split
    · next reason updated hw =>
      with_unfolding_all cases hp
      unfold Miri.Memory.Allocation.writeUninit at hw
      dsimp only [Id.run] at hw
      with_unfolding_all erw [hsliceD] at hw
      simp only [Miri.Memory.allocRange, Miri.ABI.Size.ofBytes, hnz_tot, bne_self_eq_false,
        Bool.false_eq_true, ↓reduceIte] at hw
      split at hw
      · next uninitialized heq₂ =>
        with_unfolding_all (conv at heq₂ => lhs; whnf)
        rw [hm₂] at heq₂
        with_unfolding_all (conv at heq₂ => lhs; whnf)
        injection heq₂ with huninit_eq
        subst huninit_eq
        dsimp only [bind, Bind.bind, pure, Pure.pure] at hw
        with_unfolding_all erw [hclear] at hw
        with_unfolding_all cases hw
      · next _ heq₂ =>
        with_unfolding_all (conv at heq₂ => lhs; whnf)
        rw [hm₂] at heq₂
        with_unfolding_all (conv at heq₂ => lhs; whnf)
        cases heq₂
    · next updated hw =>
      exact ⟨updated, rfl⟩
  · next reason updated hprep =>
    with_unfolding_all (conv at hprep => lhs; whnf)
    with_unfolding_all erw [hsliceD] at hprep
    simp only [Miri.Memory.allocRange, Miri.ABI.Size.ofBytes, hnz_tot, bne_self_eq_false,
      Bool.false_eq_true, ↓reduceIte] at hprep
    split at hprep
    · next initialized heq =>
      with_unfolding_all (conv at heq => lhs; whnf)
      rw [hm₁] at heq
      with_unfolding_all (conv at heq => lhs; whnf)
      injection heq with hinit_eq
      subst hinit_eq
      dsimp only [bind, Bind.bind, pure, Pure.pure] at hprep
      with_unfolding_all erw [hclear] at hprep
      with_unfolding_all cases hprep
    · next _ heq =>
      with_unfolding_all (conv at heq => lhs; whnf)
      rw [hm₁] at heq
      with_unfolding_all (conv at heq => lhs; whnf)
      cases heq

theorem annealMemCopy_live_uninit_range_ok
    {st : AnnealStepState}
    {srcBytes dstBytes : Nat}
    (hnS : ValidScalarBytes srcBytes) (hnD : ValidScalarBytes dstBytes)
    {srcStart dstStart total : Nat}
    (hpos : 0 < total) (hinS : srcStart + total ≤ srcBytes) (hinD : dstStart + total ≤ dstBytes)
    (srcId : Miri.Memory.AllocId) (srcTag : Miri.Memory.BorTag)
    (srcLA : Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
      Miri.Memory.MiriMemoryKind)
    (dstId : Miri.Memory.AllocId) (dstTag : Miri.Memory.BorTag)
    (dstLA : Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
      Miri.Memory.MiriMemoryKind)
    (hsrc_id : srcId.value.toNat < 2 ^ 32)
    (hsrc_base : st.machine.lookupBaseAddr srcId = some (annealStackBaseAddr srcId))
    (hsrc_live : st.machine.memory.live.find? (fun entry => entry.1 == srcId) = some (srcId, srcLA))
    (hsrc_shape : StackScalarAllocShape (translateSizeBytes srcBytes) srcLA.allocation)
    (hsrc_uninit : srcLA.allocation.initializationMask =
      Miri.Memory.InitMask.new (translateSizeBytes srcBytes) false)
    (hdst_id : dstId.value.toNat < 2 ^ 32)
    (hdst_base : st.machine.lookupBaseAddr dstId = some (annealStackBaseAddr dstId))
    (hdst_live : st.machine.memory.live.find? (fun entry => entry.1 == dstId) = some (dstId, dstLA))
    (hdst_shape : StackScalarAllocShape (translateSizeBytes dstBytes) dstLA.allocation) :
    ∃ mach', annealMemCopy
      ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr srcId + UInt64.ofNat srcStart),
        some (.concrete srcId srcTag)⟩
      ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr dstId + UInt64.ofNat dstStart),
        some (.concrete dstId dstTag)⟩
      (Miri.ABI.Size.ofBytes (UInt64.ofNat total)) true st = .ok () { st with machine := mach' } := by
  have hle : total ≤ isizeMaxBytes := by
    unfold isizeMaxBytes; rcases hnS with rfl | rfl | rfl | rfl | rfl <;> omega
  have hts : Miri.ABI.Size.ofBytes (UInt64.ofNat total) = translateSizeBytes total := by
    have _ : total < 2^64 := by rcases hnS with rfl | rfl | rfl | rfl | rfl <;> omega
    rfl
  have hsrc_sz : srcLA.allocation.byteSize.bytes.toNat = srcBytes := by
    rw [hsrc_shape.byteSize_eq]; rcases hnS with rfl | rfl | rfl | rfl | rfl <;> rfl
  have hdst_sz : dstLA.allocation.byteSize.bytes.toNat = dstBytes := by
    rw [hdst_shape.byteSize_eq]; rcases hnD with rfl | rfl | rfl | rfl | rfl <;> rfl
  obtain ⟨alloc', hcopy⟩ := hsrc_shape.copyRepeatedly_range_uninit hnS hnD hpos hinS hinD
    hsrc_uninit hdst_shape (srcId == dstId)
  have hsrc_lt : srcStart < 2^32 := by rcases hnS with rfl | rfl | rfl | rfl | rfl <;> omega
  have hdst_lt : dstStart < 2^32 := by rcases hnD with rfl | rfl | rfl | rfl | rfl <;> omega
  have hinS' : srcStart + total ≤ srcLA.allocation.byteSize.bytes.toNat := by rw [hsrc_sz]; exact hinS
  have hinD' : dstStart + total ≤ dstLA.allocation.byteSize.bytes.toNat := by rw [hdst_sz]; exact hinD
  have heq := annealMemCopy_live_inbounds_eq (st := st) srcId srcTag srcStart srcLA dstId dstTag dstStart dstLA
    hsrc_id hsrc_lt hsrc_base hsrc_live hinS'
    hdst_id hdst_lt hdst_base hdst_live hinD' hpos hle
  rw [hcopy] at heq
  rw [hts] at heq
  exact ⟨_, heq⟩

private theorem lookupAllocMapByTag_mem :
    ∀ {allocMap : List AllocMapEntry} {t : Nat} {e : AllocMapEntry},
      lookupAllocMapByTag allocMap t = some e → e ∈ allocMap ∧ e.tag = t
  | [], _, _, h => by cases h
  | x :: xs, t, e, h => by
    unfold lookupAllocMapByTag at h
    cases hb : Nat.beq x.tag t
    · simp only [hb, Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨hm, ht⟩ := lookupAllocMapByTag_mem h
      exact ⟨List.mem_cons_of_mem x hm, ht⟩
    · simp only [hb, ↓reduceIte] at h
      injection h with he
      subst he
      exact ⟨List.mem_cons_self .., Nat.eq_of_beq_eq_true hb⟩

private theorem writeBytesScalarPreVal_of_val? {locals : List LocalSlot} {op : MirAst.Operand}
    {sc : MirAst.ScalarInt} (h : writeBytesScalarVal? locals op = some sc) :
    WriteBytesScalarPreVal locals op sc := by
  cases op with
  | move _ => cases h
  | constant cc =>
    dsimp only [writeBytesScalarVal?] at h
    cases hval : cc.val with
    | scalar sv =>
      cases sv with
      | int sc₀ =>
        rw [hval] at h; injection h with heq; subst heq
        exact Or.inl ⟨cc, rfl, hval⟩
      | ptr _ _ => rw [hval] at h; cases h
    | _ => rw [hval] at h; cases h
  | copy pl =>
    rcases pl with ⟨idx, proj⟩
    cases proj with
    | cons _ _ => cases h
    | nil =>
      dsimp only [writeBytesScalarVal?] at h
      cases hsl : get? locals idx with
      | none => rw [hsl] at h; cases h
      | some slot =>
        cases slot with
        | dead | uninit => rw [hsl] at h; cases h
        | init v =>
          cases v with
          | scalar sc₀ =>
            rw [hsl] at h; injection h with heq; subst heq
            exact Or.inr ⟨idx, rfl, hsl⟩
          | _ => rw [hsl] at h; cases h

/-- When every positive-byte write through `dstPtr` targets an `.active` borrow
entry whose sibling borrows on the same local are already `.disabled`,
`copyNextAllocMap` leaves `allocMap` unchanged. -/
theorem copyNextAllocMap_eq_self
    {locals : List LocalSlot} {allocMap : List AllocMapEntry}
    {dstIdx : Local} {countOp : MirAst.Operand} {elemBytes : Nat}
    (hact : ∀ dstPtr countSc e_d,
      get? locals dstIdx = some (.init (.ptr dstPtr 8)) →
      WriteBytesScalarPreVal locals countOp countSc →
      0 < countSc.bits * elemBytes →
      e_d ∈ allocMap → e_d.tag = dstPtr.tag →
      ∀ x ∈ allocMap, x.localIdx = e_d.localIdx →
        (x.tag = dstPtr.tag ∧ x.perm = .active) ∨ (x.tag ≠ dstPtr.tag ∧ x.perm = .disabled)) :
    copyNextAllocMap locals allocMap dstIdx countOp elemBytes = allocMap := by
  unfold copyNextAllocMap writeBytesNextAllocMap
  cases hc : writeBytesScalarVal? locals countOp with
  | none => rfl
  | some countSc =>
    dsimp only
    by_cases hz : countSc.bits * elemBytes = 0
    · simp [hz]
    · simp only [hz, ↓reduceIte]
      have hpos : 0 < countSc.bits * elemBytes := Nat.pos_of_ne_zero hz
      have hpre := writeBytesScalarPreVal_of_val? hc
      cases hd : get? locals dstIdx with
      | none => rfl
      | some slot =>
        cases slot with
        | dead | uninit => rfl
        | init v =>
          cases v with
          | ptr dstPtr sz =>
            cases Decidable.em (sz = 8) with
            | inl h8 =>
              subst h8
              cases hl : lookupAllocMapByTag allocMap dstPtr.tag with
              | none => simp [hl]
              | some e_d =>
                simp only [hl]
                obtain ⟨he_d, htag_d⟩ := lookupAllocMapByTag_mem hl
                exact updateAllocMapOnWrite_eq_self_of_active
                  (hact dstPtr countSc e_d hd hpre hpos he_d htag_d)
            | inr hne8 =>
              cases sz with
              | zero => rfl
              | succ k =>
                revert hne8
                match k with
                | 7 => intro h; exact absurd rfl h
                | 0 | 1 | 2 | 3 | 4 | 5 | 6 | _ + 8 => intro _; rfl
          | _ => rfl

/-- **`step_intrinsic_copyNonOverlapping_simulation_same_allocMap` (`LM-4.2`)**:
specialization of `step_intrinsic_copyNonOverlapping_simulation_explicit` that
preserves the exact pre-state `allocMap` (`StepRelLM3_1 body m allocMap ...`)
whenever `dst`'s borrow is `.active` and any foreign borrows of `e_d.localIdx`
are already `.disabled` (or when `count * elemBytes = 0` or the step is UB). -/
theorem step_intrinsic_copyNonOverlapping_simulation_same_allocMap
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
    (htgt_compat : ∀ srcPtr dstPtr e_s e_d decl_s decl_d,
      get? s.frame.locals srcIdx = some (.init (.ptr srcPtr 8)) →
      get? s.frame.locals dstIdx = some (.init (.ptr dstPtr 8)) →
      e_s ∈ allocMap → e_s.tag = srcPtr.tag →
      e_d ∈ allocMap → e_d.tag = dstPtr.tag →
      get? body.localDecls e_s.localIdx = some decl_s →
      get? body.localDecls e_d.localIdx = some decl_d →
      0 < elemBytes →
      CopyTargetCompatible decl_s decl_d pointeeTy.kind)
    (hlive_ok : ∀ srcPtr dstPtr countSc e_s e_d decl_s decl_d srcBytes dstBytes,
      get? s.frame.locals srcIdx = some (.init (.ptr srcPtr 8)) →
      get? s.frame.locals dstIdx = some (.init (.ptr dstPtr 8)) →
      WriteBytesScalarPreVal s.frame.locals countOp countSc →
      0 < countSc.bits * elemBytes →
      countSc.bits * elemBytes ≤ isizeMaxBytes →
      e_s ∈ allocMap → e_s.tag = srcPtr.tag →
      e_d ∈ allocMap → e_d.tag = dstPtr.tag →
      get? body.localDecls e_s.localIdx = some decl_s →
      get? body.localDecls e_d.localIdx = some decl_d →
      rigidTyByteSize body.layouts decl_s.ty = some srcBytes →
      rigidTyByteSize body.layouts decl_d.ty = some dstBytes →
      srcPtr.offsetBytes + countSc.bits * elemBytes ≤ srcBytes →
      dstPtr.offsetBytes + countSc.bits * elemBytes ≤ dstBytes →
      get? s.frame.locals e_s.localIdx ≠ some .dead →
      get? s.frame.locals e_d.localIdx ≠ some .dead →
      e_s.perm ≠ .disabled ∧
        (e_d.perm = .active ∨ e_d.perm = .reserved) ∧
        get? s.frame.locals e_s.localIdx ≠ some .uninit ∧
        ((dstPtr.offsetBytes = 0 ∧ countSc.bits * elemBytes = dstBytes) ∨
          get? s.frame.locals e_d.localIdx ≠ some .uninit))
    (hact : ∀ dstPtr countSc e_d,
      get? s.frame.locals dstIdx = some (.init (.ptr dstPtr 8)) →
      WriteBytesScalarPreVal s.frame.locals countOp countSc →
      0 < countSc.bits * elemBytes →
      e_d ∈ allocMap → e_d.tag = dstPtr.tag →
      ∀ x ∈ allocMap, x.localIdx = e_d.localIdx →
        (x.tag = dstPtr.tag ∧ x.perm = .active) ∨ (x.tag ≠ dstPtr.tag ∧ x.perm = .disabled)) :
    StepRelLM3_1 body m allocMap
      (stepMirFnLM4_2 body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  rw [← copyNextAllocMap_eq_self hact]
  exact step_intrinsic_copyNonOverlapping_simulation_explicit hstate hphase hbb hstmt
    hsrcDecl hsrcTy hsrcImm hdstDecl hdstTy hdstImm hcountInt hcountOp hpt
    htgt_compat hlive_ok

/-- **General byte-range uninitialized-source divergence (`LM-4.2`)**: copying any
positive number of elements (`0 < countSc.bits * elemBytes`, arbitrary `count`
and arbitrary aligned byte offsets `srcPtr.offsetBytes`, `dstPtr.offsetBytes`
with `srcPtr.offsetBytes + countSc.bits * elemBytes ≤ srcBytes` and
`dstPtr.offsetBytes + countSc.bits * elemBytes ≤ dstBytes`) from an
uninitialized (`.uninit`) live integral stack local `e_s.localIdx` into a live
integral stack local `e_d.localIdx`:

* Anneal's typed `evalCopyRootIntScalars` rejects reading `.uninit` for an
  integral local (`stepMirFnLM4_2 body s = MirStepNode.fail .ub`);
* `lean-miri`'s untyped `Allocation.copyRepeatedly` copies the uninitialized
  byte mask via `initialized.noBytesInit` (`Allocation.writeUninit`) and steps
  with `.ok true`. -/
theorem step_intrinsic_copyNonOverlapping_uninit_src_range_divergence
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {srcIdx dstIdx : Local} {countOp : MirAst.Operand} {span : String}
    {srcDecl dstDecl : LocalDecl} {srcMut dstMut : Mutability} {pointeeTy countTy : Ty}
    {ptId : Miri.MIR.TyId} {elemBytes elemAlign : Nat}
    {srcPtr dstPtr : ProvenancePtr} {countSc : MirAst.ScalarInt}
    {e_s e_d : AllocMapEntry} {decl_s decl_d : LocalDecl}
    {srcKind dstKind : Miri.MIR.IntegerKind}
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
    (halS : ptrValueAligned elemAlign (.ptr srcPtr 8) = true)
    (halD : ptrValueAligned elemAlign (.ptr dstPtr 8) = true)
    (hcnt_pre : WriteBytesScalarPreVal s.frame.locals countOp countSc)
    (hpos : 0 < countSc.bits * elemBytes)
    (he_s : e_s ∈ allocMap) (het_s : e_s.tag = srcPtr.tag)
    (he_d : e_d ∈ allocMap) (het_d : e_d.tag = dstPtr.tag)
    (hdecl_s : get? body.localDecls e_s.localIdx = some decl_s)
    (hdecl_d : get? body.localDecls e_d.localIdx = some decl_d)
    (hsrcInt : IsIntegralTy decl_s.ty srcKind)
    (hdstInt : IsIntegralTy decl_d.ty dstKind)
    (hinS : srcPtr.offsetBytes + countSc.bits * elemBytes ≤ integerKindByteWidth srcKind)
    (hinD : dstPtr.offsetBytes + countSc.bits * elemBytes ≤ integerKindByteWidth dstKind)
    (huninit_s : get? s.frame.locals e_s.localIdx = some .uninit)
    (hdst_live : get? s.frame.locals e_d.localIdx ≠ some .dead) :
    stepMirFnLM4_2 body s = MirStepNode.fail .ub ∧
    ∃ m',
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .ok true) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, _, _⟩ := id hstate
  have hanneal_step : stepMirFnLM4_2 body s =
      evalCopyNonOverlappingLM4_2 s (.copy ⟨srcIdx, []⟩) (.copy ⟨dstIdx, []⟩) countOp
        body.localDecls body.layouts := by
    rw [stepMirFnLM4_2_eq_of_not_other body s hcal hphase]
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
  rcases annealEvalOperand_rawPtr_lm3_1 hstate hframes hsrcDecl hsrcTy (hsrcImm tf hframes) with
    ⟨hd, _⟩ | ⟨_, hun, _⟩ | ⟨_, _, _, hsc, _⟩ |
    ⟨srcPtr', mptr_s, tf₁, hsrc_ptr, hptrRel_s, hm₁, hstate₁, hvals₁⟩
  · rw [hsrc_val] at hd; cases hd
  · rw [hsrc_val] at hun; cases hun
  · rw [hsrc_val] at hsc; cases hsc
  · rw [hsrc_val] at hsrc_ptr; cases hsrc_ptr
    rcases annealEvalOperand_rawPtr_lm3_1 hstate₁ rfl hdstDecl hdstTy
        (IsImmediateFrameLocal.of_values_eq hvals₁ (hdstImm tf hframes)) with
      ⟨hd, _⟩ | ⟨_, hun, _⟩ | ⟨_, _, _, hsc, _⟩ |
      ⟨dstPtr', mptr_d, tf₂, hdst_ptr, hptrRel_d, hm₂, hstate₂, hvals₂⟩
    · rw [hdst_val] at hd; cases hd
    · rw [hdst_val] at hun; cases hun
    · rw [hdst_val] at hsc; cases hsc
    · rw [hdst_val] at hdst_ptr; cases hdst_ptr
      have himm₂ : ∀ j, IsImmediateFrameLocal tf j → IsImmediateFrameLocal tf₂ j :=
        fun j hj => IsImmediateFrameLocal.of_values_eq hvals₂
          (IsImmediateFrameLocal.of_values_eq hvals₁ hj)
      rcases annealEvalOperand_scalar_lm3_1 hstate₂ rfl ((hcountOp tf hframes).mono_immediate himm₂)
          hcountInt.prim with
        ⟨_, _, ha₃', _⟩ | ⟨_, ha₃', _⟩ |
        ⟨countSc', mcount, tf₃, ha₃', hm₃, hstate₃, hrelI_c, _⟩
      · rw [ha₃] at ha₃'; cases ha₃'
      · rw [ha₃] at ha₃'; cases ha₃'
      · rw [ha₃] at ha₃'; cases ha₃'
        obtain ⟨tf₃', hframes₃, _, _, hfr₃, _, _, _, _, _, halloc, _⟩ := id hstate₃
        cases hframes₃
        obtain ⟨hrelC, hszC⟩ := copyImmediateRel_of_integral hcountInt hrelI_c
        obtain ⟨hrig_s, htr_s, hvalid_s⟩ := hsrcInt.size_spec body.layouts
        obtain ⟨hrig_d, htr_d, hvalid_d⟩ := hdstInt.size_spec body.layouts
        have hle : countSc.bits * elemBytes ≤ isizeMaxBytes := by
          unfold isizeMaxBytes
          have : integerKindByteWidth srcKind ≤ 16 := by cases srcKind <;> decide
          omega
        have hlook_s : lookupBorrow s.memory.borrows srcPtr.tag = some e_s.toBorrowEntry := by
          rw [← het_s]; exact (halloc.borrow_sync e_s he_s).2
        have hlook_d : lookupBorrow s.memory.borrows dstPtr.tag = some e_d.toBorrowEntry := by
          rw [← het_d]; exact (halloc.borrow_sync e_d he_d).2
        have hopS := operandPointeeTy_copy_rawPtr (layouts := body.layouts) hsrcDecl hsrcTy
        have ha_int := evalCopyNonOverlappingWithCount_int_reduce hopS
          hpt.wb.anneal_size hpt.anneal_align hle hpos halS halD
          hlook_s hdecl_s hrig_s hsrcInt.intCastTargetBytes_eq
          hlook_d hdecl_d hrig_d hdstInt.intCastTargetBytes_eq
          (dst := .copy ⟨dstIdx, []⟩)
        refine ⟨?_, ?_⟩
        · rw [hanneal_step]; unfold evalCopyNonOverlappingLM4_2
          rw [ha₁]; dsimp only; rw [ha₂]; dsimp only; rw [ha₃]; dsimp only
          rw [ha_int, copyIte_pos ⟨hinS, hinD⟩, evalCopyRootIntScalars_uninit_src_ub huninit_s]
          cases e_s.perm <;> cases e_d.perm <;> rfl
        · have hchkS := annealCheckPtrAlign_stackPtr hstate₃ rfl hpt.align_pair hptrRel_s
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
                (Miri.ABI.Size.ofBytes (UInt64.ofNat (countSc.bits * elemBytes))) true
                { m with stack := ⟨#[tf₃]⟩ } := by
            unfold copyMiriStmtAction
            rw [EStateM.bind_eq_ok hm₁, EStateM.bind_eq_ok hm₂, EStateM.bind_eq_ok hm₃,
              hm_ev, EStateM.bind_eq_ok hchkS, EStateM.bind_eq_ok hchkD]
          rcases hptrRel_s with
            ⟨srcId, srcBorTag, hprov_s, hid_s, _, haddr_s, e_s', he_s', het_s', hea_s'⟩
          rcases hptrRel_d with
            ⟨dstId, dstBorTag, hprov_d, hid_d, _, haddr_d, e_d', he_d', het_d', hea_d'⟩
          have hes_eq : e_s' = e_s := Option.some.inj
            ((copyLookupAllocMapByTag_of_mem_nodup halloc.tags_nodup he_s' het_s').symm.trans
              (copyLookupAllocMapByTag_of_mem_nodup halloc.tags_nodup he_s het_s))
          have hed_eq : e_d' = e_d := Option.some.inj
            ((copyLookupAllocMapByTag_of_mem_nodup halloc.tags_nodup he_d' het_d').symm.trans
              (copyLookupAllocMapByTag_of_mem_nodup halloc.tags_nodup he_d het_d))
          rw [hes_eq] at hea_s'
          rw [hed_eq] at hea_d'
          have hp_s_eq : mptr_s.withOptionalProvenance =
              ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr srcId + UInt64.ofNat srcPtr.offsetBytes),
                some (.concrete srcId srcBorTag)⟩ := by
            rcases mptr_s with ⟨o, pr⟩
            dsimp only [Miri.Memory.Pointer.withOptionalProvenance] at haddr_s hprov_s ⊢
            subst haddr_s hprov_s; rfl
          have hp_d_eq : mptr_d.withOptionalProvenance =
              ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr dstId + UInt64.ofNat dstPtr.offsetBytes),
                some (.concrete dstId dstBorTag)⟩ := by
            rcases mptr_d with ⟨o, pr⟩
            dsimp only [Miri.Memory.Pointer.withOptionalProvenance] at haddr_d hprov_d ⊢
            subst haddr_d hprov_d; rfl
          rw [hp_s_eq, hp_d_eq] at hm_mem
          have hbase_s : m.machine.lookupBaseAddr srcId = some (annealStackBaseAddr srcId) := by
            rw [← hea_s']; exact (halloc.base_addr_valid e_s he_s).2.2
          have hbase_d : m.machine.lookupBaseAddr dstId = some (annealStackBaseAddr dstId) := by
            rw [← hea_d']; exact (halloc.base_addr_valid e_d he_d).2.2
          obtain ⟨slot_s, mls_s, _, _, hslot_s, hmls_s, _, hloc_s⟩ := hfr₃.lookup_local hdecl_s
          obtain ⟨slot_d, _, _, _, hslot_d, _, _, _⟩ := hfr₃.lookup_local hdecl_d
          have hs_un : slot_s = .uninit := Option.some.inj (hslot_s.symm.trans huninit_s)
          have hd_s : slot_s ≠ .dead := by rw [hs_un]; nofun
          have hd_d : slot_d ≠ .dead := fun h => hdst_live (hslot_d.trans (congrArg some h))
          obtain ⟨⟨lay_s, hlay_s⟩, _, hshape_fn_s⟩ :=
            (halloc.local_alloc_sync tf₃ rfl e_s he_s).1 slot_s hslot_s hd_s
          obtain ⟨srcLA, hfind_s', _, _, hshape_s'⟩ := hshape_fn_s decl_s hdecl_s
          have hfind_s : m.machine.memory.live.find? (fun x => x.1 == srcId) =
              some (srcId, srcLA) := by rw [← hea_s']; exact hfind_s'
          have hshape_s : StackScalarAllocShape (translateSizeBytes (integerKindByteWidth srcKind))
              srcLA.allocation := htr_s ▸ hshape_s'
          obtain ⟨_, _, hshape_fn_d⟩ :=
            (halloc.local_alloc_sync tf₃ rfl e_d he_d).1 slot_d hslot_d hd_d
          obtain ⟨dstLA, hfind_d', _, _, hshape_d'⟩ := hshape_fn_d decl_d hdecl_d
          have hfind_d : m.machine.memory.live.find? (fun x => x.1 == dstId) =
              some (dstId, dstLA) := by rw [← hea_d']; exact hfind_d'
          have hshape_d : StackScalarAllocShape (translateSizeBytes (integerKindByteWidth dstKind))
              dstLA.allocation := htr_d ▸ hshape_d'
          have hmls_s_eq : mls_s = ⟨.live (.indirect (stackAllocPlace e_s.allocId)), lay_s⟩ := by
            rw [hlay_s] at hmls_s; exact Option.some.inj hmls_s.symm
          have hnz_sz_s : (translateTy decl_s.ty body.layouts).layout.size ≠
              Miri.ABI.Size.ZERO := by
            rw [htr_s]; cases srcKind <;> decide
          obtain ⟨hun_spec, _⟩ := hloc_s.indirect_stackAllocPlace_spec hmls_s_eq
            (halloc.base_addr_valid e_s he_s).2.2 hfind_s'
            (halloc.live_key_unique e_s he_s) hnz_sz_s
          have hni := hun_spec hs_un
          rw [htr_s] at hni
          have hmask_false : srcLA.allocation.initializationMask =
              Miri.Memory.InitMask.new (translateSizeBytes (integerKindByteWidth srcKind)) false := by
            obtain ⟨_, _, _, _, bS, hmaskS⟩ := hshape_s
            cases bS with
            | false => exact hmaskS
            | true =>
              exfalso; apply hni; rw [hmaskS]
              cases srcKind <;> rfl
          obtain ⟨mach', hmc⟩ := annealMemCopy_live_uninit_range_ok
            (st := { m with stack := ⟨#[tf₃]⟩ }) hvalid_s hvalid_d hpos hinS hinD
            srcId srcBorTag srcLA dstId dstBorTag dstLA
            hid_s hbase_s hfind_s hshape_s hmask_false
            hid_d hbase_d hfind_d hshape_d
          have hm_act : copyMiriStmtAction body srcIdx dstIdx countOp m =
              .ok () { stack := ⟨#[tf₃]⟩, machine := mach' } := by
            rw [hm_mem]; exact hmc
          exact ⟨_, copyStep_miri_ok hframes hfr.body_eq hfr.location_eq hfr₃.location_eq
            hbb hstmt hm_act⟩

/-- **General byte-range Tree Borrows permission divergence (`LM-4.2`)**:
copying any positive number of elements (`0 < countSc.bits * elemBytes`,
arbitrary `count` and arbitrary aligned byte offsets `srcPtr.offsetBytes`,
`dstPtr.offsetBytes` with `srcPtr.offsetBytes + countSc.bits * elemBytes ≤ srcBytes`
and `dstPtr.offsetBytes + countSc.bits * elemBytes ≤ dstBytes`) between live
integral stack locals `e_s.localIdx` and `e_d.localIdx` (on distinct locals, or
disjoint byte sub-ranges of the same local, with `dst` either wholly overwritten
or already initialized) when `e_s.perm = .disabled` or `e_d.perm` is `.frozen` /
`.disabled`:

* Anneal enforces Tree Borrows read permission on `src` and write permission on
  `dst` (`stepMirFnLM4_2 body s = MirStepNode.fail .ub`);
* `lean-miri` under `annealMemoryCopyHooks` (pre-`LM-3.3` Tree Borrows) checks
  only allocation mutability and steps with `.ok true`. -/
theorem step_intrinsic_copyNonOverlapping_perm_range_divergence
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {srcIdx dstIdx : Local} {countOp : MirAst.Operand} {span : String}
    {srcDecl dstDecl : LocalDecl} {srcMut dstMut : Mutability} {pointeeTy countTy : Ty}
    {ptId : Miri.MIR.TyId} {elemBytes elemAlign : Nat}
    {srcPtr dstPtr : ProvenancePtr} {countSc : MirAst.ScalarInt}
    {e_s e_d : AllocMapEntry} {decl_s decl_d : LocalDecl}
    {srcKind dstKind : Miri.MIR.IntegerKind}
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
    (halS : ptrValueAligned elemAlign (.ptr srcPtr 8) = true)
    (halD : ptrValueAligned elemAlign (.ptr dstPtr 8) = true)
    (hcnt_pre : WriteBytesScalarPreVal s.frame.locals countOp countSc)
    (hpos : 0 < countSc.bits * elemBytes)
    (he_s : e_s ∈ allocMap) (het_s : e_s.tag = srcPtr.tag)
    (he_d : e_d ∈ allocMap) (het_d : e_d.tag = dstPtr.tag)
    (hdecl_s : get? body.localDecls e_s.localIdx = some decl_s)
    (hdecl_d : get? body.localDecls e_d.localIdx = some decl_d)
    (hsrcInt : IsIntegralTy decl_s.ty srcKind)
    (hdstInt : IsIntegralTy decl_d.ty dstKind)
    (hinS : srcPtr.offsetBytes + countSc.bits * elemBytes ≤ integerKindByteWidth srcKind)
    (hinD : dstPtr.offsetBytes + countSc.bits * elemBytes ≤ integerKindByteWidth dstKind)
    (hdisj : e_s.localIdx = e_d.localIdx →
      srcPtr.offsetBytes + countSc.bits * elemBytes ≤ dstPtr.offsetBytes ∨
      dstPtr.offsetBytes + countSc.bits * elemBytes ≤ srcPtr.offsetBytes)
    (hsrc_live : get? s.frame.locals e_s.localIdx ≠ some .dead)
    (hdst_live : get? s.frame.locals e_d.localIdx ≠ some .dead)
    (hdst_init : (dstPtr.offsetBytes = 0 ∧
        countSc.bits * elemBytes = integerKindByteWidth dstKind) ∨
      get? s.frame.locals e_d.localIdx ≠ some .uninit)
    (hperm_bad : e_s.perm = .disabled ∨ e_d.perm = .frozen ∨ e_d.perm = .disabled) :
    stepMirFnLM4_2 body s = MirStepNode.fail .ub ∧
    ∃ m',
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .ok true) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, _, _⟩ := id hstate
  have hanneal_step : stepMirFnLM4_2 body s =
      evalCopyNonOverlappingLM4_2 s (.copy ⟨srcIdx, []⟩) (.copy ⟨dstIdx, []⟩) countOp
        body.localDecls body.layouts := by
    rw [stepMirFnLM4_2_eq_of_not_other body s hcal hphase]
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
  rcases annealEvalOperand_rawPtr_lm3_1 hstate hframes hsrcDecl hsrcTy (hsrcImm tf hframes) with
    ⟨hd, _⟩ | ⟨_, hun, _⟩ | ⟨_, _, _, hsc, _⟩ |
    ⟨srcPtr', mptr_s, tf₁, hsrc_ptr, hptrRel_s, hm₁, hstate₁, hvals₁⟩
  · rw [hsrc_val] at hd; cases hd
  · rw [hsrc_val] at hun; cases hun
  · rw [hsrc_val] at hsc; cases hsc
  · rw [hsrc_val] at hsrc_ptr; cases hsrc_ptr
    rcases annealEvalOperand_rawPtr_lm3_1 hstate₁ rfl hdstDecl hdstTy
        (IsImmediateFrameLocal.of_values_eq hvals₁ (hdstImm tf hframes)) with
      ⟨hd, _⟩ | ⟨_, hun, _⟩ | ⟨_, _, _, hsc, _⟩ |
      ⟨dstPtr', mptr_d, tf₂, hdst_ptr, hptrRel_d, hm₂, hstate₂, hvals₂⟩
    · rw [hdst_val] at hd; cases hd
    · rw [hdst_val] at hun; cases hun
    · rw [hdst_val] at hsc; cases hsc
    · rw [hdst_val] at hdst_ptr; cases hdst_ptr
      have himm₂ : ∀ j, IsImmediateFrameLocal tf j → IsImmediateFrameLocal tf₂ j :=
        fun j hj => IsImmediateFrameLocal.of_values_eq hvals₂
          (IsImmediateFrameLocal.of_values_eq hvals₁ hj)
      rcases annealEvalOperand_scalar_lm3_1 hstate₂ rfl ((hcountOp tf hframes).mono_immediate himm₂)
          hcountInt.prim with
        ⟨_, _, ha₃', _⟩ | ⟨_, ha₃', _⟩ |
        ⟨countSc', mcount, tf₃, ha₃', hm₃, hstate₃, hrelI_c, _⟩
      · rw [ha₃] at ha₃'; cases ha₃'
      · rw [ha₃] at ha₃'; cases ha₃'
      · rw [ha₃] at ha₃'; cases ha₃'
        obtain ⟨tf₃', hframes₃, _, _, hfr₃, _, _, _, _, _, halloc, _⟩ := id hstate₃
        cases hframes₃
        obtain ⟨hrelC, hszC⟩ := copyImmediateRel_of_integral hcountInt hrelI_c
        let srcBytes := integerKindByteWidth srcKind
        let dstBytes := integerKindByteWidth dstKind
        let total := countSc.bits * elemBytes
        obtain ⟨hrig_s, htr_s, hvalid_s⟩ := hsrcInt.size_spec body.layouts
        obtain ⟨hrig_d, htr_d, hvalid_d⟩ := hdstInt.size_spec body.layouts
        have hle : countSc.bits * elemBytes ≤ isizeMaxBytes := by
          unfold isizeMaxBytes
          have : srcBytes ≤ 16 := by dsimp [srcBytes]; cases srcKind <;> decide
          omega
        have hlook_s : lookupBorrow s.memory.borrows srcPtr.tag = some e_s.toBorrowEntry := by
          rw [← het_s]; exact (halloc.borrow_sync e_s he_s).2
        have hlook_d : lookupBorrow s.memory.borrows dstPtr.tag = some e_d.toBorrowEntry := by
          rw [← het_d]; exact (halloc.borrow_sync e_d he_d).2
        have hopS := operandPointeeTy_copy_rawPtr (layouts := body.layouts) hsrcDecl hsrcTy
        have ha_int := evalCopyNonOverlappingWithCount_int_reduce hopS
          hpt.wb.anneal_size hpt.anneal_align hle hpos halS halD
          hlook_s hdecl_s hrig_s hsrcInt.intCastTargetBytes_eq
          hlook_d hdecl_d hrig_d hdstInt.intCastTargetBytes_eq
          (dst := .copy ⟨dstIdx, []⟩)
        refine ⟨?_, ?_⟩
        · rw [hanneal_step]; unfold evalCopyNonOverlappingLM4_2
          rw [ha₁]; dsimp only; rw [ha₂]; dsimp only; rw [ha₃]; dsimp only
          rw [ha_int, copyIte_pos ⟨hinS, hinD⟩]
          cases hpS : e_s.perm <;> cases hpD : e_d.perm <;>
            first | rfl | (simp [hpS, hpD] at hperm_bad)
        · have hchkS := annealCheckPtrAlign_stackPtr hstate₃ rfl hpt.align_pair hptrRel_s
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
                (Miri.ABI.Size.ofBytes (UInt64.ofNat total)) true
                { m with stack := ⟨#[tf₃]⟩ } := by
            unfold copyMiriStmtAction
            rw [EStateM.bind_eq_ok hm₁, EStateM.bind_eq_ok hm₂, EStateM.bind_eq_ok hm₃,
              hm_ev, EStateM.bind_eq_ok hchkS, EStateM.bind_eq_ok hchkD]
          rcases hptrRel_s with
            ⟨srcId, srcBorTag, hprov_s, hid_s, hoff_s, haddr_s, e_s', he_s', het_s', hea_s'⟩
          rcases hptrRel_d with
            ⟨dstId, dstBorTag, hprov_d, hid_d, hoff_d, haddr_d, e_d', he_d', het_d', hea_d'⟩
          have hes_eq : e_s' = e_s := Option.some.inj
            ((copyLookupAllocMapByTag_of_mem_nodup halloc.tags_nodup he_s' het_s').symm.trans
              (copyLookupAllocMapByTag_of_mem_nodup halloc.tags_nodup he_s het_s))
          have hed_eq : e_d' = e_d := Option.some.inj
            ((copyLookupAllocMapByTag_of_mem_nodup halloc.tags_nodup he_d' het_d').symm.trans
              (copyLookupAllocMapByTag_of_mem_nodup halloc.tags_nodup he_d het_d))
          rw [hes_eq] at hea_s'
          rw [hed_eq] at hea_d'
          have hp_s_eq : mptr_s.withOptionalProvenance =
              ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr srcId + UInt64.ofNat srcPtr.offsetBytes),
                some (.concrete srcId srcBorTag)⟩ := by
            rcases mptr_s with ⟨o, pr⟩
            dsimp only [Miri.Memory.Pointer.withOptionalProvenance] at haddr_s hprov_s ⊢
            subst haddr_s hprov_s; rfl
          have hp_d_eq : mptr_d.withOptionalProvenance =
              ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr dstId + UInt64.ofNat dstPtr.offsetBytes),
                some (.concrete dstId dstBorTag)⟩ := by
            rcases mptr_d with ⟨o, pr⟩
            dsimp only [Miri.Memory.Pointer.withOptionalProvenance] at haddr_d hprov_d ⊢
            subst haddr_d hprov_d; rfl
          rw [hp_s_eq, hp_d_eq] at hm_mem
          have hbase_s : m.machine.lookupBaseAddr srcId = some (annealStackBaseAddr srcId) := by
            rw [← hea_s']; exact (halloc.base_addr_valid e_s he_s).2.2
          have hbase_d : m.machine.lookupBaseAddr dstId = some (annealStackBaseAddr dstId) := by
            rw [← hea_d']; exact (halloc.base_addr_valid e_d he_d).2.2
          obtain ⟨slot_s, mls_s, _, _, hslot_s, hmls_s, _, hloc_s⟩ := hfr₃.lookup_local hdecl_s
          obtain ⟨slot_d, mls_d, _, _, hslot_d, hmls_d, _, hloc_d⟩ := hfr₃.lookup_local hdecl_d
          have hd_s : slot_s ≠ .dead := fun h => hsrc_live (hslot_s.trans (congrArg some h))
          have hd_d : slot_d ≠ .dead := fun h => hdst_live (hslot_d.trans (congrArg some h))
          obtain ⟨⟨lay_s, hlay_s⟩, hsc_only_s, hshape_fn_s⟩ :=
            (halloc.local_alloc_sync tf₃ rfl e_s he_s).1 slot_s hslot_s hd_s
          obtain ⟨srcLA, hfind_s', _, _, hshape_s'⟩ := hshape_fn_s decl_s hdecl_s
          have hfind_s : m.machine.memory.live.find? (fun x => x.1 == srcId) =
              some (srcId, srcLA) := by rw [← hea_s']; exact hfind_s'
          have hshape_s : StackScalarAllocShape (translateSizeBytes srcBytes)
              srcLA.allocation := htr_s ▸ hshape_s'
          obtain ⟨⟨lay_d, hlay_d⟩, hsc_only_d, hshape_fn_d⟩ :=
            (halloc.local_alloc_sync tf₃ rfl e_d he_d).1 slot_d hslot_d hd_d
          obtain ⟨dstLA, hfind_d', _, _, hshape_d'⟩ := hshape_fn_d decl_d hdecl_d
          have hfind_d : m.machine.memory.live.find? (fun x => x.1 == dstId) =
              some (dstId, dstLA) := by rw [← hea_d']; exact hfind_d'
          have hshape_d : StackScalarAllocShape (translateSizeBytes dstBytes)
              dstLA.allocation := htr_d ▸ hshape_d'
          have hts_s : (translateSizeBytes srcBytes).bytes.toNat = srcBytes := by
            dsimp only [srcBytes]; rcases hvalid_s with h0 | h0 | h0 | h0 | h0 <;> (rw [h0]; rfl)
          have hts_d : (translateSizeBytes dstBytes).bytes.toNat = dstBytes := by
            dsimp only [dstBytes]; rcases hvalid_d with h0 | h0 | h0 | h0 | h0 <;> (rw [h0]; rfl)
          have hsz_la_s : srcLA.allocation.byteSize.bytes.toNat = srcBytes := by
            rw [hshape_s.byteSize_eq, hts_s]
          have hsz_la_d : dstLA.allocation.byteSize.bytes.toNat = dstBytes := by
            rw [hshape_d.byteSize_eq, hts_d]
          have hmls_s_eq : mls_s = ⟨.live (.indirect (stackAllocPlace e_s.allocId)), lay_s⟩ := by
            rw [hlay_s] at hmls_s; exact Option.some.inj hmls_s.symm
          have hnz_sz_s : (translateTy decl_s.ty body.layouts).layout.size ≠
              Miri.ABI.Size.ZERO := by
            rw [htr_s]; cases srcKind <;> decide
          obtain ⟨hun_spec, hsc_spec⟩ := hloc_s.indirect_stackAllocPlace_spec hmls_s_eq
            (halloc.base_addr_valid e_s he_s).2.2 hfind_s'
            (halloc.live_key_unique e_s he_s) hnz_sz_s
          have hm_copy : ∃ mach', copyMiriStmtAction body srcIdx dstIdx countOp m =
              .ok () { stack := ⟨#[tf₃]⟩, machine := mach' } := by
            cases hs_case : slot_s with
            | dead => exact absurd hs_case hd_s
            | uninit =>
              have hni := hun_spec hs_case
              rw [htr_s] at hni
              have hmask_false : srcLA.allocation.initializationMask =
                  Miri.Memory.InitMask.new (translateSizeBytes srcBytes) false := by
                obtain ⟨_, _, _, _, bS, hmaskS⟩ := hshape_s
                cases bS with
                | false => exact hmaskS
                | true =>
                  exfalso; apply hni; rw [hmaskS]
                  cases srcKind <;> rfl
              obtain ⟨mach', hmc⟩ := annealMemCopy_live_uninit_range_ok
                (st := { m with stack := ⟨#[tf₃]⟩ }) hvalid_s hvalid_d hpos hinS hinD
                srcId srcBorTag srcLA dstId dstBorTag dstLA
                hid_s hbase_s hfind_s hshape_s hmask_false
                hid_d hbase_d hfind_d hshape_d
              exact ⟨mach', by rw [hm_mem]; exact hmc⟩
            | init v_s =>
              obtain ⟨sc_s, rfl⟩ := hsc_only_s v_s hs_case
              obtain ⟨hsz_sc_eq, _, _, msc_s, hrel_sc, hread_s⟩ := hsc_spec sc_s hs_case
              have hsc_bytes : sc_s.sizeBytes = srcBytes := by
                have h := htr_s.symm.trans hsz_sc_eq
                have h1 : (translateSizeBytes sc_s.sizeBytes).bytes.toNat = sc_s.sizeBytes := by
                  rcases hrel_sc.validBytes with h0 | h0 | h0 | h0 | h0 <;> (rw [h0]; rfl)
                have h2 := congrArg (fun z : Miri.ABI.Size => z.bytes.toNat) h
                rw [hts_s, h1] at h2
                exact h2.symm
              rw [htr_s] at hread_s
              have hdisj_same : (srcId == dstId) = true →
                  srcPtr.offsetBytes + total ≤ dstPtr.offsetBytes ∨
                  dstPtr.offsetBytes + total ≤ srcPtr.offsetBytes := by
                intro hbeq
                have hid_eq : e_s.allocId = e_d.allocId :=
                  hea_s'.trans ((eq_of_beq hbeq).trans hea_d'.symm)
                exact hdisj (halloc.alloc_to_local_injective e_s he_s e_d he_d hid_eq)
              by_cases hwhole : dstPtr.offsetBytes = 0 ∧ total = dstBytes
              · obtain ⟨hoff0_d, htot_eq⟩ := hwhole
                have hne_id : srcId ≠ dstId := by
                  intro hid_eq
                  have hsame := halloc.alloc_to_local_injective e_s he_s e_d he_d
                    (hea_s'.trans (hid_eq.trans hea_d'.symm))
                  have hdecl_eq : decl_s = decl_d :=
                    Option.some.inj (hdecl_s.symm.trans (hsame ▸ hdecl_d))
                  have hsz_eq_sd : srcBytes = dstBytes :=
                    Option.some.inj (hrig_s.symm.trans (hdecl_eq ▸ hrig_d))
                  rcases hdisj hsame with hd | hd <;> omega
                have hinS_d : srcPtr.offsetBytes + dstBytes ≤ srcBytes := htot_eq ▸ hinS
                obtain ⟨alloc', _, hcopy_ok, _, _, _, _, _⟩ :=
                  hshape_s.copyRepeatedly_range_whole_dst hvalid_s hvalid_d
                    hrel_sc hsc_bytes hinS_d hshape_d hread_s
                have hm_eq := annealMemCopy_live_inbounds_eq
                  (st := { m with stack := ⟨#[tf₃]⟩ })
                  srcId srcBorTag srcPtr.offsetBytes srcLA
                  dstId dstBorTag 0 dstLA
                  hid_s hoff_s hbase_s hfind_s (hsz_la_s ▸ hinS_d)
                  hid_d (by decide) hbase_d hfind_d (by omega)
                  (htot_eq ▸ hpos) (htot_eq ▸ hle)
                rw [beq_false_of_ne hne_id, hcopy_ok] at hm_eq
                exact ⟨_, by rw [hm_mem, show total = dstBytes from htot_eq, hoff0_d]; exact hm_eq⟩
              · have hnot_un_d : get? s.frame.locals e_d.localIdx ≠ some .uninit := by
                  rcases hdst_init with hw | hnu
                  · exact absurd hw hwhole
                  · exact hnu
                have hd_init : ∃ sc_d, slot_d = .init (.scalar sc_d) := by
                  cases hd_case : slot_d with
                  | dead => exact absurd hd_case hd_d
                  | uninit => exact absurd (hslot_d.trans (congrArg some hd_case)) hnot_un_d
                  | init v =>
                    obtain ⟨sc_d, rfl⟩ := hsc_only_d v hd_case
                    exact ⟨sc_d, rfl⟩
                obtain ⟨sc_d, hsd_eq⟩ := hd_init
                have hmls_d_eq : mls_d = ⟨.live (.indirect (stackAllocPlace e_d.allocId)), lay_d⟩ := by
                  rw [hlay_d] at hmls_d; exact Option.some.inj hmls_d.symm
                have hnz_sz_d : (translateTy decl_d.ty body.layouts).layout.size ≠
                    Miri.ABI.Size.ZERO := by
                  rw [htr_d]; cases dstKind <;> decide
                obtain ⟨_, hsc_spec_d⟩ := hloc_d.indirect_stackAllocPlace_spec hmls_d_eq
                  (halloc.base_addr_valid e_d he_d).2.2 hfind_d'
                  (halloc.live_key_unique e_d he_d) hnz_sz_d
                obtain ⟨hsz_scd_eq, _, _, msc_d, hrel_scd, hread_d⟩ := hsc_spec_d sc_d hsd_eq
                have hscd_bytes : sc_d.sizeBytes = dstBytes := by
                  have h := htr_d.symm.trans hsz_scd_eq
                  have h1 : (translateSizeBytes sc_d.sizeBytes).bytes.toNat = sc_d.sizeBytes := by
                    rcases hrel_scd.validBytes with h0 | h0 | h0 | h0 | h0 <;> (rw [h0]; rfl)
                  have h2 := congrArg (fun z : Miri.ABI.Size => z.bytes.toNat) h
                  rw [hts_d, h1] at h2
                  exact h2.symm
                rw [htr_d] at hread_d
                obtain ⟨alloc', _, hcopy_ok, _, _, _, _, _⟩ :=
                  hshape_s.copyRepeatedly_range_partial_dst hvalid_s hvalid_d
                    hrel_sc hsc_bytes hrel_scd hscd_bytes hpos hinS hinD hdisj_same
                    hshape_d hread_s hread_d
                have hm_eq := annealMemCopy_live_inbounds_eq
                  (st := { m with stack := ⟨#[tf₃]⟩ })
                  srcId srcBorTag srcPtr.offsetBytes srcLA
                  dstId dstBorTag dstPtr.offsetBytes dstLA
                  hid_s hoff_s hbase_s hfind_s (hsz_la_s ▸ hinS)
                  hid_d hoff_d hbase_d hfind_d (hsz_la_d ▸ hinD) hpos hle
                rw [hcopy_ok] at hm_eq
                exact ⟨_, by rw [hm_mem]; exact hm_eq⟩
          obtain ⟨mach', hm_act⟩ := hm_copy
          exact ⟨_, copyStep_miri_ok hframes hfr.body_eq hfr.location_eq hfr₃.location_eq
            hbb hstmt hm_act⟩

/-! ## 8. Stage-1 `Trusted` Provenance-Preserving `CopyNonOverlapping` Evaluation (Anneal Side Only) -/

/-- Stage-1 `evalCopySingleDirect` (`Statements.lean:1464`) on a raw-pointer
pointee type (`pointeeKind = .rawPtr mut pk`) copies `.init (.ptr p 8)` from
`e_s.localIdx` into `e_d.localIdx` **preserving `ProvenancePtr` `p` intact**. -/
theorem evalCopySingleDirect_rawPtr_distinct_ok
    {s : MachineState} {src dst : MirAst.Operand}
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    {srcPtr dstPtr p : ProvenancePtr} {e_s e_d : AllocMapEntry}
    {mutability : Mutability} {pk : RigidTy} {idxS idxD : Nat} {slot_d : LocalSlot}
    {decl_d : LocalDecl}
    (hopS : operandPointeeTy localDecls layouts src =
      some { kind := .rawPtr mutability pk, layoutIdx := idxS })
    (hopD : operandPointeeTy localDecls layouts dst =
      some { kind := .rawPtr mutability pk, layoutIdx := idxD })
    (hne_tag : srcPtr.tag ≠ dstPtr.tag)
    (hne_loc : e_s.localIdx ≠ e_d.localIdx)
    (hslot_s : get? s.frame.locals e_s.localIdx = some (.init (.ptr p 8)))
    (hslot_d : get? s.frame.locals e_d.localIdx = some slot_d)
    (hne_dead_d : slot_d ≠ .dead)
    (hdecl_d : get? localDecls e_d.localIdx = some decl_d)
    (hty_d : decl_d.ty.kind = .rawPtr mutability pk) :
    evalCopySingleDirect s src dst localDecls layouts srcPtr dstPtr
        e_s.toBorrowEntry e_d.toBorrowEntry s.frame.locals =
      MirStepNode.step
        (advanceStmt s (s.frame.locals.set e_d.localIdx (.init (.ptr p 8)))
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
  have hset_d := set?_eq_some_set hlt_d (.init (.ptr p 8))
  have hval_ok :
      validateValueForTy? layouts
        (placeTy localDecls layouts { local_ := e_d.localIdx, projection := .nil })
        (.ptr p 8) = true := by
    unfold placeTy resolveProjectedTy
    rw [hdecl_d]
    rcases decl_d with ⟨_, ⟨kind_d, _⟩, _⟩
    dsimp only at hty_d ⊢
    subst hty_d
    rfl
  unfold evalCopySingleDirect
  dsimp only [AllocMapEntry.toBorrowEntry]
  rw [hb_tag]; dsimp only
  rw [hb_loc]; dsimp only
  rw [hslot_s]; dsimp only [readProjectedValue]
  rw [hopS, hopD]; dsimp only [sameRigidTyShape]
  rw [writePlaceValue_root_ok hval_ok hslot_d hne_dead_d]

/-- **`stepMirFn_copyNonOverlapping_rawPtr_preserves_provenance` (`LM-4.2`,
Stage-1, Anneal side only)**: one Stage-1 `stepMirFn` step
(`Trusted.Rustc.V2026_06_01.MirSemantics.stepMirFn`) of
`copy_nonoverlapping::<*mut T>(src, dst, 1)` when `src` and `dst` are raw pointers to
a raw-pointer pointee type `.rawPtr mutability pk` at root offset `0`, `src`
targets local `e_s.localIdx` holding `.init (.ptr p 8)`, and `dst` targets a
distinct live local `e_d.localIdx` (`decl_d.ty.kind = .rawPtr mutability pk`):
Stage-1 copies `.init (.ptr p 8)` into `e_d.localIdx` with its `ProvenancePtr` `p`
intact.

This is **not** a lockstep simulation: it says nothing about `lean-miri`. A
Stage-1 `StepRelLM3_1` simulation of pointer-valued copies additionally needs a
relation for memory-backed locals holding provenance-carrying pointers, which
`StateRelLM3_1` (scalar-only `StackScalarAllocShape`) does not provide. -/
theorem stepMirFn_copyNonOverlapping_rawPtr_preserves_provenance
    {body : CapturedMir} {s : MachineState}
    (hcal : s.memory.activeCallee = none)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {srcIdx dstIdx : Local} {countOp : MirAst.Operand} {span : String}
    {srcDecl dstDecl decl_d : LocalDecl} {srcMut dstMut mutability : Mutability} {pk : RigidTy}
    {srcPtr dstPtr p : ProvenancePtr}
    {countSc : MirAst.ScalarInt} {e_s e_d : AllocMapEntry} {slot_d : LocalSlot}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.intrinsic (.copyNonOverlapping (.copy ⟨srcIdx, []⟩) (.copy ⟨dstIdx, []⟩) countOp),
        span⟩)
    (hsrcDecl : get? body.localDecls srcIdx = some srcDecl)
    (hsrcTy : srcDecl.ty.kind = .rawPtr srcMut (.rawPtr mutability pk))
    (hdstDecl : get? body.localDecls dstIdx = some dstDecl)
    (hdstTy : dstDecl.ty.kind = .rawPtr dstMut (.rawPtr mutability pk))
    (hsrc_val : get? s.frame.locals srcIdx = some (.init (.ptr srcPtr 8)))
    (hdst_val : get? s.frame.locals dstIdx = some (.init (.ptr dstPtr 8)))
    (hoff0_s : srcPtr.offsetBytes = 0)
    (hoff0_d : dstPtr.offsetBytes = 0)
    (hcnt_pre : WriteBytesScalarPreVal s.frame.locals countOp countSc)
    (hcnt1 : countSc.bits = 1)
    (hlook_s : lookupBorrow s.memory.borrows srcPtr.tag = some e_s.toBorrowEntry)
    (hlook_d : lookupBorrow s.memory.borrows dstPtr.tag = some e_d.toBorrowEntry)
    (hperm_s : e_s.perm ≠ .disabled)
    (hperm_d : e_d.perm = .active ∨ e_d.perm = .reserved)
    (hne_tag : srcPtr.tag ≠ dstPtr.tag)
    (hne_loc : e_s.localIdx ≠ e_d.localIdx)
    (hslot_s : get? s.frame.locals e_s.localIdx = some (.init (.ptr p 8)))
    (hslot_d : get? s.frame.locals e_d.localIdx = some slot_d)
    (hne_dead_d : slot_d ≠ .dead)
    (hdecl_d : get? body.localDecls e_d.localIdx = some decl_d)
    (hty_d : decl_d.ty.kind = .rawPtr mutability pk)
    (hunion_s : unionLocalByteSize? body.localDecls body.layouts e_s.localIdx = none)
    (hunion_d : unionLocalByteSize? body.localDecls body.layouts e_d.localIdx = none) :
    stepMirFn body s =
      MirStepNode.step
        (advanceStmt s (s.frame.locals.set e_d.localIdx (.init (.ptr p 8)))
          { s.memory with
            borrows := invalidateConflictingBorrows s.memory.borrows e_d.localIdx
              (some dstPtr.tag) }) := by
  have hstep : stepMirFn body s =
      evalCopyNonOverlapping s (.copy ⟨srcIdx, []⟩) (.copy ⟨dstIdx, []⟩) countOp
        body.localDecls body.layouts := by
    rw [stepMirFn_eq_of_not_other body s hcal hphase]
    simp only [hbb, hstmt]; rfl
  have ha₁ : evalOperand s.frame.locals (.copy ⟨srcIdx, []⟩) s.memory.borrows s.memory.globals
      body.layouts s.memory.callerLocals body.localDecls = .ok (.ptr srcPtr 8) s.frame.locals := by
    unfold evalOperand; dsimp only; rw [hsrc_val]; rfl
  have ha₂ : evalOperand s.frame.locals (.copy ⟨dstIdx, []⟩) s.memory.borrows s.memory.globals
      body.layouts s.memory.callerLocals body.localDecls = .ok (.ptr dstPtr 8) s.frame.locals := by
    unfold evalOperand; dsimp only; rw [hdst_val]; rfl
  have ha₃ : evalOperand s.frame.locals countOp s.memory.borrows s.memory.globals
      body.layouts s.memory.callerLocals body.localDecls =
      .ok (.scalar countSc) s.frame.locals := by
    rcases hcnt_pre with ⟨cc, rfl, hv⟩ | ⟨idx, rfl, hsl⟩
    · unfold evalOperand; dsimp only; rw [hv]; rfl
    · unfold evalOperand; dsimp only; rw [hsl]; rfl
  have hperm_ok :
      evalCopyNonOverlappingPermOk s (.copy ⟨srcIdx, []⟩) (.copy ⟨dstIdx, []⟩)
        body.localDecls body.layouts srcPtr dstPtr e_s.toBorrowEntry e_d.toBorrowEntry 1
        s.frame.locals =
      MirStepNode.step
        (advanceStmt s (s.frame.locals.set e_d.localIdx (.init (.ptr p 8)))
          { s.memory with
            borrows := invalidateConflictingBorrows s.memory.borrows e_d.localIdx
              (some dstPtr.tag) }) := by
    unfold evalCopyNonOverlappingPermOk resolveUnionEndpoint?
    dsimp only [AllocMapEntry.toBorrowEntry]
    rw [hunion_s, hunion_d, hoff0_s, hoff0_d]
    exact evalCopySingleDirect_rawPtr_distinct_ok
      (operandPointeeTy_copy_rawPtr hsrcDecl hsrcTy)
      (operandPointeeTy_copy_rawPtr hdstDecl hdstTy)
      hne_tag hne_loc hslot_s hslot_d hne_dead_d hdecl_d hty_d
  rw [hstep]
  unfold evalCopyNonOverlapping
  rw [ha₁]; dsimp only; rw [ha₂]; dsimp only; rw [ha₃]; dsimp only
  unfold evalCopyNonOverlappingWithCount
  rw [hcnt1]; dsimp only
  rw [hlook_s, hlook_d]
  dsimp only [AllocMapEntry.toBorrowEntry]
  rcases hperm_d with hp_d | hp_d <;> rw [hp_d] <;>
    (cases hp_s : e_s.perm <;> first | exact hperm_ok | exact absurd hp_s hperm_s)

/-! ## 9. Stage-1 `Trusted` Lockstep Simulation and Divergence Transfer for `CopyNonOverlapping` -/

private theorem evalCopyNonOverlapping_stage1_unfold
    {body : CapturedMir} {s : MachineState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {srcIdx dstIdx : Local} {countOp : MirAst.Operand} {countTy : Ty}
    (hop : WellTypedScalarOperand body tf countOp countTy) :
    evalCopyNonOverlapping s (.copy ⟨srcIdx, []⟩) (.copy ⟨dstIdx, []⟩) countOp
        body.localDecls body.layouts =
      match
        evalOperand s.frame.locals (.copy ⟨srcIdx, []⟩) s.memory.borrows s.memory.globals
          body.layouts s.memory.callerLocals
      with
      | .ub => MirStepNode.fail .ub
      | .unsupported => MirStepNode.unsupported
      | .ok srcVal locals₁ =>
        match
          evalOperand locals₁ (.copy ⟨dstIdx, []⟩) s.memory.borrows s.memory.globals
            body.layouts s.memory.callerLocals
        with
        | .ub => MirStepNode.fail .ub
        | .unsupported => MirStepNode.unsupported
        | .ok dstVal locals₂ =>
          match
            evalOperand locals₂ countOp s.memory.borrows s.memory.globals
              body.layouts s.memory.callerLocals
          with
          | .ub => MirStepNode.fail .ub
          | .unsupported => MirStepNode.unsupported
          | .ok (.scalar countSc) locals₃ =>
            evalCopyNonOverlappingWithCount s (.copy ⟨srcIdx, []⟩) (.copy ⟨dstIdx, []⟩)
              body.localDecls body.layouts srcVal dstVal countSc.bits locals₃
          | .ok _ _ => MirStepNode.fail .ub := by
  cases hop <;> rfl

private theorem evalCopyNonOverlapping_stage1_eq_of_withCount_eq
    {body : CapturedMir} {s : MachineState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {srcIdx dstIdx : Local} {countOp : MirAst.Operand} {countTy : Ty}
    (hop : WellTypedScalarOperand body tf countOp countTy)
    (hwith : ∀ srcVal dstVal countSc,
      get? s.frame.locals srcIdx = some (.init srcVal) →
      get? s.frame.locals dstIdx = some (.init dstVal) →
      WriteBytesScalarPreVal s.frame.locals countOp countSc →
      evalCopyNonOverlappingWithCount s (.copy ⟨srcIdx, []⟩) (.copy ⟨dstIdx, []⟩)
        body.localDecls body.layouts srcVal dstVal countSc.bits s.frame.locals =
      evalCopyNonOverlappingWithCountLM4_2 s (.copy ⟨srcIdx, []⟩) (.copy ⟨dstIdx, []⟩)
        body.localDecls body.layouts srcVal dstVal countSc.bits s.frame.locals) :
    evalCopyNonOverlapping s (.copy ⟨srcIdx, []⟩) (.copy ⟨dstIdx, []⟩) countOp
        body.localDecls body.layouts =
      evalCopyNonOverlappingLM4_2 s (.copy ⟨srcIdx, []⟩) (.copy ⟨dstIdx, []⟩) countOp
        body.localDecls body.layouts := by
  rw [evalCopyNonOverlapping_stage1_unfold hop]
  unfold evalCopyNonOverlappingLM4_2
  rw [evalOperand_copy_local_eq (idx := srcIdx)]
  cases hsrc : get? s.frame.locals srcIdx with
  | none => rfl
  | some slotS =>
    cases slotS with
    | dead | uninit => rfl
    | init srcVal =>
      dsimp only
      rw [evalOperand_copy_local_eq (idx := dstIdx)]
      cases hdst : get? s.frame.locals dstIdx with
      | none => rfl
      | some slotD =>
        cases slotD with
        | dead | uninit => rfl
        | init dstVal =>
          dsimp only
          cases hop with
          | constScalar c countSc hval _ _ _ _ _ _ =>
            unfold evalOperand; dsimp only; rw [hval]; dsimp only
            exact hwith srcVal dstVal countSc hsrc hdst (Or.inl ⟨c, rfl, hval⟩)
          | copyLocal cIdx _ _ _ _ =>
            rw [evalOperand_copy_local_eq (idx := cIdx)]
            cases hc : get? s.frame.locals cIdx with
            | none => rfl
            | some slotC =>
              cases slotC with
              | dead | uninit => rfl
              | init vC =>
                cases vC with
                | scalar countSc =>
                  dsimp only
                  exact hwith srcVal dstVal countSc hsrc hdst (Or.inr ⟨cIdx, rfl, hc⟩)
                | _ => rfl

private theorem evalCopyNonOverlappingWithCount_stage1_single_eq
    {s : MachineState} {src dst : MirAst.Operand}
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    {srcPtr dstPtr : ProvenancePtr} {e_s e_d : AllocMapEntry}
    (hlookS : lookupBorrow s.memory.borrows srcPtr.tag = some e_s.toBorrowEntry)
    (hlookD : lookupBorrow s.memory.borrows dstPtr.tag = some e_d.toBorrowEntry)
    (hoffS : srcPtr.offsetBytes = 0)
    (hoffD : dstPtr.offsetBytes = 0)
    (hunionS : unionLocalByteSize? localDecls layouts e_s.localIdx = none)
    (hunionD : unionLocalByteSize? localDecls layouts e_d.localIdx = none) :
    evalCopyNonOverlappingWithCount s src dst localDecls layouts
        (.ptr srcPtr 8) (.ptr dstPtr 8) 1 s.frame.locals =
      match e_s.perm, e_d.perm with
      | .disabled, _ => MirStepNode.fail .ub
      | _, .frozen => MirStepNode.fail .ub
      | _, .disabled => MirStepNode.fail .ub
      | _, _ =>
        evalCopySingleDirect s src dst localDecls layouts srcPtr dstPtr
          e_s.toBorrowEntry e_d.toBorrowEntry s.frame.locals := by
  unfold evalCopyNonOverlappingWithCount
  dsimp only
  rw [hlookS, hlookD]
  dsimp only [AllocMapEntry.toBorrowEntry]
  have hperm_ok :
      evalCopyNonOverlappingPermOk s src dst localDecls layouts srcPtr dstPtr
        e_s.toBorrowEntry e_d.toBorrowEntry 1 s.frame.locals =
      evalCopySingleDirect s src dst localDecls layouts srcPtr dstPtr
        e_s.toBorrowEntry e_d.toBorrowEntry s.frame.locals := by
    unfold evalCopyNonOverlappingPermOk resolveUnionEndpoint?
    dsimp only [AllocMapEntry.toBorrowEntry]
    rw [hunionS, hunionD, hoffS, hoffD]
    rfl
  cases e_s.perm <;> cases e_d.perm <;> first | rfl | exact hperm_ok

private theorem sliceScalarBytes_zero_full {bits elemBytes : Nat}
    (hlt : bits < scalarModulus elemBytes) :
    sliceScalarBytes bits elemBytes 0 elemBytes = bits := by
  have hble : Nat.ble (scalarModulus elemBytes) bits = false :=
    copyBle_eq_false_of_gt (by omega)
  unfold sliceScalarBytes wrapScalarBits
  rw [hble]; dsimp only
  change (bits / 1) % scalarModulus elemBytes = bits
  rw [Nat.div_one, Nat.mod_eq_of_lt hlt]

private theorem intCastTargetBytes_eq_of_rigidTyKindByteSize
    {k : RigidTy} {b₁ b₂ : Nat}
    (h₁ : intCastTargetBytes k = some b₁)
    (h₂ : rigidTyKindByteSize k = some b₂) :
    b₁ = b₂ := by
  cases k <;> first | cases h₁ | exact Option.some.inj (h₁.symm.trans h₂)

private theorem evalCopySingleDirect_eq_evalCopyRootIntScalars
    {s : MachineState} {src dst : MirAst.Operand}
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    {srcPtr dstPtr : ProvenancePtr} {e_s e_d : AllocMapEntry}
    {pointeeTy : Ty} {idxS idxD elemBytes : Nat}
    {slot_s slot_d : LocalSlot} {decl_d : LocalDecl}
    (hcaller : s.memory.callerLocals = .nil)
    (hprim : IsPrimScalarTy pointeeTy)
    (hopS : operandPointeeTy localDecls layouts src =
      some { kind := pointeeTy.kind, layoutIdx := idxS })
    (hopD : operandPointeeTy localDecls layouts dst =
      some { kind := pointeeTy.kind, layoutIdx := idxD })
    (hoff0_s : srcPtr.offsetBytes = 0)
    (hoff0_d : dstPtr.offsetBytes = 0)
    (helem_pos : 0 < elemBytes)
    (htag_loc : srcPtr.tag = dstPtr.tag → e_s.localIdx = e_d.localIdx)
    (hslot_s : get? s.frame.locals e_s.localIdx = some slot_s)
    (hslot_d : get? s.frame.locals e_d.localIdx = some slot_d)
    (hdecl_d : get? localDecls e_d.localIdx = some decl_d)
    (hint_d : intCastTargetBytes decl_d.ty.kind = some elemBytes)
    (hsc_spec : ∀ v_s, slot_s = .init v_s →
      ∃ sc_s, v_s = .scalar sc_s ∧
        sc_s.sizeBytes = elemBytes ∧
        sc_s.bits < scalarModulus elemBytes) :
    evalCopySingleDirect s src dst localDecls layouts srcPtr dstPtr
        e_s.toBorrowEntry e_d.toBorrowEntry s.frame.locals =
      evalCopyRootIntScalars s s.frame.locals srcPtr dstPtr
        e_s.toBorrowEntry e_d.toBorrowEntry elemBytes elemBytes elemBytes := by
  cases hs : slot_s with
  | dead =>
    rw [evalCopySingleDirect_dead_src_ub hcaller (hslot_s.trans (congrArg some hs)),
      evalCopyRootIntScalars_dead_src_ub (hslot_s.trans (congrArg some hs))]
  | uninit =>
    rw [evalCopySingleDirect_uninit_src_ub (hslot_s.trans (congrArg some hs)),
      evalCopyRootIntScalars_uninit_src_ub (hslot_s.trans (congrArg some hs))]
  | init v_s =>
    obtain ⟨sc_s, rfl, hsc_sz, hsc_lt⟩ := hsc_spec v_s hs
    have hslot_s' : get? s.frame.locals e_s.localIdx = some (.init (.scalar sc_s)) :=
      hslot_s.trans (congrArg some hs)
    by_cases hd_d : slot_d = .dead
    · subst hd_d
      rw [evalCopySingleDirect_dead_dst_ub hcaller hprim hopS hopD hslot_s' hslot_d,
        evalCopyRootIntScalars_dead_dst_ub hslot_s' hslot_d]
    · have hls : lookupCopyRootSlot s s.frame.locals e_s.localIdx =
          some (.init (.scalar sc_s)) := by
        unfold lookupCopyRootSlot; rw [hslot_s']
      have hld : lookupCopyRootSlot s s.frame.locals e_d.localIdx = some slot_d := by
        unfold lookupCopyRootSlot; rw [hslot_d]
      by_cases hsame : e_s.localIdx = e_d.localIdx
      · rw [evalCopySingleDirect_overlap_ub hsame]
        unfold evalCopyRootIntScalars
        dsimp only [AllocMapEntry.toBorrowEntry]
        rw [hls, hld]
        have hble0 : Nat.ble elemBytes 0 = false := copyBle_eq_false_of_gt (by omega)
        cases hd_case : slot_d with
        | dead => exact absurd hd_case hd_d
        | uninit | init _ =>
          dsimp only
          rw [hsc_sz, Nat.beq_refl]
          dsimp only
          simp [hoff0_s, hoff0_d, hsame, hble0]
      · have hne_tag : srcPtr.tag ≠ dstPtr.tag := fun ht => hsame (htag_loc ht)
        have hb_loc : Nat.beq e_s.localIdx e_d.localIdx = false := by
          cases h : Nat.beq e_s.localIdx e_d.localIdx
          · rfl
          · exact absurd (Nat.eq_of_beq_eq_true h) hsame
        have hbool_d : decl_d.ty.kind = .bool →
            sc_s.sizeBytes = 1 ∧ (sc_s.bits = 0 ∨ sc_s.bits = 1) :=
          fun h => by rw [h] at hint_d; cases hint_d
        have hchar_d : decl_d.ty.kind = .char →
            sc_s.sizeBytes = 4 ∧ isValidCharCode sc_s.bits = true :=
          fun h => by rw [h] at hint_d; cases hint_d
        rw [evalCopySingleDirect_distinct_ok hprim hopS hopD hne_tag hsame
          hslot_s' hslot_d hd_d hdecl_d hbool_d hchar_d]
        unfold evalCopyRootIntScalars
        dsimp only [AllocMapEntry.toBorrowEntry]
        rw [hls, hld]
        cases hd_case : slot_d with
        | dead => exact absurd hd_case hd_d
        | uninit | init _ =>
          dsimp only
          rw [hsc_sz, Nat.beq_refl]
          dsimp only
          simp only [hoff0_s, hoff0_d, hb_loc, Bool.false_and, Nat.beq_refl, Bool.and_self]
          rw [sliceScalarBytes_zero_full hsc_lt,
            show ({ bits := sc_s.bits, sizeBytes := elemBytes } : MirAst.ScalarInt) = sc_s by
              cases sc_s; subst hsc_sz; rfl,
            writeCopyRootSlot_local_ok (hslot_d.trans (congrArg some hd_case)) (by nofun)]

/-- **`stepMirFn_copyNonOverlapping_stage1_eq_lm4_2` (`LM-4.2`, Stage-1 bridge)**:
from any `StateRelLM3_1`-related state at
`StatementKind.intrinsic (.copyNonOverlapping (.copy ⟨srcIdx, []⟩) (.copy ⟨dstIdx, []⟩) countOp)`,
Stage-1 `stepMirFn body s` equals `stepMirFnLM4_2 body s` whenever:
1. on a zero-element copy (`countSc.bits = 0`), `srcVal` and `dstVal` are aligned
   to `elemAlign` (`hzero_align`);
2. on a positive-element copy (`0 < countSc.bits`) between provenance-carrying
   pointers `.ptr srcPtr 8` and `.ptr dstPtr 8`, `countSc.bits = 1`, both byte
   offsets are `0`, both target locals have the pointee type `pointeeTy.kind`, and
   neither target local is a union (`hptr_single`).

Covers all outcomes on this fragment: dead/uninitialized operand UB, aligned
`count = 0` no-op steps, positive-count provenance-free `.scalar` pointer UB,
dead target stack locals, uninitialized source locals, Tree Borrows permission
failures, same-local overlap UB, and valid distinct-local single-element copies. -/
theorem stepMirFn_copyNonOverlapping_stage1_eq_lm4_2
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
    (_hcountInt : IsIntegralTy countTy .usize)
    (hcountOp : ∀ tf, m.stack.frames = #[tf] → WellTypedScalarOperand body tf countOp countTy)
    (hpt : CopyPointee body.layouts pointeeTy.kind ptId elemBytes elemAlign)
    (helem_pos : 0 < elemBytes)
    (hzero_align : ∀ srcVal dstVal countSc,
      get? s.frame.locals srcIdx = some (.init srcVal) →
      get? s.frame.locals dstIdx = some (.init dstVal) →
      WriteBytesScalarPreVal s.frame.locals countOp countSc →
      countSc.bits = 0 →
      ptrValueAligned elemAlign srcVal = true ∧
        ptrValueAligned elemAlign dstVal = true)
    (hptr_single : ∀ srcPtr dstPtr countSc e_s e_d decl_s decl_d,
      get? s.frame.locals srcIdx = some (.init (.ptr srcPtr 8)) →
      get? s.frame.locals dstIdx = some (.init (.ptr dstPtr 8)) →
      WriteBytesScalarPreVal s.frame.locals countOp countSc →
      0 < countSc.bits →
      e_s ∈ allocMap → e_s.tag = srcPtr.tag →
      e_d ∈ allocMap → e_d.tag = dstPtr.tag →
      get? body.localDecls e_s.localIdx = some decl_s →
      get? body.localDecls e_d.localIdx = some decl_d →
      countSc.bits = 1 ∧
        srcPtr.offsetBytes = 0 ∧
        dstPtr.offsetBytes = 0 ∧
        decl_s.ty.kind = pointeeTy.kind ∧
        decl_d.ty.kind = pointeeTy.kind ∧
        unionLocalByteSize? body.localDecls body.layouts e_s.localIdx = none ∧
        unionLocalByteSize? body.localDecls body.layouts e_d.localIdx = none) :
    stepMirFn body s = stepMirFnLM4_2 body s := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, hcaller, _, halloc, _⟩ := id hstate
  rw [stepMirFn_eq_of_not_other body s hcal hphase,
    stepMirFnLM4_2_eq_of_not_other body s hcal hphase]
  simp only [hbb, hstmt]
  dsimp only [evalStmt, evalStmtLM4_2]
  apply evalCopyNonOverlapping_stage1_eq_of_withCount_eq (hcountOp tf hframes)
  intro srcVal dstVal countSc hsrc hdst hcnt
  obtain ⟨hopS_idx, hopS⟩ :=
    operandPointeeTy_copy_rawPtr_exists (layouts := body.layouts) hsrcDecl hsrcTy
  obtain ⟨hopD_idx, hopD⟩ :=
    operandPointeeTy_copy_rawPtr_exists (layouts := body.layouts) hdstDecl hdstTy
  by_cases hc0 : countSc.bits = 0
  · obtain ⟨halS, halD⟩ := hzero_align srcVal dstVal countSc hsrc hdst hcnt hc0
    rw [hc0]
    unfold evalCopyNonOverlappingWithCount evalCopyNonOverlappingWithCountLM4_2
    rw [copyPrecheck_eq _ _ 0 hopS hpt.wb.anneal_size hpt.anneal_align]
    simp [halS, halD]
  · have hc_pos : 0 < countSc.bits := Nat.pos_of_ne_zero hc0
    have hb_c0 : Nat.beq countSc.bits 0 = false := by
      cases hb : Nat.beq countSc.bits 0
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true hb) hc0
    have hpos : 0 < countSc.bits * elemBytes := Nat.mul_pos hc_pos helem_pos
    have hnz : ¬ (countSc.bits * elemBytes = 0) := by omega
    rcases annealEvalOperand_rawPtr_lm3_1 hstate hframes hsrcDecl hsrcTy (hsrcImm tf hframes) with
      ⟨hd, _⟩ | ⟨_, hun, _⟩ |
      ⟨sc_s, _, _, hsrc_sc, _⟩ |
      ⟨srcPtr, mptr_s, _, hsrc_ptr, hptrRel_s, _⟩
    · rw [hsrc] at hd; cases hd
    · rw [hsrc] at hun; cases hun
    · rw [hsrc] at hsrc_sc; injection hsrc_sc with h; injection h with h; subst h
      unfold evalCopyNonOverlappingWithCount evalCopyNonOverlappingWithCountLM4_2
      rw [hb_c0, copyPrecheck_eq _ _ countSc.bits hopS hpt.wb.anneal_size hpt.anneal_align]
      by_cases hle : countSc.bits * elemBytes ≤ isizeMaxBytes <;>
        by_cases hal :
          (ptrValueAligned elemAlign (.scalar sc_s) && ptrValueAligned elemAlign dstVal) = true <;>
        simp [hle, hal, hnz]
    · rw [hsrc] at hsrc_ptr; injection hsrc_ptr with h; injection h with h; subst h
      rcases annealEvalOperand_rawPtr_lm3_1 hstate hframes hdstDecl hdstTy (hdstImm tf hframes) with
        ⟨hd, _⟩ | ⟨_, hun, _⟩ |
        ⟨sc_d, _, _, hdst_sc, _⟩ |
        ⟨dstPtr, mptr_d, _, hdst_ptr, hptrRel_d, _⟩
      · rw [hdst] at hd; cases hd
      · rw [hdst] at hun; cases hun
      · rw [hdst] at hdst_sc; injection hdst_sc with h; injection h with h; subst h
        unfold evalCopyNonOverlappingWithCount evalCopyNonOverlappingWithCountLM4_2
        rw [hb_c0, copyPrecheck_eq _ _ countSc.bits hopS hpt.wb.anneal_size hpt.anneal_align]
        by_cases hle : countSc.bits * elemBytes ≤ isizeMaxBytes <;>
          by_cases hal :
            (ptrValueAligned elemAlign (.ptr srcPtr 8) &&
              ptrValueAligned elemAlign (.scalar sc_d)) = true <;>
          simp [hle, hal, hnz]
      · rw [hdst] at hdst_ptr; injection hdst_ptr with h; injection h with h; subst h
        rcases hptrRel_s with ⟨_, _, _, _, _, _, e_s, he_s, het_s, _⟩
        rcases hptrRel_d with ⟨_, _, _, _, _, _, e_d, he_d, het_d, _⟩
        obtain ⟨decl_s, hdecl_s, hprim_s⟩ := halloc.target_decl e_s he_s
        obtain ⟨decl_d, hdecl_d, hprim_d⟩ := halloc.target_decl e_d he_d
        obtain ⟨hcnt1, hoff0_s, hoff0_d, hk_s, hk_d, hunion_s, hunion_d⟩ :=
          hptr_single srcPtr dstPtr countSc e_s e_d decl_s decl_d
            hsrc hdst hcnt hc_pos he_s het_s he_d het_d hdecl_s hdecl_d
        have hprim_pt := isPrimScalarTy_of_kind_eq hprim_s hk_s
        obtain ⟨hrig_s, htr_s, hvalid_sz⟩ :=
          primScalar_size_of_writeBytesPointee hprim_s (hk_s.symm ▸ hpt.wb)
        obtain ⟨hrig_d, _, _⟩ :=
          primScalar_size_of_writeBytesPointee hprim_d (hk_d.symm ▸ hpt.wb)
        have hle1 : elemBytes ≤ isizeMaxBytes := by
          unfold isizeMaxBytes; rcases hvalid_sz with rfl | rfl | rfl | rfl | rfl <;> omega
        have halS := ptrValueAligned_of_offset_zero hpt.align_pair.validCopyAlign hoff0_s
        have halD := ptrValueAligned_of_offset_zero hpt.align_pair.validCopyAlign hoff0_d
        have hlook_s : lookupBorrow s.memory.borrows srcPtr.tag = some e_s.toBorrowEntry := by
          rw [← het_s]; exact (halloc.borrow_sync e_s he_s).2
        have hlook_d : lookupBorrow s.memory.borrows dstPtr.tag = some e_d.toBorrowEntry := by
          rw [← het_d]; exact (halloc.borrow_sync e_d he_d).2
        rw [hcnt1,
          evalCopyNonOverlappingWithCount_stage1_single_eq
            hlook_s hlook_d hoff0_s hoff0_d hunion_s hunion_d,
          evalCopyNonOverlappingWithCount_of_perm_or_single hopS
            hpt.wb.anneal_size hpt.anneal_align hle1 helem_pos halS halD
            hlook_s hdecl_s hrig_s hoff0_s hlook_d hdecl_d hrig_d hoff0_d]
        have htag_loc : srcPtr.tag = dstPtr.tag → e_s.localIdx = e_d.localIdx := by
          intro htag
          have hl1 := copyLookupAllocMapByTag_of_mem_nodup halloc.tags_nodup he_s het_s
          have hl2 := copyLookupAllocMapByTag_of_mem_nodup halloc.tags_nodup he_d
            (het_d.trans htag.symm)
          rw [hl1] at hl2; injection hl2 with heq; exact congrArg _ heq
        obtain ⟨slot_s, mls_s, _, _, hslot_s, hmls_s, _, hloc_s⟩ := hfr.lookup_local hdecl_s
        obtain ⟨slot_d, _, _, _, hslot_d, _, _, _⟩ := hfr.lookup_local hdecl_d
        have hsc_spec : ∀ v_s, slot_s = .init v_s →
            ∃ sc_s, v_s = .scalar sc_s ∧
              sc_s.sizeBytes = elemBytes ∧
              sc_s.bits < scalarModulus elemBytes := by
          intro v_s hs_init
          have hd_s : slot_s ≠ .dead := by rw [hs_init]; nofun
          obtain ⟨⟨lay_s, hlay_s⟩, hsc_only_s, hshape_fn_s⟩ :=
            (halloc.local_alloc_sync tf hframes e_s he_s).1 slot_s hslot_s hd_s
          obtain ⟨srcLA, hfind_s', _, _, _⟩ := hshape_fn_s decl_s hdecl_s
          obtain ⟨sc_s, rfl⟩ := hsc_only_s v_s hs_init
          have hmls_s_eq : mls_s = ⟨.live (.indirect (stackAllocPlace e_s.allocId)), lay_s⟩ := by
            rw [hlay_s] at hmls_s; exact Option.some.inj hmls_s.symm
          have hts_nat : (translateSizeBytes elemBytes).bytes.toNat = elemBytes := by
            rcases hvalid_sz with rfl | rfl | rfl | rfl | rfl <;> rfl
          have hnz_sz_s : (translateTy decl_s.ty body.layouts).layout.size ≠
              Miri.ABI.Size.ZERO := by
            rw [htr_s]; intro h
            have := congrArg (fun z : Miri.ABI.Size => z.bytes.toNat) h
            rw [hts_nat] at this; change elemBytes = 0 at this; omega
          obtain ⟨_, hsc_sp⟩ := hloc_s.indirect_stackAllocPlace_spec hmls_s_eq
            (halloc.base_addr_valid e_s he_s).2.2 hfind_s'
            (halloc.live_key_unique e_s he_s) hnz_sz_s
          obtain ⟨hsz_sc_eq, _, _, msc_s, hrel_sc, _⟩ := hsc_sp sc_s hs_init
          have hsc_bytes : sc_s.sizeBytes = elemBytes := by
            have h := htr_s.symm.trans hsz_sc_eq
            have h1 : (translateSizeBytes sc_s.sizeBytes).bytes.toNat = sc_s.sizeBytes := by
              rcases hrel_sc.validBytes with h0 | h0 | h0 | h0 | h0 <;> (rw [h0]; rfl)
            have := congrArg (fun z : Miri.ABI.Size => z.bytes.toNat) h
            omega
          exact ⟨sc_s, rfl, hsc_bytes, hsc_bytes ▸ hrel_sc.canonical⟩
        cases hs_int : intCastTargetBytes decl_s.ty.kind with
        | none =>
          cases e_s.perm <;> cases e_d.perm <;> rfl
        | some srcBytes =>
          have hd_int : intCastTargetBytes decl_d.ty.kind = some srcBytes := by
            rw [hk_d, ← hk_s, hs_int]
          have hsb_eq : srcBytes = elemBytes :=
            intCastTargetBytes_eq_of_rigidTyKindByteSize (hk_s ▸ hs_int) hpt.wb.anneal_size
          subst hsb_eq
          rw [hd_int]
          have hbody_eq := evalCopySingleDirect_eq_evalCopyRootIntScalars
            hcaller hprim_pt hopS hopD hoff0_s hoff0_d helem_pos htag_loc
            hslot_s hslot_d hdecl_d hd_int hsc_spec
          cases e_s.perm <;> cases e_d.perm <;> first | rfl | exact hbody_eq

/-- **`step_intrinsic_copyNonOverlapping_stage1_simulation_explicit` (`LM-4.2`,
Stage-1 `Trusted`)**: one real Stage-1 `stepMirFn` step of
`StatementKind.intrinsic (.copyNonOverlapping (.copy ⟨srcIdx, []⟩) (.copy ⟨dstIdx, []⟩) countOp)`
in lockstep (`StepRelLM3_1`) with `lean-miri`'s `Miri.Interpreter.Step.step` under
`copyNextAllocMap`, transferred from `step_intrinsic_copyNonOverlapping_simulation_explicit`
via `stepMirFn_copyNonOverlapping_stage1_eq_lm4_2`. -/
theorem step_intrinsic_copyNonOverlapping_stage1_simulation_explicit
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
    (helem_pos : 0 < elemBytes)
    (hzero_align : ∀ srcVal dstVal countSc,
      get? s.frame.locals srcIdx = some (.init srcVal) →
      get? s.frame.locals dstIdx = some (.init dstVal) →
      WriteBytesScalarPreVal s.frame.locals countOp countSc →
      countSc.bits = 0 →
      ptrValueAligned elemAlign srcVal = true ∧
        ptrValueAligned elemAlign dstVal = true)
    (htgt_same : ∀ srcPtr dstPtr e_s e_d decl_s decl_d,
      get? s.frame.locals srcIdx = some (.init (.ptr srcPtr 8)) →
      get? s.frame.locals dstIdx = some (.init (.ptr dstPtr 8)) →
      e_s ∈ allocMap → e_s.tag = srcPtr.tag →
      e_d ∈ allocMap → e_d.tag = dstPtr.tag →
      get? body.localDecls e_s.localIdx = some decl_s →
      get? body.localDecls e_d.localIdx = some decl_d →
      decl_s.ty.kind = pointeeTy.kind ∧
        decl_d.ty.kind = pointeeTy.kind ∧
        unionLocalByteSize? body.localDecls body.layouts e_s.localIdx = none ∧
        unionLocalByteSize? body.localDecls body.layouts e_d.localIdx = none)
    (hptr_single : ∀ srcPtr dstPtr countSc,
      get? s.frame.locals srcIdx = some (.init (.ptr srcPtr 8)) →
      get? s.frame.locals dstIdx = some (.init (.ptr dstPtr 8)) →
      WriteBytesScalarPreVal s.frame.locals countOp countSc →
      0 < countSc.bits →
      countSc.bits = 1 ∧
        srcPtr.offsetBytes = 0 ∧
        dstPtr.offsetBytes = 0)
    (hlive_ok : ∀ srcPtr dstPtr countSc e_s e_d,
      get? s.frame.locals srcIdx = some (.init (.ptr srcPtr 8)) →
      get? s.frame.locals dstIdx = some (.init (.ptr dstPtr 8)) →
      WriteBytesScalarPreVal s.frame.locals countOp countSc →
      0 < countSc.bits →
      e_s ∈ allocMap → e_s.tag = srcPtr.tag →
      e_d ∈ allocMap → e_d.tag = dstPtr.tag →
      get? s.frame.locals e_s.localIdx ≠ some .dead →
      get? s.frame.locals e_d.localIdx ≠ some .dead →
      e_s.perm ≠ .disabled ∧
        (e_d.perm = .active ∨ e_d.perm = .reserved) ∧
        get? s.frame.locals e_s.localIdx ≠ some .uninit) :
    StepRelLM3_1 body m
      (copyNextAllocMap s.frame.locals allocMap dstIdx countOp elemBytes)
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  rw [stepMirFn_copyNonOverlapping_stage1_eq_lm4_2 hstate hphase hbb hstmt
    hsrcDecl hsrcTy hsrcImm hdstDecl hdstTy hdstImm hcountInt hcountOp hpt
    helem_pos hzero_align (fun srcPtr dstPtr countSc e_s e_d decl_s decl_d
      hsrc hdst hcnt hc_pos he_s het_s he_d het_d hdecl_s hdecl_d => by
      obtain ⟨hcnt1, hoff0_s, hoff0_d⟩ := hptr_single srcPtr dstPtr countSc hsrc hdst hcnt hc_pos
      obtain ⟨hk_s, hk_d, hun_s, hun_d⟩ :=
        htgt_same srcPtr dstPtr e_s e_d decl_s decl_d hsrc hdst he_s het_s he_d het_d
          hdecl_s hdecl_d
      exact ⟨hcnt1, hoff0_s, hoff0_d, hk_s, hk_d, hun_s, hun_d⟩)]
  refine step_intrinsic_copyNonOverlapping_simulation_explicit hstate hphase hbb hstmt
    hsrcDecl hsrcTy hsrcImm hdstDecl hdstTy hdstImm hcountInt hcountOp hpt ?_ ?_
  · intro srcPtr dstPtr e_s e_d decl_s decl_d hsrc hdst he_s het_s he_d het_d hdecl_s hdecl_d _
    obtain ⟨hk_s, hk_d, _, _⟩ :=
      htgt_same srcPtr dstPtr e_s e_d decl_s decl_d hsrc hdst he_s het_s he_d het_d
        hdecl_s hdecl_d
    exact Or.inr ⟨hk_s, hk_d⟩
  · intro srcPtr dstPtr countSc e_s e_d decl_s decl_d srcBytes dstBytes
      hsrc hdst hcnt hpos _ he_s het_s he_d het_d hdecl_s hdecl_d _ hrig_d _ _ hlive_s hlive_d
    have hc_pos : 0 < countSc.bits := by
      cases h : countSc.bits with
      | zero => rw [h, Nat.zero_mul] at hpos; exact absurd hpos (Nat.lt_irrefl 0)
      | succ k => omega
    obtain ⟨hcnt1, _, hoff0_d⟩ := hptr_single srcPtr dstPtr countSc hsrc hdst hcnt hc_pos
    obtain ⟨_, hk_d, _, _⟩ :=
      htgt_same srcPtr dstPtr e_s e_d decl_s decl_d hsrc hdst he_s het_s he_d het_d
        hdecl_s hdecl_d
    obtain ⟨hp_s, hp_d, hnu_s⟩ :=
      hlive_ok srcPtr dstPtr countSc e_s e_d hsrc hdst hcnt hc_pos he_s het_s he_d het_d
        hlive_s hlive_d
    have hdst_sz : dstBytes = elemBytes := by
      unfold rigidTyByteSize at hrig_d
      rw [hk_d, hpt.wb.anneal_size] at hrig_d
      exact Option.some.inj hrig_d.symm
    exact ⟨hp_s, hp_d, hnu_s, Or.inl ⟨hoff0_d, by rw [hcnt1, Nat.one_mul, hdst_sz]⟩⟩

/-- **`step_intrinsic_copyNonOverlapping_stage1_simulation` (`LM-4.2`,
Stage-1 `Trusted`)**: existential `allocMap'` packaging of
`step_intrinsic_copyNonOverlapping_stage1_simulation_explicit`. -/
theorem step_intrinsic_copyNonOverlapping_stage1_simulation
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
    (helem_pos : 0 < elemBytes)
    (hzero_align : ∀ srcVal dstVal countSc,
      get? s.frame.locals srcIdx = some (.init srcVal) →
      get? s.frame.locals dstIdx = some (.init dstVal) →
      WriteBytesScalarPreVal s.frame.locals countOp countSc →
      countSc.bits = 0 →
      ptrValueAligned elemAlign srcVal = true ∧
        ptrValueAligned elemAlign dstVal = true)
    (htgt_same : ∀ srcPtr dstPtr e_s e_d decl_s decl_d,
      get? s.frame.locals srcIdx = some (.init (.ptr srcPtr 8)) →
      get? s.frame.locals dstIdx = some (.init (.ptr dstPtr 8)) →
      e_s ∈ allocMap → e_s.tag = srcPtr.tag →
      e_d ∈ allocMap → e_d.tag = dstPtr.tag →
      get? body.localDecls e_s.localIdx = some decl_s →
      get? body.localDecls e_d.localIdx = some decl_d →
      decl_s.ty.kind = pointeeTy.kind ∧
        decl_d.ty.kind = pointeeTy.kind ∧
        unionLocalByteSize? body.localDecls body.layouts e_s.localIdx = none ∧
        unionLocalByteSize? body.localDecls body.layouts e_d.localIdx = none)
    (hptr_single : ∀ srcPtr dstPtr countSc,
      get? s.frame.locals srcIdx = some (.init (.ptr srcPtr 8)) →
      get? s.frame.locals dstIdx = some (.init (.ptr dstPtr 8)) →
      WriteBytesScalarPreVal s.frame.locals countOp countSc →
      0 < countSc.bits →
      countSc.bits = 1 ∧
        srcPtr.offsetBytes = 0 ∧
        dstPtr.offsetBytes = 0)
    (hlive_ok : ∀ srcPtr dstPtr countSc e_s e_d,
      get? s.frame.locals srcIdx = some (.init (.ptr srcPtr 8)) →
      get? s.frame.locals dstIdx = some (.init (.ptr dstPtr 8)) →
      WriteBytesScalarPreVal s.frame.locals countOp countSc →
      0 < countSc.bits →
      e_s ∈ allocMap → e_s.tag = srcPtr.tag →
      e_d ∈ allocMap → e_d.tag = dstPtr.tag →
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
    step_intrinsic_copyNonOverlapping_stage1_simulation_explicit hstate hphase hbb hstmt
      hsrcDecl hsrcTy hsrcImm hdstDecl hdstTy hdstImm hcountInt hcountOp hpt
      helem_pos hzero_align htgt_same hptr_single hlive_ok⟩

/-- **`step_intrinsic_copyNonOverlapping_stage1_simulation_same_allocMap` (`LM-4.2`,
Stage-1 `Trusted`)**: specialization of
`step_intrinsic_copyNonOverlapping_stage1_simulation_explicit` preserving `allocMap`
when `dst` uses an `.active` borrow with any foreign borrows on `e_d.localIdx`
already `.disabled` (or on zero-count / UB steps). -/
theorem step_intrinsic_copyNonOverlapping_stage1_simulation_same_allocMap
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
    (helem_pos : 0 < elemBytes)
    (hzero_align : ∀ srcVal dstVal countSc,
      get? s.frame.locals srcIdx = some (.init srcVal) →
      get? s.frame.locals dstIdx = some (.init dstVal) →
      WriteBytesScalarPreVal s.frame.locals countOp countSc →
      countSc.bits = 0 →
      ptrValueAligned elemAlign srcVal = true ∧
        ptrValueAligned elemAlign dstVal = true)
    (htgt_same : ∀ srcPtr dstPtr e_s e_d decl_s decl_d,
      get? s.frame.locals srcIdx = some (.init (.ptr srcPtr 8)) →
      get? s.frame.locals dstIdx = some (.init (.ptr dstPtr 8)) →
      e_s ∈ allocMap → e_s.tag = srcPtr.tag →
      e_d ∈ allocMap → e_d.tag = dstPtr.tag →
      get? body.localDecls e_s.localIdx = some decl_s →
      get? body.localDecls e_d.localIdx = some decl_d →
      decl_s.ty.kind = pointeeTy.kind ∧
        decl_d.ty.kind = pointeeTy.kind ∧
        unionLocalByteSize? body.localDecls body.layouts e_s.localIdx = none ∧
        unionLocalByteSize? body.localDecls body.layouts e_d.localIdx = none)
    (hptr_single : ∀ srcPtr dstPtr countSc,
      get? s.frame.locals srcIdx = some (.init (.ptr srcPtr 8)) →
      get? s.frame.locals dstIdx = some (.init (.ptr dstPtr 8)) →
      WriteBytesScalarPreVal s.frame.locals countOp countSc →
      0 < countSc.bits →
      countSc.bits = 1 ∧
        srcPtr.offsetBytes = 0 ∧
        dstPtr.offsetBytes = 0)
    (hlive_ok : ∀ srcPtr dstPtr countSc e_s e_d,
      get? s.frame.locals srcIdx = some (.init (.ptr srcPtr 8)) →
      get? s.frame.locals dstIdx = some (.init (.ptr dstPtr 8)) →
      WriteBytesScalarPreVal s.frame.locals countOp countSc →
      0 < countSc.bits →
      e_s ∈ allocMap → e_s.tag = srcPtr.tag →
      e_d ∈ allocMap → e_d.tag = dstPtr.tag →
      get? s.frame.locals e_s.localIdx ≠ some .dead →
      get? s.frame.locals e_d.localIdx ≠ some .dead →
      e_s.perm ≠ .disabled ∧
        (e_d.perm = .active ∨ e_d.perm = .reserved) ∧
        get? s.frame.locals e_s.localIdx ≠ some .uninit)
    (hact : ∀ dstPtr countSc e_d,
      get? s.frame.locals dstIdx = some (.init (.ptr dstPtr 8)) →
      WriteBytesScalarPreVal s.frame.locals countOp countSc →
      0 < countSc.bits * elemBytes →
      e_d ∈ allocMap → e_d.tag = dstPtr.tag →
      ∀ x ∈ allocMap, x.localIdx = e_d.localIdx →
        (x.tag = dstPtr.tag ∧ x.perm = .active) ∨ (x.tag ≠ dstPtr.tag ∧ x.perm = .disabled)) :
    StepRelLM3_1 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  rw [← copyNextAllocMap_eq_self hact]
  exact step_intrinsic_copyNonOverlapping_stage1_simulation_explicit hstate hphase hbb hstmt
    hsrcDecl hsrcTy hsrcImm hdstDecl hdstTy hdstImm hcountInt hcountOp hpt
    helem_pos hzero_align htgt_same hptr_single hlive_ok

/-- **Stage-1 uninitialized-source divergence (`LM-4.2`, Stage-1 `Trusted`)**:
copying `count = 1` element from an uninitialized (`.uninit`) live non-union
primitive-scalar stack local into a live non-union primitive-scalar destination
local:
* Stage-1 `stepMirFn` (`evalCopySingleDirect`) rejects reading `.uninit` for a
  non-union local (`stepMirFn body s = MirStepNode.fail .ub`);
* `lean-miri`'s untyped `Allocation.copyRepeatedly` copies uninitialized bytes
  (`initialized.noBytesInit`) and returns `.ok true`. -/
theorem step_intrinsic_copyNonOverlapping_stage1_uninit_src_divergence
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
    (hunion_s : unionLocalByteSize? body.localDecls body.layouts e_s.localIdx = none)
    (hunion_d : unionLocalByteSize? body.localDecls body.layouts e_d.localIdx = none)
    (huninit_s : get? s.frame.locals e_s.localIdx = some .uninit)
    (hdst_live : get? s.frame.locals e_d.localIdx ≠ some .dead) :
    stepMirFn body s = MirStepNode.fail .ub ∧
    ∃ m',
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .ok true) := by
  obtain ⟨_, _, _, _, _, hcal, _, _, _, _, halloc, _⟩ := id hstate
  have hstep : stepMirFn body s =
      evalCopyNonOverlapping s (.copy ⟨srcIdx, []⟩) (.copy ⟨dstIdx, []⟩) countOp
        body.localDecls body.layouts := by
    rw [stepMirFn_eq_of_not_other body s hcal hphase]
    simp only [hbb, hstmt]; rfl
  have ha₁ : evalOperand s.frame.locals (.copy ⟨srcIdx, []⟩) s.memory.borrows s.memory.globals
      body.layouts s.memory.callerLocals body.localDecls = .ok (.ptr srcPtr 8) s.frame.locals := by
    unfold evalOperand; dsimp only; rw [hsrc_val]; rfl
  have ha₂ : evalOperand s.frame.locals (.copy ⟨dstIdx, []⟩) s.memory.borrows s.memory.globals
      body.layouts s.memory.callerLocals body.localDecls = .ok (.ptr dstPtr 8) s.frame.locals := by
    unfold evalOperand; dsimp only; rw [hdst_val]; rfl
  have ha₃ : evalOperand s.frame.locals countOp s.memory.borrows s.memory.globals
      body.layouts s.memory.callerLocals body.localDecls =
      .ok (.scalar countSc) s.frame.locals := by
    rcases hcnt_pre with ⟨cc, rfl, hv⟩ | ⟨idx, rfl, hsl⟩
    · unfold evalOperand; dsimp only; rw [hv]; rfl
    · unfold evalOperand; dsimp only; rw [hsl]; rfl
  have hlook_s : lookupBorrow s.memory.borrows srcPtr.tag = some e_s.toBorrowEntry := by
    rw [← het_s]; exact (halloc.borrow_sync e_s he_s).2
  have hlook_d : lookupBorrow s.memory.borrows dstPtr.tag = some e_d.toBorrowEntry := by
    rw [← het_d]; exact (halloc.borrow_sync e_d he_d).2
  refine ⟨?_, (step_intrinsic_copyNonOverlapping_uninit_src_divergence hstate hphase hbb hstmt
    hsrcDecl hsrcTy hsrcImm hdstDecl hdstTy hdstImm hcountInt hcountOp hpt
    hsrc_val hdst_val hoff0_s hoff0_d hcnt_pre hcnt1 he_s het_s he_d het_d
    hsrc_tgt hdst_tgt huninit_s hdst_live).2⟩
  rw [hstep]
  unfold evalCopyNonOverlapping
  rw [ha₁]; dsimp only; rw [ha₂]; dsimp only; rw [ha₃]; dsimp only
  rw [hcnt1, evalCopyNonOverlappingWithCount_stage1_single_eq
    hlook_s hlook_d hoff0_s hoff0_d hunion_s hunion_d,
    evalCopySingleDirect_uninit_src_ub huninit_s]
  cases e_s.perm <;> cases e_d.perm <;> rfl

/-- **Stage-1 Tree Borrows permission divergence (`LM-4.2`, Stage-1 `Trusted`)**:
copying `count = 1` element between distinct live primitive-scalar stack locals
when `e_s.perm = .disabled` or `e_d.perm` is `.frozen` / `.disabled`:
* Stage-1 `stepMirFn` (`evalCopyNonOverlappingWithCount`) enforces Tree Borrows
  read permission on `src` and write permission on `dst`
  (`stepMirFn body s = MirStepNode.fail .ub`);
* `lean-miri` under `annealMemoryCopyHooks` checks only allocation mutability
  and returns `.ok true`. -/
theorem step_intrinsic_copyNonOverlapping_stage1_perm_divergence
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
  obtain ⟨_, _, _, _, _, hcal, _, _, _, _, halloc, _⟩ := id hstate
  have hstep : stepMirFn body s =
      evalCopyNonOverlapping s (.copy ⟨srcIdx, []⟩) (.copy ⟨dstIdx, []⟩) countOp
        body.localDecls body.layouts := by
    rw [stepMirFn_eq_of_not_other body s hcal hphase]
    simp only [hbb, hstmt]; rfl
  have ha₁ : evalOperand s.frame.locals (.copy ⟨srcIdx, []⟩) s.memory.borrows s.memory.globals
      body.layouts s.memory.callerLocals body.localDecls = .ok (.ptr srcPtr 8) s.frame.locals := by
    unfold evalOperand; dsimp only; rw [hsrc_val]; rfl
  have ha₂ : evalOperand s.frame.locals (.copy ⟨dstIdx, []⟩) s.memory.borrows s.memory.globals
      body.layouts s.memory.callerLocals body.localDecls = .ok (.ptr dstPtr 8) s.frame.locals := by
    unfold evalOperand; dsimp only; rw [hdst_val]; rfl
  have ha₃ : evalOperand s.frame.locals countOp s.memory.borrows s.memory.globals
      body.layouts s.memory.callerLocals body.localDecls =
      .ok (.scalar countSc) s.frame.locals := by
    rcases hcnt_pre with ⟨cc, rfl, hv⟩ | ⟨idx, rfl, hsl⟩
    · unfold evalOperand; dsimp only; rw [hv]; rfl
    · unfold evalOperand; dsimp only; rw [hsl]; rfl
  have hlook_s : lookupBorrow s.memory.borrows srcPtr.tag = some e_s.toBorrowEntry := by
    rw [← het_s]; exact (halloc.borrow_sync e_s he_s).2
  have hlook_d : lookupBorrow s.memory.borrows dstPtr.tag = some e_d.toBorrowEntry := by
    rw [← het_d]; exact (halloc.borrow_sync e_d he_d).2
  refine ⟨?_, (step_intrinsic_copyNonOverlapping_perm_divergence hstate hphase hbb hstmt
    hsrcDecl hsrcTy hsrcImm hdstDecl hdstTy hdstImm hcountInt hcountOp hpt
    hsrc_val hdst_val hoff0_s hoff0_d hcnt_pre hcnt1 he_s het_s he_d het_d
    hne_loc hsrc_tgt hdst_tgt hsrc_live hdst_live hperm_bad).2⟩
  rw [hstep]
  unfold evalCopyNonOverlapping
  rw [ha₁]; dsimp only; rw [ha₂]; dsimp only; rw [ha₃]; dsimp only
  unfold evalCopyNonOverlappingWithCount
  rw [hcnt1]; dsimp only
  rw [hlook_s, hlook_d]
  dsimp only [AllocMapEntry.toBorrowEntry]
  cases hpS : e_s.perm <;> cases hpD : e_d.perm <;>
    first | rfl | (simp [hpS, hpD] at hperm_bad)


end LeanMiriSpec.Correspondence
