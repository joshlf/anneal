/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import LeanMiriSpec.Correspondence.SimLM2_2
import LeanMiriSpec.Correspondence.Witness

/-!
# Non-Vacuity Witnesses for the `LM-2.2` Correspondence (`WitLM2_2`)

This module constructs seventeen concrete `Runtime(PostCleanup)` MIR bodies and
execution traces witnessing that every `LM-2.2` definition, typing judgment,
and simulation theorem across `LayoutLM2_2`, `ProjLM2_2`, and `SimLM2_2` has
jointly satisfiable syntactic premises and executes in lockstep on Anneal and
upstream `lean-miri`:

1. **`AbiRepr.ScalarPair` + Immediate Copy + `forceAllocation` Field Write +
   `StorageDead` Deallocation (`lm22PairBody`)**: constructs `(u32, u16)` in
   `_1`, copies it into immediate `.structImm` local `_2` (`_2 = Copy(_1)`),
   reads `_2.1` directly from `.Immediate.scalarPair`, promotes `_2` to stack
   memory via `forceAllocation` on `_2.0 = const 0x99AABBCC_u32` (preserving
   `_2.1 = 0x5566_u16` and keeping trailing alignment padding bytes `6, 7`
   `.uninit`), re-reads `_2.0` into `_0`, frees both stack allocations via
   `StorageDead`, and instantiates `step_two_stmts_lm2_2_simulation` and
   `StateRelLM2_2.toStateRel_of_flat_imm (by rintro ⟨_, _⟩ _ _ h _ _ ⟨⟩; cases h)`.
2. **Unpadded `AbiRepr.Memory` Struct (`lm22UnpaddedBody`)**: constructs 3-field
   `UnpaddedTriple { a: u32, b: u32, c: u32 }` (`size = 12`, `0` padding bytes),
   overwrites `_1.1 = const 77_u32`, reads `_1.1`, and proves base `StateRel`
   while `_1` is live `.indirect` in stack memory (an unpadded aggregate projects
   to the base `MemPlaceRel … (some rootVal)` via `StructMemPlaceRel.toMemPlaceRel`).
3. **`AbiRepr.Scalar` Wrapper + Padded `AbiRepr.Memory` (`lm22PaddedBody`)**:
   proves `ValidStructLayout` at both `InnerU32(u32)` and
   `PaddedOuter { tag: u8, inner: InnerU32 }`, witnesses byte-level
   `writeField_preserves_other_fields_and_padding` + `has_uninit_of_padding_byte`,
   and traces `InnerU32` construction, `PaddedOuter` construction (`Move(_2)`),
   nested read `_1.1.0`, and nested write `_1.1.0 = const 99_u32` with padding
   bytes `1, 2, 3` `.uninit`, related by `StateRelLM2_2` while the padded struct
   is live in memory and by base `StateRel` once it is dead.
4. **2-Level Nested Struct `NestedOuter { tag: u8, inner: InnerPair { x: u32, y: u16 } }`
   (`lm22NestedBody`)**: proves `ValidStructLayout` at both `InnerPair` (`size = 8`,
   padding `6, 7`) and `NestedOuter` (`size = 12`, padding `1, 2, 3, 10, 11`),
   constructs `_2 = NestedOuter(7_u8, move _1)` via `scalarPairSub`, instantiates
   `step_two_stmts_lm2_2_simulation` directly on `_2 = NestedOuter(...)` followed
   by 2-level nested write `_2.1.1 = const 0xBEEF_u16` at byte offset `4 + 4 = 8`,
   verifies all 5 alignment padding bytes remain `.uninit`, and reads back
   `_2.0 = 7_u8`, `_2.1.0 = 0x11112222_u32`, and `_2.1.1 = 0xBEEF_u16`.
5. **Whole-Value Reassignment of a Memory-Backed `ScalarPair` (`lm22ReassignBody`)**:
   forces `_1 : (u32, u16)` into memory (aggregate + field write), proves its
   `lean-miri` local is `.live (.indirect mp)`, overwrites it with `_1 = copy _2`
   (`step_assign_use_struct_lm2_2_simulation`, upstream
   `writePlaceImmediateNoValidate` through memory), reads both new fields back,
   and runs the whole block through `step_stmts_lm2_2_simulation` at once.
-/

namespace LeanMiriSpec.Correspondence.Witness

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open LeanMiriSpec.Correspondence

/-! ## Shared Layout Primitives & Lockstep Trace Combinators -/

def lm22U32Ty : Ty := { kind := .uint .u32, layoutIdx := 0 }
def lm22U32Decl : LocalDecl := { mutability := .mut, ty := lm22U32Ty, debugName := none }

def lm22ConstU32 (n : Nat) : ConstOperand :=
  { ty := lm22U32Ty, val := .scalar (.int ⟨n, 4⟩) }

def lm22U32TypeLayout : TypeLayout :=
  { size := { bytes := 4 }
    align := { bytes := 4 }
    backendRepr := .scalar (.initialized (.int 32 false) { start := 0, end_ := 4294967295 })
    fields := .primitive
    variants := .single 0
    isUninhabited := false }

def lm22U16TypeLayout : TypeLayout :=
  { size := { bytes := 2 }
    align := { bytes := 2 }
    backendRepr := .scalar (.initialized (.int 16 false) { start := 0, end_ := 65535 })
    fields := .primitive
    variants := .single 0
    isUninhabited := false }

def lm22U8TypeLayout : TypeLayout :=
  { size := { bytes := 1 }
    align := { bytes := 1 }
    backendRepr := .scalar (.initialized (.int 8 false) { start := 0, end_ := 255 })
    fields := .primitive
    variants := .single 0
    isUninhabited := false }

def lm22FnAbiU32 : FnAbi :=
  { args := []
    ret := { layout := lm22U32TypeLayout, mode := .direct }
    conv := .rust
    canUnwind := false }

def lm22FnAbiU16 : FnAbi :=
  { args := []
    ret := { layout := lm22U16TypeLayout, mode := .direct }
    conv := .rust
    canUnwind := false }

def mkStmt22 (k : StatementKind) : MirAst.Statement :=
  { kind := k, span := "lm-2.2-witness" }

def mkTerm22 (k : TerminatorKind) : MirAst.Terminator :=
  { kind := k, span := "lm-2.2-witness" }

/-- Step `AnnealStepState` `n` times on `body`. -/
def lm22StepMiriN (body : CapturedMir) : Nat → AnnealStepState → AnnealStepState
  | 0, m => m
  | n + 1, m =>
      (Miri.Interpreter.Step.step (annealStepHooksLM2_2 body.localDecls body.layouts) ()
        (lm22StepMiriN body n m)).1

/-- Step `MachineState` `n` times on `body`. -/
def lm22StepAnnealN (body : CapturedMir) : Nat → MachineState → MachineState
  | 0, s => s
  | n + 1, s =>
      match stepMirFn body (lm22StepAnnealN body n s) with
      | .tau (.running s') => s'
      | _ => lm22StepAnnealN body n s

theorem lm22_u32_prim : IsPrimScalarTy lm22U32Ty :=
  Or.inr (Or.inr (Or.inr ⟨.u32, rfl⟩))

theorem lm22_u16_prim : IsPrimScalarTy u16Ty :=
  Or.inr (Or.inr (Or.inr ⟨.u16, rfl⟩))

theorem lm22_u8_prim : IsPrimScalarTy u8Ty :=
  Or.inr (Or.inr (Or.inr ⟨.u8, rfl⟩))

theorem lm22_constU32_wt {body : CapturedMir} {env : StructTypeEnv}
    {stEnv : LM2_2StaticEnv} (n : Nat) (hn : n < 4294967296)
    (henv : env lm22U32Ty = none) :
    WellTypedLM2_2Operand body env stEnv (.constant (lm22ConstU32 n)) lm22U32Ty :=
  .constScalar _ ⟨n, 4⟩ rfl henv lm22_u32_prim (Or.inr (Or.inr (Or.inl rfl)))
    (by rw [scalarModulus_eq_two_pow]; exact hn) rfl nofun nofun

theorem lm22_constU16_wt {body : CapturedMir} {env : StructTypeEnv}
    {stEnv : LM2_2StaticEnv} (n : Nat) (hn : n < 65536)
    (henv : env u16Ty = none) :
    WellTypedLM2_2Operand body env stEnv (.constant (constU16 n)) u16Ty :=
  .constScalar _ ⟨n, 2⟩ rfl henv lm22_u16_prim (Or.inr (Or.inl rfl))
    (by rw [scalarModulus_eq_two_pow]; exact hn) rfl nofun nofun

theorem lm22_constU8_wt {body : CapturedMir} {env : StructTypeEnv}
    {stEnv : LM2_2StaticEnv} (n : Nat) (hn : n < 256)
    (henv : env u8Ty = none) :
    WellTypedLM2_2Operand body env stEnv (.constant (constU8 n)) u8Ty :=
  .constScalar _ ⟨n, 1⟩ rfl henv lm22_u8_prim (Or.inl rfl)
    (by rw [scalarModulus_eq_two_pow]; exact hn) rfl nofun nofun

/-- Advance `StateRelLM2_2`, `runAnnealBounded`, and `runMiriBoundedLM2_2` across one
well-typed `LM-2.2` statement when Anneal steps to `s'`. -/
theorem lm22_runBounded_step
    {body : CapturedMir} {env : StructTypeEnv}
    {stEnv stEnv' : LM2_2StaticEnv} {k k' fuel : Nat}
    {s s' : MachineState} {m : AnnealStepState}
    {bb : BasicBlockData} {stmt : MirAst.Statement}
    (hstate : StateRelLM2_2 body env stEnv k s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some stmt)
    (hwt : WellTypedLM2_2Stmt body env stEnv k stmt stEnv' k')
    (ha : stepMirFn body s = .step s') :
    StepRelLM2_2 body env stEnv' k' m (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksLM2_2 body.localDecls body.layouts) () m) ∧
    StateRelLM2_2 body env stEnv' k' s'
      (Miri.Interpreter.Step.step (annealStepHooksLM2_2 body.localDecls body.layouts) () m).1 ∧
    runAnnealBounded body (fuel + 1) s = runAnnealBounded body fuel s' ∧
    runMiriBoundedLM2_2 body (fuel + 1) m =
      runMiriBoundedLM2_2 body fuel
        (Miri.Interpreter.Step.step (annealStepHooksLM2_2 body.localDecls body.layouts) () m).1 := by
  have hsim := step_stmt_lm2_2_simulation hstate hphase hbb hstmt hwt
  refine ⟨hsim, ?_⟩
  have ha_run : runAnnealBounded body (fuel + 1) s = runAnnealBounded body fuel s' := by
    conv => lhs; unfold runAnnealBounded
    rw [ha]; rfl
  rw [ha] at hsim
  generalize hm : Miri.Interpreter.Step.step (annealStepHooksLM2_2 body.localDecls body.layouts) () m = r
    at hsim ⊢
  cases hsim with
  | step _ m' hs' =>
    have hne : m'.stack.frames.isEmpty = false := by
      rcases hs' with ⟨tf', htf', _, _, _, _, _, _, _, _, _, _, _, _⟩
      rw [htf']; rfl
    have hm_run : runMiriBoundedLM2_2 body (fuel + 1) m = runMiriBoundedLM2_2 body fuel m' := by
      conv => lhs; unfold runMiriBoundedLM2_2
      rw [hm]; dsimp only; rw [hne]; rfl
    exact ⟨hs', ha_run, hm_run⟩

/-- Symbolic root-frame `return` agreement from base `StateRel` via
`step_terminator_goto_return_simulation_lm2_2`, avoiding opaque `USize` evaluation in
`Std.DHashMap` when multiple stack allocations have been freed by `StorageDead`. -/
theorem lm22_return_agree_of_stateRel
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {bb : BasicBlockData} {decl0 : LocalDecl}
    {bits sz : Nat} {mem' : Memory}
    (hstate : StateRel body s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    (hstmt_len : s.frame.stmtIdx = length bb.statements)
    (hcleanup : bb.isCleanup = false)
    (hret : bb.terminator.kind = .return_)
    (hdecl0 : get? body.localDecls 0 = some decl0)
    (hprim0 : IsPrimScalarTy decl0.ty)
    (himm0 : ∀ tf, m.stack.frames = #[tf] → IsImmediateFrameLocal tf 0)
    (ha : stepMirFn body s = .retNormal (.scalar ⟨bits, sz⟩) mem') :
    annealOutcomeScalarBits sz (runAnnealBounded body 1 s) = some bits ∧
    miriOutcomeScalarBits sz (runMiriBoundedLM2_2 body 1 m) = some bits := by
  have hsim := step_terminator_goto_return_simulation_lm2_2 hstate hphase hbb hstmt_none
    hstmt_len hcleanup (Or.inr (Or.inl ⟨hret, decl0, hdecl0, hprim0.size_ne_zero, himm0⟩))
  have ha_out : annealOutcomeScalarBits sz (runAnnealBounded body 1 s) = some bits := by
    unfold runAnnealBounded annealOutcomeScalarBits
    rw [ha]
    dsimp only [MirStepNode.retNormal]
    simp
  refine ⟨ha_out, ?_⟩
  rw [ha] at hsim
  generalize hm : Miri.Interpreter.Step.step (annealStepHooksLM2_2 body.localDecls body.layouts) () m = r
    at hsim
  cases hsim with
  | retRoot decl0' _ imm0 _ m' hdecl0' hretOp himmRel hm'_eq =>
    have hd_eq := Option.some.inj (hdecl0.symm.trans hdecl0')
    subst hd_eq
    obtain ⟨sc, msc, hsc_eq, rfl, hrel, _, _, _⟩ := himmRel.of_primitive_scalar hprim0
    injection hsc_eq with hsc_eq'
    cases hsc_eq'
    rcases hrel with ⟨hvb, hcan, hsz_r, hdata_r⟩
    have hemp : m'.stack.frames.isEmpty = true := by rw [hm'_eq]; rfl
    have hm_out : runMiriBoundedLM2_2 body 1 m =
        .returned m' (.ok (.immediate (.scalar (.fromScalarInt msc)))) := by
      unfold runMiriBoundedLM2_2
      rw [hm]; dsimp only; rw [hemp, hretOp]; rfl
    rw [hm_out]
    unfold miriOutcomeScalarBits
    have hto : (Miri.Memory.Scalar.fromScalarInt msc : Miri.Memory.Scalar AnnealProv).toScalarInt =
        .ok msc := rfl
    have hsz_eq : (msc.size == Miri.ABI.Size.ofBytes (UInt64.ofNat sz)) = true := by
      rw [hsz_r]; dsimp only
      rcases hvb with rfl | rfl | rfl | rfl | rfl <;> decide
    have hlt128 : bits < 2 ^ 128 := by
      dsimp only at hvb hcan
      rw [scalarModulus_eq_two_pow] at hcan
      rcases hvb with rfl | rfl | rfl | rfl | rfl <;> omega
    have hbits_eq : msc.data.toNat = bits := by
      rw [hdata_r]; dsimp only
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt128]
    simp only [hemp, ↓reduceIte, hto, hsz_eq, hbits_eq]

def isAnnealTauStep (res : MirStepNode) : Bool :=
  match res with
  | .tau (.running _) => true
  | _ => false

theorem stepMirFn_eq_step_lm22StepAnnealN (body : CapturedMir) (n : Nat) (s0 : MachineState)
    (hok : isAnnealTauStep (stepMirFn body (lm22StepAnnealN body n s0)) = true) :
    stepMirFn body (lm22StepAnnealN body n s0) = .step (lm22StepAnnealN body (n + 1) s0) := by
  conv => rhs; unfold lm22StepAnnealN
  cases h : stepMirFn body (lm22StepAnnealN body n s0) with
  | tau st =>
    cases st with
    | running s' => rfl
    | halted _ | faulted _ => rw [h] at hok; cases hok
  | ret _ | vis _ _ => rw [h] at hok; cases hok

theorem lm22_trace_step
    {body : CapturedMir} {env : StructTypeEnv}
    {stEnv stEnv_raw : LM2_2StaticEnv} (stEnv' : LM2_2StaticEnv)
    {k k' n fuel : Nat} {s0 : MachineState} {m0 : AnnealStepState}
    {bb : BasicBlockData} {stmt : MirAst.Statement}
    (hstate : StateRelLM2_2 body env stEnv k (lm22StepAnnealN body n s0) (lm22StepMiriN body n m0))
    (hphase : ∀ p, body.phase ≠ .other p)
    (hbb : get? body.basicBlocks (lm22StepAnnealN body n s0).frame.blockIdx = some bb)
    (hstmt : get? bb.statements (lm22StepAnnealN body n s0).frame.stmtIdx = some stmt)
    (hwt : WellTypedLM2_2Stmt body env stEnv k stmt stEnv_raw k')
    (hpost : stEnv_raw = stEnv')
    (hok : isAnnealTauStep (stepMirFn body (lm22StepAnnealN body n s0)) = true) :
    StateRelLM2_2 body env stEnv' k'
      (lm22StepAnnealN body (n + 1) s0) (lm22StepMiriN body (n + 1) m0) ∧
    runAnnealBounded body (fuel + 1) (lm22StepAnnealN body n s0) =
      runAnnealBounded body fuel (lm22StepAnnealN body (n + 1) s0) ∧
    runMiriBoundedLM2_2 body (fuel + 1) (lm22StepMiriN body n m0) =
      runMiriBoundedLM2_2 body fuel (lm22StepMiriN body (n + 1) m0) := by
  subst hpost
  exact (lm22_runBounded_step hstate hphase hbb hstmt hwt
    (stepMirFn_eq_step_lm22StepAnnealN body n s0 hok)).2

/-- Extract `StructMemPlaceRel` for an initialized memory-backed local `idx`
(`idx ∉ immLocals` and verified indirect by a non-immediate witness or by showing
`StateRelLM2_2` when `topFrame.locals[idx]?` is not `.immediate`). -/
theorem lm22_extract_struct_local
    {body : CapturedMir} {env : StructTypeEnv}
    {stEnv : LM2_2StaticEnv} {k : Nat}
    {s : MachineState} {m : AnnealStepState}
    {idx : Local} {decl : LocalDecl}
    {fields : List StructFieldDesc} {paths : List (List ProjectionElem)}
    {rootVal : Value}
    (hstate : StateRelLM2_2 body env stEnv k s m)
    (hdecl : get? body.localDecls idx = some decl)
    (henv : env decl.ty = some (fields, paths))
    (hslot : get? s.frame.locals idx = some (.init rootVal)) :
    (∃ imm, ImmediateStructRel decl.ty body.layouts fields paths rootVal imm) ∨
    (∃ mp, StructMemPlaceRel m.machine decl.ty body.layouts fields paths rootVal mp) := by
  rcases hstate with ⟨tf, _, _, _, hfr, _, _, _, _, _, _, _, _, _⟩
  obtain ⟨slot, mls, _, _, hsl, _, _, hloc⟩ := hfr.lookup_local hdecl
  have hsl_eq := Option.some.inj (hsl.symm.trans hslot)
  subst hsl_eq
  cases hloc with
  | base _ _ henv_none _ => rw [henv] at henv_none; cases henv_none
  | structImm fs ps _ imm _ henv' _ himm =>
    have heq := Option.some.inj (henv.symm.trans henv')
    rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
    exact Or.inl ⟨imm, himm⟩
  | structInd fs ps _ mp _ henv' _ hsmpr =>
    have heq := Option.some.inj (henv.symm.trans henv')
    rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
    exact Or.inr ⟨mp, hsmpr⟩

theorem lm22_not_immediateStructRel_of_memory {ty : Ty} {layouts : LayoutTable}
    {fields : List StructFieldDesc} {paths : List (List ProjectionElem)}
    {v : Value} {imm : Miri.Interpreter.Immediate AnnealProv}
    (hmem : (translateTy ty layouts).layout.backendRepr = .Memory (sized := true))
    (himm : ImmediateStructRel ty layouts fields paths v imm) : False := by
  cases himm with
  | scalarWrapper _ _ _ _ _ _ _ hrepr => rw [hmem] at hrepr; cases hrepr
  | scalarPair _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hrepr => rw [hmem] at hrepr; cases hrepr

theorem lm22_imm_of_mem_immLocals {body : CapturedMir} {env : StructTypeEnv}
    {stEnv : LM2_2StaticEnv} {k : Nat} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_2 body env stEnv k s m)
    {idx : Local} (hmem : idx ∈ stEnv.immLocals) :
    ∀ tf, m.stack.frames = #[tf] → IsImmediateFrameLocal tf idx := by
  intro tf htf mls hmls mp hmp
  rcases hstate with ⟨tf0, htf0, _, _, _, _, himm_env, _, _, _, _, _, _, _⟩
  cases Array.singleton_inj.mp (htf0.symm.trans htf)
  cases mls with
  | mk val lay => dsimp at hmp; subst hmp; exact himm_env idx hmem mp lay hmls

/-! ## 1. `AbiRepr.ScalarPair`, Immediate Copy, `forceAllocation` Write, & `StorageDead` -/

def lm22PairTy : Ty :=
  { kind := .tuple [.uint .u32, .uint .u16], layoutIdx := 0 }

def lm22PairDecl : LocalDecl :=
  { mutability := .mut, ty := lm22PairTy, debugName := none }

def lm22PairTypeLayout : TypeLayout :=
  { size := { bytes := 8 }
    align := { bytes := 4 }
    backendRepr :=
      .scalarPair
        (.initialized (.int 32 false) { start := 0, end_ := 4294967295 })
        (.initialized (.int 16 false) { start := 0, end_ := 65535 })
    fields := .arbitrary [{ bytes := 0 }, { bytes := 4 }] [0, 1]
    variants := .single 0
    isUninhabited := false
    fieldLayouts := [1, 2] }

def lm22PairLayoutTable : LayoutTable :=
  { pointerBits := 64
    isLittleEndian := true
    entries := [lm22PairTypeLayout, lm22U32TypeLayout, lm22U16TypeLayout] }

def lm22PairField0 : StructFieldDesc :=
  { offset := Miri.ABI.Size.ZERO
    ty := lm22U32Ty
    fieldLayout := (translateTy lm22U32Ty lm22PairLayoutTable).layout }

def lm22PairField1 : StructFieldDesc :=
  { offset := Miri.ABI.Size.ofBytes 4
    ty := u16Ty
    fieldLayout := (translateTy u16Ty lm22PairLayoutTable).layout }

def lm22PairFields : List StructFieldDesc :=
  [lm22PairField0, lm22PairField1]

def lm22PairPaths : List (List ProjectionElem) :=
  [[.field 0 lm22U32Ty], [.field 1 u16Ty]]

def lm22PairEnv : StructTypeEnv := fun ty =>
  match ty.kind with
  | .tuple [.uint .u32, .uint .u16] => some (lm22PairFields, lm22PairPaths)
  | _ => none

theorem lm22Pair_validStructLayout :
    ValidStructLayout (translateTy lm22PairTy lm22PairLayoutTable).layout lm22PairFields := by
  refine
    { fields_in_bounds := ?_
      fields_disjoint := ?_
      fields_aligned := ?_
      fields_shape_valid := Or.inr (ValidStructLayout.arbitrary_flat #[0, 1] rfl (by decide)) }
  · intro i hi
    match i with
    | 0 => change lm22PairField0.offset.bytes.toNat + lm22PairField0.fieldLayout.size.bytes.toNat ≤ _; decide
    | 1 => change lm22PairField1.offset.bytes.toNat + lm22PairField1.fieldLayout.size.bytes.toNat ≤ _; decide
    | _ + 2 => simp [lm22PairFields] at hi; omega
  · intro i j hi hj hne
    match i, j with
    | 0, 0 | 1, 1 => exact False.elim (hne rfl)
    | 0, 1 =>
      left
      change lm22PairField0.offset.bytes.toNat + lm22PairField0.fieldLayout.size.bytes.toNat ≤
        lm22PairField1.offset.bytes.toNat
      decide
    | 1, 0 =>
      right
      change lm22PairField0.offset.bytes.toNat + lm22PairField0.fieldLayout.size.bytes.toNat ≤
        lm22PairField1.offset.bytes.toNat
      decide
    | _ + 2, _ => simp [lm22PairFields] at hi; omega
    | _, _ + 2 => simp [lm22PairFields] at hj; omega
  · intro i hi
    match i with
    | 0 => change 2 ^ lm22PairField0.fieldLayout.align.abi.pow2 ∣ lm22PairField0.offset.bytes.toNat; decide
    | 1 => change 2 ^ lm22PairField1.fieldLayout.align.abi.pow2 ∣ lm22PairField1.offset.bytes.toNat; decide
    | _ + 2 => simp [lm22PairFields] at hi; omega

theorem lm22Pair_isImmediateStructTy :
    IsImmediateStructTy lm22PairEnv lm22PairLayoutTable lm22PairTy
      lm22PairFields lm22PairPaths :=
  .scalarPair lm22PairField0 lm22PairField1 lm22U32Ty u16Ty [] []
    _ _ (Miri.ABI.Size.ofBytes 4)
    rfl lm22Pair_validStructLayout (by decide)
    (Or.inl ⟨[.uint .u32, .uint .u16], rfl⟩)
    (fun _ h => nomatch h)
    rfl (by decide) (by decide) (by decide) (by decide)
    rfl rfl rfl rfl
    (Or.inl lm22_u32_prim) (Or.inl lm22_u16_prim)
    lm22_u32_prim lm22_u16_prim
    (Or.inl ⟨rfl, rfl⟩) (Or.inl ⟨rfl, rfl⟩)

theorem lm22Pair_trailing_padding_bytes :
    isStructPaddingByte lm22PairFields (Miri.ABI.Size.ofBytes 8) 6 ∧
    isStructPaddingByte lm22PairFields (Miri.ABI.Size.ofBytes 8) 7 := by
  refine ⟨⟨by decide, ?_⟩, ⟨by decide, ?_⟩⟩ <;>
    (intro f hf
     cases hf with
     | head => right; decide
     | tail _ hf2 =>
       cases hf2 with
       | head => right; decide
       | tail _ hnil => cases hnil)

/-- `Runtime(PostCleanup)` MIR exercising `AbiRepr.ScalarPair` construction,
immediate `.structImm` copy (`_2 = Copy(_1)`), immediate `ScalarPair` projection
read (`_3 = Copy(_2.1)`), `forceAllocation` field write (`_2.0 = const 0x99AABBCC_u32`)
preserving `_2.1 = 0x5566_u16` and keeping trailing padding bytes `6, 7` `.uninit`,
re-read (`_0 = Copy(_2.0)`), and `StorageDead` stack deallocation. -/
def lm22PairBody : CapturedMir where
  defPath := "lm_2_2_witness::scalar_pair"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [lm22U32Decl, lm22PairDecl, lm22PairDecl, u16Decl]
  basicBlocks := [
    { statements := [
        mkStmt22 (.storageLive 1),
        mkStmt22 (.storageLive 2),
        mkStmt22 (.storageLive 3),
        mkStmt22 (.assign ⟨1, []⟩
          (.aggregate .tuple
            [.constant (lm22ConstU32 0x11223344), .constant (constU16 0x5566)])),
        mkStmt22 (.assign ⟨2, []⟩ (.use (.copy ⟨1, []⟩))),
        mkStmt22 (.assign ⟨3, []⟩ (.use (.copy ⟨2, [.field 1 u16Ty]⟩))),
        mkStmt22 (.assign ⟨2, [.field 0 lm22U32Ty]⟩
          (.use (.constant (lm22ConstU32 0x99AABBCC)))),
        mkStmt22 (.assign ⟨0, []⟩ (.use (.copy ⟨2, [.field 0 lm22U32Ty]⟩))),
        mkStmt22 (.storageDead 3),
        mkStmt22 (.storageDead 2),
        mkStmt22 (.storageDead 1)],
      terminator := mkTerm22 .return_,
      isCleanup := false }]
  fnAbi := lm22FnAbiU32
  layouts := lm22PairLayoutTable
  allocations := []

def lm22PairMiriFrame0 :
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { body := translateBody lm22PairBody
    bodyIdentity := .ofCanonicalIndex 0
    functionInstance := { kind := .Item 0, args := #[] }
    extra := ()
    returnContinuation := .stop false
    returnPlace :=
      .frameLocal 0 0 none (translateTy lm22U32Ty lm22PairLayoutTable) (.ofAllocationToken 0)
    localsIdentity := .ofAllocationToken 0
    locals := #[
      { value := .live (.immediate .uninit), layout := none },
      { value := .dead, layout := none },
      { value := .dead, layout := none },
      { value := .dead, layout := none }]
    vaList := #[]
    trackCallerArg := none
    location := .mir ⟨0, 0⟩ }

def lm22PairMiriInit : AnnealStepState :=
  { stack := ⟨#[lm22PairMiriFrame0]⟩, machine := AnnealMachine.empty }

theorem lm22Pair_phase : ∀ p, lm22PairBody.phase ≠ .other p := by
  intro p h; cases h

def lm22PairStEnv0 : LM2_2StaticEnv := { initLocals := [], immLocals := [0] }

theorem lm22Pair_stateRelLM2_2_init :
    StateRelLM2_2 lm22PairBody lm22PairEnv lm22PairStEnv0 2
      (initMachineState lm22PairBody []) lm22PairMiriInit := by
  refine .mk lm22PairMiriFrame0 rfl rfl
    ⟨translateTy lm22U32Ty lm22PairLayoutTable, rfl⟩ ?_
    (fun _ h => nomatch h)
    (fun j hj mp l => by
      simp [lm22PairStEnv0] at hj; subst hj
      simp [lm22PairMiriFrame0])
    (Or.inr (AllocIdWatermark.empty 2 (by decide))) rfl rfl rfl rfl rfl
    (by
      intro i j _ _ _ _ _ hi _
      revert hi
      match i with
      | 0 | 1 | 2 | 3 => rintro ⟨⟩
      | _ + 4 => rintro ⟨⟩)
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro i decl slot mls hdecl hslot hmls
  match i with
  | 0 =>
    have hd : decl = lm22U32Decl := by simpa [lm22PairBody, get?] using hdecl.symm
    have hs : slot = .uninit := by
      simpa [initMachineState, lm22PairBody, initLocalsAux, get?] using hslot.symm
    have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
      simpa [lm22PairMiriFrame0] using hmls.symm
    subst hd hs hm
    exact .base .uninit _ rfl (.immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩))
  | 1 =>
    have hd : decl = lm22PairDecl := by simpa [lm22PairBody, get?] using hdecl.symm
    have hs : slot = .dead := by
      simpa [initMachineState, lm22PairBody, initLocalsAux, get?] using hslot.symm
    have hm : mls = { value := .dead, layout := none } := by
      simpa [lm22PairMiriFrame0] using hmls.symm
    subst hd hs hm
    exact .structDead lm22PairFields lm22PairPaths none rfl (fun _ h => nomatch h)
  | 2 =>
    have hd : decl = lm22PairDecl := by simpa [lm22PairBody, get?] using hdecl.symm
    have hs : slot = .dead := by
      simpa [initMachineState, lm22PairBody, initLocalsAux, get?] using hslot.symm
    have hm : mls = { value := .dead, layout := none } := by
      simpa [lm22PairMiriFrame0] using hmls.symm
    subst hd hs hm
    exact .structDead lm22PairFields lm22PairPaths none rfl (fun _ h => nomatch h)
  | 3 =>
    have hd : decl = u16Decl := by simpa [lm22PairBody, get?] using hdecl.symm
    have hs : slot = .dead := by
      simpa [initMachineState, lm22PairBody, initLocalsAux, get?] using hslot.symm
    have hm : mls = { value := .dead, layout := none } := by
      simpa [lm22PairMiriFrame0] using hmls.symm
    subst hd hs hm
    exact .base .dead _ rfl (.dead none (fun _ h => nomatch h))
  | _ + 4 => simp [lm22PairBody, get?] at hdecl

theorem lm22Pair_stmt3_wt (stEnv : LM2_2StaticEnv) (k : Nat) :
    WellTypedLM2_2Stmt lm22PairBody lm22PairEnv stEnv (k + 1)
      (mkStmt22 (.assign ⟨1, []⟩
        (.aggregate .tuple
          [.constant (lm22ConstU32 0x11223344), .constant (constU16 0x5566)])))
      (aggPostStaticEnv stEnv 1
        [.constant (lm22ConstU32 0x11223344), .constant (constU16 0x5566)]) k :=
  .assignAggregate stEnv k 1 .tuple _ _
    (.mk lm22PairDecl lm22PairFields lm22PairPaths _ _ rfl (Or.inl rfl) rfl rfl
      lm22Pair_validStructLayout (by decide) rfl rfl (by decide)
      (.cons stEnv 0 0 1 _ _ trivial
        (.primLeaf (by decide) _ (lm22_constU32_wt 0x11223344 (by decide) rfl)
          rfl lm22_u32_prim rfl rfl rfl rfl rfl rfl)
        (.cons _ 1 1 2 _ [] trivial
          (.primLeaf (by decide) _ (lm22_constU16_wt 0x5566 (by decide) rfl)
            rfl lm22_u16_prim rfl rfl rfl rfl rfl rfl)
          (.nil _ 2))))

theorem lm22Pair_stmt4_wt (stEnv : LM2_2StaticEnv) (k : Nat)
    (h2_imm : 2 ∈ stEnv.immLocals) :
    WellTypedLM2_2Stmt lm22PairBody lm22PairEnv stEnv k
      (mkStmt22 (.assign ⟨2, []⟩ (.use (.copy ⟨1, []⟩))))
      (usePostStaticEnv stEnv 2 (.copy ⟨1, []⟩)) k :=
  .assignUse stEnv k 2 (.copy ⟨1, []⟩) _
    (.mk lm22PairDecl rfl h2_imm
      (.immStructLocal false 1 lm22PairDecl lm22PairFields lm22PairPaths rfl
        lm22Pair_isImmediateStructTy))

theorem lm22Pair_stmt5_wt (stEnv : LM2_2StaticEnv) (k : Nat)
    (h3_imm : 3 ∈ stEnv.immLocals) :
    WellTypedLM2_2Stmt lm22PairBody lm22PairEnv stEnv k
      (mkStmt22 (.assign ⟨3, []⟩ (.use (.copy ⟨2, [.field 1 u16Ty]⟩))))
      (usePostStaticEnv stEnv 3 (.copy ⟨2, [.field 1 u16Ty]⟩)) k :=
  .assignUse stEnv k 3 (.copy ⟨2, [.field 1 u16Ty]⟩) _
    (.mk u16Decl rfl h3_imm
      (.projectedScalar false 2 [.field 1 u16Ty] u16Ty rfl
        (.mk lm22PairDecl lm22PairFields lm22PairPaths 1 (by decide) (by decide)
          rfl rfl rfl rfl lm22_u16_prim
          (.single (translateTy lm22PairTy lm22PairLayoutTable) 1 u16Ty
            (Miri.ABI.Size.ofBytes 4) (Or.inl lm22_u16_prim) rfl rfl
            (by decide)))))

theorem lm22Pair_stmt6_fw (stEnv : LM2_2StaticEnv)
    (h2_init : 2 ∈ stEnv.initLocals) :
    WellTypedLM2_2FieldWrite lm22PairBody lm22PairEnv stEnv
      2 [.field 0 lm22U32Ty] (.constant (lm22ConstU32 0x99AABBCC)) :=
  .mk lm22PairDecl lm22PairFields lm22PairPaths 0 rfl rfl h2_init rfl (by decide)
    (by decide) rfl
    (fun j hj hne => by
      match j with
      | 0 => exact False.elim (hne rfl)
      | 1 => exact .diff_head (by decide)
      | _ + 2 => simp [lm22PairPaths] at hj; omega)
    (.single (translateTy lm22PairTy lm22PairLayoutTable) 0 lm22U32Ty
      Miri.ABI.Size.ZERO (Or.inl lm22_u32_prim) rfl rfl (by decide))
    rfl rfl lm22_u32_prim trivial (lm22_constU32_wt 0x99AABBCC (by decide) rfl)

theorem lm22Pair_stmt6_wt (stEnv : LM2_2StaticEnv) (k : Nat)
    (h2_init : 2 ∈ stEnv.initLocals) :
    WellTypedLM2_2Stmt lm22PairBody lm22PairEnv stEnv (k + 1)
      (mkStmt22 (.assign ⟨2, [.field 0 lm22U32Ty]⟩
        (.use (.constant (lm22ConstU32 0x99AABBCC)))))
      (fieldWritePostStaticEnv stEnv 2 (.constant (lm22ConstU32 0x99AABBCC))) k :=
  .assignFieldWrite stEnv k 2 [.field 0 lm22U32Ty] (.constant (lm22ConstU32 0x99AABBCC)) _
    (lm22Pair_stmt6_fw stEnv h2_init)

theorem lm22Pair_stmt7_wt (stEnv : LM2_2StaticEnv) (k : Nat)
    (h0_imm : 0 ∈ stEnv.immLocals) :
    WellTypedLM2_2Stmt lm22PairBody lm22PairEnv stEnv k
      (mkStmt22 (.assign ⟨0, []⟩ (.use (.copy ⟨2, [.field 0 lm22U32Ty]⟩))))
      (usePostStaticEnv stEnv 0 (.copy ⟨2, [.field 0 lm22U32Ty]⟩)) k :=
  .assignUse stEnv k 0 (.copy ⟨2, [.field 0 lm22U32Ty]⟩) _
    (.mk lm22U32Decl rfl h0_imm
      (.projectedScalar false 2 [.field 0 lm22U32Ty] lm22U32Ty rfl
        (.mk lm22PairDecl lm22PairFields lm22PairPaths 0 (by decide) (by decide)
          rfl rfl rfl rfl lm22_u32_prim
          (.single (translateTy lm22PairTy lm22PairLayoutTable) 0 lm22U32Ty
            Miri.ABI.Size.ZERO (Or.inl lm22_u32_prim) rfl rfl (by decide)))))

/-- Lockstep `StateRelLM2_2` trace across `lm22PairBody`, together with:
1. `StateRelLM2_2` at step 5 while `_2` is an immediate `.structImm` `ScalarPair`
   and `_1` is a stack-allocated `.structInd` `ScalarPair` whose trailing padding
   is uninitialized (such a state has no base `StateRel` counterpart),
2. `step_two_stmts_lm2_2_simulation` composing immediate field read `_3 = Copy(_2.1)`
   with `forceAllocation` field write `_2.0 = const 0x99AABBCC_u32`,
3. `StructMemPlaceRel` + trailing alignment padding bytes `6, 7` `.uninit` on `_2`
   after `forceAllocation`,
4. base `StateRel` after `StorageDead` frees both stack allocations, and
5. `runAnnealBounded` / `runMiriBoundedLM2_2` return agreement (`0x99AABBCC_u32`). -/
theorem lm22Pair_full_trace_and_returns_agree :
    StateRelLM2_2 lm22PairBody lm22PairEnv { initLocals := [2, 1], immLocals := [2, 3, 2, 0] } 1
      (lm22StepAnnealN lm22PairBody 5 (initMachineState lm22PairBody []))
      (lm22StepMiriN lm22PairBody 5 lm22PairMiriInit) ∧
    (∃ mp localAlloc,
      StructMemPlaceRel
        (lm22StepMiriN lm22PairBody 7 lm22PairMiriInit).machine
        lm22PairTy lm22PairLayoutTable lm22PairFields lm22PairPaths
        (.aggregate 0 [.scalar ⟨0x99AABBCC, 4⟩, .scalar ⟨0x5566, 2⟩]) mp ∧
      (∃ allocId,
        (∃ tag, mp.ptr.provenance = some (.concrete allocId tag)) ∧
        (lm22StepMiriN lm22PairBody 7 lm22PairMiriInit).machine.memory.live.find?
          (fun (k, _) => k == allocId) = some (allocId, localAlloc)) ∧
      localAlloc.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 6) = .ok false ∧
      localAlloc.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 7) = .ok false ∧
      localAlloc.allocation.initializationMask.isRangeInitialized
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8)) ≠ .ok (.ok ())) ∧
    StateRel lm22PairBody
      (lm22StepAnnealN lm22PairBody 11 (initMachineState lm22PairBody []))
      (lm22StepMiriN lm22PairBody 11 lm22PairMiriInit) ∧
    annealOutcomeScalarBits 4
      (runAnnealBounded lm22PairBody 12 (initMachineState lm22PairBody [])) = some 0x99AABBCC ∧
    miriOutcomeScalarBits 4
      (runMiriBoundedLM2_2 lm22PairBody 12 lm22PairMiriInit) = some 0x99AABBCC := by
  have hs0 : StateRelLM2_2 lm22PairBody lm22PairEnv lm22PairStEnv0 2
      (lm22StepAnnealN lm22PairBody 0 (initMachineState lm22PairBody []))
      (lm22StepMiriN lm22PairBody 0 lm22PairMiriInit) := lm22Pair_stateRelLM2_2_init
  have ⟨hs1, ha0, hm0⟩ := lm22_trace_step ⟨[], [1, 0]⟩ (fuel := 11) hs0
    lm22Pair_phase rfl rfl (.storageLive _ 2 1 lm22PairDecl _ rfl) rfl rfl
  have ⟨hs2, ha1, hm1⟩ := lm22_trace_step ⟨[], [2, 1, 0]⟩ (fuel := 10) hs1
    lm22Pair_phase rfl rfl (.storageLive _ 2 2 lm22PairDecl _ rfl) rfl rfl
  have ⟨hs3, ha2, hm2⟩ := lm22_trace_step ⟨[], [3, 2, 1, 0]⟩ (fuel := 9) hs2
    lm22Pair_phase rfl rfl (.storageLive _ 2 3 u16Decl _ rfl) rfl rfl
  have ⟨hs4, ha3, hm3⟩ := lm22_trace_step ⟨[1], [3, 2, 0]⟩ (fuel := 8) hs3
    lm22Pair_phase rfl rfl (lm22Pair_stmt3_wt _ 1) rfl rfl
  have ⟨hs5, ha4, hm4⟩ := lm22_trace_step ⟨[2, 1], [2, 3, 2, 0]⟩ (fuel := 7) hs4
    lm22Pair_phase rfl rfl (lm22Pair_stmt4_wt _ 1 (by decide)) rfl rfl
  have htwo_5_6 := step_two_stmts_lm2_2_simulation hs5 lm22Pair_phase rfl rfl rfl
    (lm22Pair_stmt5_wt _ 1 (by decide)) (lm22Pair_stmt6_wt _ 0 (by decide))
  rcases htwo_5_6 with ⟨hub5, _⟩ | ⟨_, _, _, _, _, _⟩
  · cases hub5
  · have ⟨hs6, ha5, hm5⟩ := lm22_trace_step ⟨[3, 2, 1], [3, 2, 3, 2, 0]⟩ (fuel := 6) hs5
      lm22Pair_phase rfl rfl (lm22Pair_stmt5_wt _ 1 (by decide)) rfl rfl
    have ⟨hs7, ha6, hm6⟩ := lm22_trace_step ⟨[3, 2, 1], [3, 3, 0]⟩ (fuel := 5) hs6
      lm22Pair_phase rfl rfl (lm22Pair_stmt6_wt _ 0 (by decide)) rfl rfl
    have ⟨hs8, ha7, hm7⟩ := lm22_trace_step ⟨[0, 3, 2, 1], [0, 3, 3, 0]⟩ (fuel := 4) hs7
      lm22Pair_phase rfl rfl (lm22Pair_stmt7_wt _ 0 (by decide)) rfl rfl
    have ⟨hs9, ha8, hm8⟩ := lm22_trace_step ⟨[3, 0, 3, 2, 1], [3, 0, 3, 3, 0]⟩ (fuel := 3) hs8
      lm22Pair_phase rfl rfl (.storageDead _ 0 3 u16Decl _ rfl (by decide)) rfl rfl
    have ⟨hs10, ha9, hm9⟩ := lm22_trace_step ⟨[2, 3, 0, 3, 2, 1], [2, 3, 0, 3, 3, 0]⟩ (fuel := 2) hs9
      lm22Pair_phase rfl rfl (.storageDead _ 0 2 lm22PairDecl _ rfl (by decide)) rfl rfl
    have ⟨hs11, ha10, hm10⟩ := lm22_trace_step ⟨[1, 2, 3, 0, 3, 2, 1], [1, 2, 3, 0, 3, 3, 0]⟩ (fuel := 1) hs10
      lm22Pair_phase rfl rfl (.storageDead _ 0 1 lm22PairDecl _ rfl (by decide)) rfl rfl
    have hpad7 :
        ∃ mp localAlloc,
          StructMemPlaceRel
            (lm22StepMiriN lm22PairBody 7 lm22PairMiriInit).machine
            lm22PairTy lm22PairLayoutTable lm22PairFields lm22PairPaths
            (.aggregate 0 [.scalar ⟨0x99AABBCC, 4⟩, .scalar ⟨0x5566, 2⟩]) mp ∧
          (∃ allocId,
            (∃ tag, mp.ptr.provenance = some (.concrete allocId tag)) ∧
            (lm22StepMiriN lm22PairBody 7 lm22PairMiriInit).machine.memory.live.find?
              (fun (k, _) => k == allocId) = some (allocId, localAlloc)) ∧
          localAlloc.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 6) = .ok false ∧
          localAlloc.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 7) = .ok false ∧
          localAlloc.allocation.initializationMask.isRangeInitialized
            (Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8)) ≠ .ok (.ok ()) := by
      obtain ⟨decl7, fs7, ps7, rv7, mp7, hd7, he7, hsl7, hsmpr7, _⟩ :=
        step_assign_nested_field_write_post_structMemPlaceRel hs6 lm22Pair_phase rfl rfl
          (lm22Pair_stmt6_fw _ (by decide))
          (stepMirFn_eq_step_lm22StepAnnealN lm22PairBody 6 (initMachineState lm22PairBody []) rfl)
      cases Option.some.inj hd7
      rcases Prod.mk.inj (Option.some.inj he7) with ⟨rfl, rfl⟩
      have hrv_eq : rv7 = .aggregate 0 [.scalar ⟨0x99AABBCC, 4⟩, .scalar ⟨0x5566, 2⟩] := by
        have hr : get? (lm22StepAnnealN lm22PairBody 7 (initMachineState lm22PairBody [])).frame.locals 2 =
            some (.init (.aggregate 0 [.scalar ⟨0x99AABBCC, 4⟩, .scalar ⟨0x5566, 2⟩])) := rfl
        have hsome := Option.some.inj (hsl7.symm.trans hr)
        injection hsome
      subst hrv_eq
      obtain ⟨allocId, localAlloc, hprov, hfind, hpad_fn, hhas_uninit⟩ :=
        hsmpr7.has_uninit_of_padding_byte lm22Pair_trailing_padding_bytes.1
      exact ⟨mp7, localAlloc, hsmpr7, ⟨allocId, hprov, hfind⟩,
        hpad_fn 6 lm22Pair_trailing_padding_bytes.1,
        hpad_fn 7 lm22Pair_trailing_padding_bytes.2,
        hhas_uninit⟩
    have hbase11 : StateRel lm22PairBody
        (lm22StepAnnealN lm22PairBody 11 (initMachineState lm22PairBody []))
        (lm22StepMiriN lm22PairBody 11 lm22PairMiriInit) := by
      refine hs11.toStateRel_of_flat_imm (by rintro ⟨_, _⟩ _ _ h _ _ ⟨⟩; cases h) (fun i _ _ _ _ hdecl henv hslot _ => ?_) ?hunpad
      case hunpad =>
        intro i _ _ _ _ _ _ hdecl henv hslot _
        match i with
        | 0 | 3 => cases Option.some.inj hdecl; cases henv
        | 1 =>
          have hdead :
              get? (lm22StepAnnealN lm22PairBody 11 (initMachineState lm22PairBody [])).frame.locals 1 =
                some .dead := rfl
          rw [hdead] at hslot; cases hslot
        | 2 =>
          have hdead :
              get? (lm22StepAnnealN lm22PairBody 11 (initMachineState lm22PairBody [])).frame.locals 2 =
                some .dead := rfl
          rw [hdead] at hslot; cases hslot
        | _ + 4 => simp [lm22PairBody, get?] at hdecl
      match i with
      | 0 | 3 => exact False.elim (henv (by cases Option.some.inj hdecl; rfl))
      | 1 =>
        have hdead :
            get? (lm22StepAnnealN lm22PairBody 11 (initMachineState lm22PairBody [])).frame.locals 1 =
              some .dead := rfl
        rw [hdead] at hslot; cases hslot
      | 2 =>
        have hdead :
            get? (lm22StepAnnealN lm22PairBody 11 (initMachineState lm22PairBody [])).frame.locals 2 =
              some .dead := rfl
        rw [hdead] at hslot; cases hslot
      | _ + 4 => simp [lm22PairBody, get?] at hdecl
    have himm0_11 : ∀ tf,
        (lm22StepMiriN lm22PairBody 11 lm22PairMiriInit).stack.frames = #[tf] →
        IsImmediateFrameLocal tf 0 := by
      intro tf htf mls hmls mp hmp
      rcases hs11 with ⟨tf0, htf0, _, _, _, _, himm_env, _, _, _, _, _, _, _⟩
      have heq := Array.singleton_inj.mp (htf0.symm.trans htf)
      subst heq
      cases mls with
      | mk val lay =>
        dsimp at hmp; subst hmp
        exact himm_env 0 (by decide) mp lay hmls
    obtain ⟨ha_ret, hm_ret⟩ := lm22_return_agree_of_stateRel hbase11 lm22Pair_phase
      rfl rfl rfl rfl rfl rfl lm22_u32_prim himm0_11 rfl
    have ha_tot :
        runAnnealBounded lm22PairBody 12 (initMachineState lm22PairBody []) =
          runAnnealBounded lm22PairBody 1
            (lm22StepAnnealN lm22PairBody 11 (initMachineState lm22PairBody [])) :=
      ha0.trans (ha1.trans (ha2.trans (ha3.trans (ha4.trans
        (ha5.trans (ha6.trans (ha7.trans (ha8.trans (ha9.trans ha10)))))))))
    have hm_tot :
        runMiriBoundedLM2_2 lm22PairBody 12 lm22PairMiriInit =
          runMiriBoundedLM2_2 lm22PairBody 1 (lm22StepMiriN lm22PairBody 11 lm22PairMiriInit) :=
      hm0.trans (hm1.trans (hm2.trans (hm3.trans (hm4.trans
        (hm5.trans (hm6.trans (hm7.trans (hm8.trans (hm9.trans hm10)))))))))
    rw [ha_tot, hm_tot]
    exact ⟨hs5, hpad7, hbase11, ha_ret, hm_ret⟩


/-! ## 2. Unpadded `AbiRepr.Memory` Struct (`UnpaddedTriple { a: u32, b: u32, c: u32 }`) -/

def lm22UnpaddedTy : Ty :=
  { kind := .adt "lm22::UnpaddedTriple" [], layoutIdx := 0 }

def lm22UnpaddedDecl : LocalDecl :=
  { mutability := .mut, ty := lm22UnpaddedTy, debugName := none }

def lm22UnpaddedTypeLayout : TypeLayout :=
  { size := { bytes := 12 }
    align := { bytes := 4 }
    backendRepr := .memory
    fields := .arbitrary [{ bytes := 0 }, { bytes := 4 }, { bytes := 8 }] [0, 1, 2]
    variants := .single 0
    isUninhabited := false
    fieldLayouts := [1, 1, 1] }

def lm22UnpaddedLayoutTable : LayoutTable :=
  { pointerBits := 64
    isLittleEndian := true
    entries := [lm22UnpaddedTypeLayout, lm22U32TypeLayout] }

def lm22UnpaddedFields : List StructFieldDesc :=
  [ { offset := Miri.ABI.Size.ZERO
      ty := lm22U32Ty
      fieldLayout := (translateTy lm22U32Ty lm22UnpaddedLayoutTable).layout }
  , { offset := Miri.ABI.Size.ofBytes 4
      ty := lm22U32Ty
      fieldLayout := (translateTy lm22U32Ty lm22UnpaddedLayoutTable).layout }
  , { offset := Miri.ABI.Size.ofBytes 8
      ty := lm22U32Ty
      fieldLayout := (translateTy lm22U32Ty lm22UnpaddedLayoutTable).layout } ]

def lm22UnpaddedPaths : List (List ProjectionElem) :=
  [[.field 0 lm22U32Ty], [.field 1 lm22U32Ty], [.field 2 lm22U32Ty]]

def lm22UnpaddedEnv : StructTypeEnv := fun ty =>
  match ty.kind with
  | .adt "lm22::UnpaddedTriple" [] => some (lm22UnpaddedFields, lm22UnpaddedPaths)
  | _ => none

theorem lm22Unpadded_validStructLayout :
    ValidStructLayout (translateTy lm22UnpaddedTy lm22UnpaddedLayoutTable).layout
      lm22UnpaddedFields := by
  refine
    { fields_in_bounds := ?_
      fields_disjoint := ?_
      fields_aligned := ?_
      fields_shape_valid := Or.inr (ValidStructLayout.arbitrary_flat #[0, 1, 2] rfl (by decide)) }
  · intro i hi
    match i with
    | 0 | 1 | 2 => decide +revert
    | _ + 3 => simp [lm22UnpaddedFields] at hi; omega
  · intro i j hi hj hne
    match i, j with
    | 0, 0 | 1, 1 | 2, 2 => exact False.elim (hne rfl)
    | 0, 1 | 0, 2 | 1, 2 => left; decide +revert
    | 1, 0 | 2, 0 | 2, 1 => right; decide +revert
    | _ + 3, _ => simp [lm22UnpaddedFields] at hi; omega
    | _, _ + 3 => simp [lm22UnpaddedFields] at hj; omega
  · intro i hi
    match i with
    | 0 | 1 | 2 => decide +revert
    | _ + 3 => simp [lm22UnpaddedFields] at hi; omega

theorem lm22Unpadded_no_padding_bytes :
    ¬ ∃ p, isStructPaddingByte lm22UnpaddedFields (Miri.ABI.Size.ofBytes 12) p := by
  intro ⟨p, hp⟩
  have hlt := lm22Unpadded_validStructLayout.sumFieldBytes_lt_iff_exists_padding.mpr ⟨p, hp⟩
  exact absurd hlt (by decide)

/-- `Runtime(PostCleanup)` MIR constructing unpadded 3-field `UnpaddedTriple(10, 20, 30)`,
overwriting `_1.1 = const 77_u32`, reading `_0 = Copy(_1.1)`, and freeing `_1`. -/
def lm22UnpaddedBody : CapturedMir where
  defPath := "lm_2_2_witness::unpadded_triple"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [lm22U32Decl, lm22UnpaddedDecl]
  basicBlocks := [
    { statements := [
        mkStmt22 (.storageLive 1),
        mkStmt22 (.assign ⟨1, []⟩
          (.aggregate (.adt "lm22::UnpaddedTriple" 0 .none)
            [.constant (lm22ConstU32 10),
             .constant (lm22ConstU32 20),
             .constant (lm22ConstU32 30)])),
        mkStmt22 (.assign ⟨1, [.field 1 lm22U32Ty]⟩ (.use (.constant (lm22ConstU32 77)))),
        mkStmt22 (.assign ⟨0, []⟩ (.use (.copy ⟨1, [.field 1 lm22U32Ty]⟩))),
        mkStmt22 (.storageDead 1)],
      terminator := mkTerm22 .return_,
      isCleanup := false }]
  fnAbi := lm22FnAbiU32
  layouts := lm22UnpaddedLayoutTable
  allocations := []

def lm22UnpaddedMiriInit : AnnealStepState :=
  { stack := ⟨#[{
      body := translateBody lm22UnpaddedBody
      bodyIdentity := .ofCanonicalIndex 0
      functionInstance := { kind := .Item 0, args := #[] }
      extra := ()
      returnContinuation := .stop false
      returnPlace :=
        .frameLocal 0 0 none (translateTy lm22U32Ty lm22UnpaddedLayoutTable) (.ofAllocationToken 0)
      localsIdentity := .ofAllocationToken 0
      locals := #[
        { value := .live (.immediate .uninit), layout := none },
        { value := .dead, layout := none }]
      vaList := #[]
      trackCallerArg := none
      location := .mir ⟨0, 0⟩ }]⟩
    machine := AnnealMachine.empty }

theorem lm22Unpadded_phase : ∀ p, lm22UnpaddedBody.phase ≠ .other p := by
  intro p h; cases h

theorem lm22Unpadded_stateRelLM2_2_init :
    StateRelLM2_2 lm22UnpaddedBody lm22UnpaddedEnv { initLocals := [], immLocals := [0] } 2
      (initMachineState lm22UnpaddedBody []) lm22UnpaddedMiriInit := by
  refine .mk _ rfl rfl ⟨translateTy lm22U32Ty lm22UnpaddedLayoutTable, rfl⟩ ?_
    (fun _ h => nomatch h)
    (fun j hj mp l => by simp at hj; subst hj; dsimp [lm22UnpaddedMiriInit]; nofun)
    (Or.inr (AllocIdWatermark.empty 2 (by decide))) rfl rfl rfl rfl rfl
    (by intro i _ _ _ _ _ _ hi _; revert hi; match i with | 0 | 1 | _ + 2 => rintro ⟨⟩)
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro i decl slot mls hdecl hslot hmls
  match i with
  | 0 =>
    have hd : decl = lm22U32Decl := Option.some.inj hdecl.symm
    have hs : slot = .uninit := Option.some.inj hslot.symm
    have hm : mls = { value := .live (.immediate .uninit), layout := none } := Option.some.inj hmls.symm
    subst hd hs hm
    exact .base .uninit _ rfl (.immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩))
  | 1 =>
    have hd : decl = lm22UnpaddedDecl := Option.some.inj hdecl.symm
    have hs : slot = .dead := Option.some.inj hslot.symm
    have hm : mls = { value := .dead, layout := none } := Option.some.inj hmls.symm
    subst hd hs hm
    exact .structDead lm22UnpaddedFields lm22UnpaddedPaths none rfl (fun _ h => nomatch h)
  | _ + 2 => simp [lm22UnpaddedBody, get?] at hdecl

/-- Concrete kernel-decided + symbolic trace witness for unpadded `.Memory` struct
`UnpaddedTriple`: proves `StructMemPlaceRel` AND base `StateRel` at step 3 while
`_1` is live `.indirect` in stack memory (an unpadded aggregate has its whole
byte range initialized, so `StructMemPlaceRel.toMemPlaceRel` yields the base
`MemPlaceRel … (some rootVal)`), together with bounded return agreement
(`some 77`). -/
theorem lm22Unpadded_full_trace_and_returns_agree :
    (∃ mp,
      StructMemPlaceRel
        (lm22StepMiriN lm22UnpaddedBody 3 lm22UnpaddedMiriInit).machine
        lm22UnpaddedTy lm22UnpaddedLayoutTable lm22UnpaddedFields lm22UnpaddedPaths
        (.aggregate 0 [.scalar ⟨10, 4⟩, .scalar ⟨77, 4⟩, .scalar ⟨30, 4⟩]) mp) ∧
    StateRel lm22UnpaddedBody
      (lm22StepAnnealN lm22UnpaddedBody 3 (initMachineState lm22UnpaddedBody []))
      (lm22StepMiriN lm22UnpaddedBody 3 lm22UnpaddedMiriInit) ∧
    annealOutcomeScalarBits 4
      (runAnnealBounded lm22UnpaddedBody 6 (initMachineState lm22UnpaddedBody [])) = some 77 ∧
    miriOutcomeScalarBits 4
      (runMiriBoundedLM2_2 lm22UnpaddedBody 6 lm22UnpaddedMiriInit) = some 77 := by
  have hs0 : StateRelLM2_2 lm22UnpaddedBody lm22UnpaddedEnv { initLocals := [], immLocals := [0] } 2
      (lm22StepAnnealN lm22UnpaddedBody 0 (initMachineState lm22UnpaddedBody []))
      (lm22StepMiriN lm22UnpaddedBody 0 lm22UnpaddedMiriInit) :=
    lm22Unpadded_stateRelLM2_2_init
  have ⟨hs1, ha0, hm0⟩ := lm22_trace_step ⟨[], [1, 0]⟩ (fuel := 5) hs0
    lm22Unpadded_phase rfl rfl (.storageLive _ 2 1 lm22UnpaddedDecl _ rfl) rfl rfl
  have hwt1 : WellTypedLM2_2Stmt lm22UnpaddedBody lm22UnpaddedEnv ⟨[], [1, 0]⟩ 2
      (mkStmt22 (.assign ⟨1, []⟩
        (.aggregate (.adt "lm22::UnpaddedTriple" 0 .none)
          [.constant (lm22ConstU32 10),
           .constant (lm22ConstU32 20),
           .constant (lm22ConstU32 30)])))
      (aggPostStaticEnv ⟨[], [1, 0]⟩ 1
        [.constant (lm22ConstU32 10), .constant (lm22ConstU32 20), .constant (lm22ConstU32 30)]) 1 :=
    .assignAggregate _ 1 1 _ _ _
      (.mk lm22UnpaddedDecl lm22UnpaddedFields lm22UnpaddedPaths _ _ rfl
        (Or.inr ⟨"lm22::UnpaddedTriple", rfl⟩) rfl rfl lm22Unpadded_validStructLayout
        (by decide) rfl rfl (by decide)
        (.cons _ 0 0 1 _ _ trivial
          (.primLeaf (by decide) _ (lm22_constU32_wt 10 (by decide) rfl)
            rfl lm22_u32_prim rfl rfl rfl rfl rfl rfl)
          (.cons _ 1 1 2 _ _ trivial
            (.primLeaf (by decide) _ (lm22_constU32_wt 20 (by decide) rfl)
              rfl lm22_u32_prim rfl rfl rfl rfl rfl rfl)
            (.cons _ 2 2 3 _ [] trivial
              (.primLeaf (by decide) _ (lm22_constU32_wt 30 (by decide) rfl)
                rfl lm22_u32_prim rfl rfl rfl rfl rfl rfl)
              (.nil _ 3)))))
  have ⟨hs2, ha1, hm1⟩ := lm22_trace_step ⟨[1], [0]⟩ (fuel := 4) hs1
    lm22Unpadded_phase rfl rfl hwt1 rfl rfl
  have hwt2 : WellTypedLM2_2Stmt lm22UnpaddedBody lm22UnpaddedEnv ⟨[1], [0]⟩ 1
      (mkStmt22 (.assign ⟨1, [.field 1 lm22U32Ty]⟩ (.use (.constant (lm22ConstU32 77)))))
      (fieldWritePostStaticEnv ⟨[1], [0]⟩ 1 (.constant (lm22ConstU32 77))) 0 :=
    .assignFieldWrite _ 0 1 [.field 1 lm22U32Ty] (.constant (lm22ConstU32 77)) _
      (.mk lm22UnpaddedDecl lm22UnpaddedFields lm22UnpaddedPaths 1 rfl rfl (by decide)
        rfl (by decide) (by decide) rfl
        (fun j hj hne => by
          match j with
          | 0 => exact .diff_head (by decide)
          | 1 => exact False.elim (hne rfl)
          | 2 => exact .diff_head (by decide)
          | _ + 3 => simp [lm22UnpaddedPaths] at hj; omega)
        (.single (translateTy lm22UnpaddedTy lm22UnpaddedLayoutTable) 1 lm22U32Ty
          (Miri.ABI.Size.ofBytes 4) (Or.inl lm22_u32_prim) rfl rfl (by decide))
        rfl rfl lm22_u32_prim trivial (lm22_constU32_wt 77 (by decide) rfl))
  have ⟨hs3, ha2, hm2⟩ := lm22_trace_step ⟨[1], [0]⟩ (fuel := 3) hs2
    lm22Unpadded_phase rfl rfl hwt2 rfl rfl
  have hwt3 : WellTypedLM2_2Stmt lm22UnpaddedBody lm22UnpaddedEnv ⟨[1], [0]⟩ 0
      (mkStmt22 (.assign ⟨0, []⟩ (.use (.copy ⟨1, [.field 1 lm22U32Ty]⟩))))
      (usePostStaticEnv ⟨[1], [0]⟩ 0 (.copy ⟨1, [.field 1 lm22U32Ty]⟩)) 0 :=
    .assignUse _ 0 0 _ _
      (.mk lm22U32Decl rfl (by decide)
        (.projectedScalar false 1 [.field 1 lm22U32Ty] lm22U32Ty rfl
          (.mk lm22UnpaddedDecl lm22UnpaddedFields lm22UnpaddedPaths 1 (by decide) (by decide)
            rfl rfl rfl rfl lm22_u32_prim
            (.single (translateTy lm22UnpaddedTy lm22UnpaddedLayoutTable) 1 lm22U32Ty
              (Miri.ABI.Size.ofBytes 4) (Or.inl lm22_u32_prim) rfl rfl (by decide)))))
  have ⟨hs4, ha3, hm3⟩ := lm22_trace_step ⟨[0, 1], [0, 0]⟩ (fuel := 2) hs3
    lm22Unpadded_phase rfl rfl hwt3 rfl rfl
  have ⟨hs5, ha4, hm4⟩ := lm22_trace_step ⟨[1, 0, 1], [1, 0, 0]⟩ (fuel := 1) hs4
    lm22Unpadded_phase rfl rfl (.storageDead _ 0 1 lm22UnpaddedDecl _ rfl (by decide)) rfl rfl
  have hsmpr3 :
      ∃ mp,
        StructMemPlaceRel
          (lm22StepMiriN lm22UnpaddedBody 3 lm22UnpaddedMiriInit).machine
          lm22UnpaddedTy lm22UnpaddedLayoutTable lm22UnpaddedFields lm22UnpaddedPaths
          (.aggregate 0 [.scalar ⟨10, 4⟩, .scalar ⟨77, 4⟩, .scalar ⟨30, 4⟩]) mp := by
    rcases lm22_extract_struct_local hs3 (idx := 1) rfl rfl rfl with ⟨_, himm⟩ | hmp
    · exact False.elim (lm22_not_immediateStructRel_of_memory rfl himm)
    · exact hmp
  have hbase3 : StateRel lm22UnpaddedBody
      (lm22StepAnnealN lm22UnpaddedBody 3 (initMachineState lm22UnpaddedBody []))
      (lm22StepMiriN lm22UnpaddedBody 3 lm22UnpaddedMiriInit) := by
    refine hs3.toStateRel_of_flat_imm (by rintro ⟨_, _⟩ _ _ h _ _ ⟨⟩; cases h)
      (fun i decl v imm lay hdecl henv hslot ⟨tf, htf, hmls⟩ => ?_) ?hunpad
    case hunpad =>
      intro i decl _ _ _ fields paths hdecl henv _ _
      match i with
      | 0 => cases Option.some.inj hdecl; cases henv
      | 1 =>
        cases Option.some.inj hdecl
        rcases Prod.mk.inj (Option.some.inj henv) with ⟨rfl, rfl⟩
        decide
      | _ + 2 => simp [lm22UnpaddedBody, get?] at hdecl
    rcases hs3 with ⟨tf0, htf0, _, _, hfr, _, _, _, _, _, _, _, _, _⟩
    cases Array.singleton_inj.mp (htf0.symm.trans htf)
    cases hfr.locals_rel i decl (.init v) ⟨.live (.immediate imm), lay⟩ hdecl hslot hmls with
    | base _ _ he _ => exact False.elim (henv he)
    | structImm _ _ _ _ _ _ _ himm =>
      match i with
      | 0 => cases Option.some.inj hdecl; exact False.elim (henv rfl)
      | 1 =>
        cases Option.some.inj hdecl
        exact False.elim (lm22_not_immediateStructRel_of_memory rfl himm)
      | _ + 2 => simp [lm22UnpaddedBody, get?] at hdecl
  have hbase5 : StateRel lm22UnpaddedBody
      (lm22StepAnnealN lm22UnpaddedBody 5 (initMachineState lm22UnpaddedBody []))
      (lm22StepMiriN lm22UnpaddedBody 5 lm22UnpaddedMiriInit) := by
    refine hs5.toStateRel_of_flat_imm (by rintro ⟨_, _⟩ _ _ h _ _ ⟨⟩; cases h) (fun i _ _ _ _ hdecl henv hslot _ => ?_) ?hunpad
    case hunpad =>
      intro i _ _ _ _ _ _ hdecl henv hslot _
      match i with
      | 0 => cases Option.some.inj hdecl; cases henv
      | 1 =>
        have hdead :
            get? (lm22StepAnnealN lm22UnpaddedBody 5 (initMachineState lm22UnpaddedBody [])).frame.locals 1 =
              some .dead := rfl
        rw [hdead] at hslot; cases hslot
      | _ + 2 => simp [lm22UnpaddedBody, get?] at hdecl
    match i with
    | 0 => cases Option.some.inj hdecl; exact False.elim (henv rfl)
    | 1 =>
      have hdead :
          get? (lm22StepAnnealN lm22UnpaddedBody 5 (initMachineState lm22UnpaddedBody [])).frame.locals 1 =
            some .dead := rfl
      rw [hdead] at hslot; cases hslot
    | _ + 2 => simp [lm22UnpaddedBody, get?] at hdecl
  have himm0_5 : ∀ tf,
      (lm22StepMiriN lm22UnpaddedBody 5 lm22UnpaddedMiriInit).stack.frames = #[tf] →
      IsImmediateFrameLocal tf 0 := by
    intro tf htf mls hmls mp hmp
    rcases hs5 with ⟨tf0, htf0, _, _, _, _, himm_env, _, _, _, _, _, _, _⟩
    cases Array.singleton_inj.mp (htf0.symm.trans htf)
    cases mls with
    | mk val lay => dsimp at hmp; subst hmp; exact himm_env 0 (by decide) mp lay hmls
  obtain ⟨ha_ret, hm_ret⟩ := lm22_return_agree_of_stateRel hbase5 lm22Unpadded_phase
    rfl rfl rfl rfl rfl rfl lm22_u32_prim himm0_5 rfl
  have ha_tot :
      runAnnealBounded lm22UnpaddedBody 6 (initMachineState lm22UnpaddedBody []) =
        runAnnealBounded lm22UnpaddedBody 1
          (lm22StepAnnealN lm22UnpaddedBody 5 (initMachineState lm22UnpaddedBody [])) :=
    ha0.trans (ha1.trans (ha2.trans (ha3.trans ha4)))
  have hm_tot :
      runMiriBoundedLM2_2 lm22UnpaddedBody 6 lm22UnpaddedMiriInit =
        runMiriBoundedLM2_2 lm22UnpaddedBody 1 (lm22StepMiriN lm22UnpaddedBody 5 lm22UnpaddedMiriInit) :=
    hm0.trans (hm1.trans (hm2.trans (hm3.trans hm4)))
  rw [ha_tot, hm_tot]
  exact ⟨hsmpr3, hbase3, ha_ret, hm_ret⟩


/-! ## 3. `AbiRepr.Scalar` Wrapper (`InnerU32`) + Padded `AbiRepr.Memory` (`PaddedOuter`) -/

def lm22InnerU32Ty : Ty :=
  { kind := .adt "lm22::InnerU32" [], layoutIdx := 1 }

def lm22InnerU32Decl : LocalDecl :=
  { mutability := .mut, ty := lm22InnerU32Ty, debugName := none }

def lm22PaddedTy : Ty :=
  { kind := .adt "lm22::PaddedOuter" [], layoutIdx := 0 }

def lm22PaddedDecl : LocalDecl :=
  { mutability := .mut, ty := lm22PaddedTy, debugName := none }

def lm22InnerU32TypeLayout : TypeLayout :=
  { size := { bytes := 4 }
    align := { bytes := 4 }
    backendRepr := .scalar (.initialized (.int 32 false) { start := 0, end_ := 4294967295 })
    fields := .arbitrary [{ bytes := 0 }] [0]
    variants := .single 0
    isUninhabited := false
    fieldLayouts := [2] }

def lm22PaddedTypeLayout : TypeLayout :=
  { size := { bytes := 8 }
    align := { bytes := 4 }
    backendRepr := .memory
    fields := .arbitrary [{ bytes := 0 }, { bytes := 4 }] [0, 1]
    variants := .single 0
    isUninhabited := false
    fieldLayouts := [3, 1] }

def lm22PaddedLayoutTable : LayoutTable :=
  { pointerBits := 64
    isLittleEndian := true
    entries := [lm22PaddedTypeLayout, lm22InnerU32TypeLayout, lm22U32TypeLayout, lm22U8TypeLayout] }

def lm22InnerU32Field0 : StructFieldDesc :=
  { offset := Miri.ABI.Size.ZERO
    ty := lm22U32Ty
    fieldLayout := (translateTy lm22U32Ty lm22PaddedLayoutTable).layout }

def lm22PaddedField0 : StructFieldDesc :=
  { offset := Miri.ABI.Size.ZERO
    ty := u8Ty
    fieldLayout := (translateTy u8Ty lm22PaddedLayoutTable).layout }

def lm22PaddedField1 : StructFieldDesc :=
  { offset := Miri.ABI.Size.ofBytes 4
    ty := lm22U32Ty
    fieldLayout := (translateTy lm22U32Ty lm22PaddedLayoutTable).layout }

def lm22PaddedFields : List StructFieldDesc :=
  [lm22PaddedField0, lm22PaddedField1]

def lm22PaddedPaths : List (List ProjectionElem) :=
  [[.field 0 u8Ty], [.field 1 lm22InnerU32Ty, .field 0 lm22U32Ty]]

def lm22PaddedEnv : StructTypeEnv := fun ty =>
  match ty.kind with
  | .adt "lm22::InnerU32" [] => some ([lm22InnerU32Field0], [[.field 0 lm22U32Ty]])
  | .adt "lm22::PaddedOuter" [] => some (lm22PaddedFields, lm22PaddedPaths)
  | _ => none

theorem lm22InnerU32_validStructLayout :
    ValidStructLayout (translateTy lm22InnerU32Ty lm22PaddedLayoutTable).layout
      [lm22InnerU32Field0] := by
  refine
    { fields_in_bounds := fun i hi => by
        match i with
        | 0 => decide +revert
        | _ + 1 => simp at hi
      fields_disjoint := fun i j hi hj hne => by
        match i, j with
        | 0, 0 => exact False.elim (hne rfl)
        | _ + 1, _ => simp at hi
        | _, _ + 1 => simp at hj
      fields_aligned := fun i hi => by
        match i with
        | 0 => decide +revert
        | _ + 1 => simp at hi
      fields_shape_valid := Or.inr (ValidStructLayout.arbitrary_flat #[0] rfl (by decide)) }

theorem lm22InnerU32_isImmediateStructTy :
    IsImmediateStructTy lm22PaddedEnv lm22PaddedLayoutTable lm22InnerU32Ty
      [lm22InnerU32Field0] [[.field 0 lm22U32Ty]] :=
  .scalarWrapper lm22InnerU32Field0 [.field 0 lm22U32Ty] _
    rfl lm22InnerU32_validStructLayout rfl rfl nofun
    (.single (translateTy lm22InnerU32Ty lm22PaddedLayoutTable) lm22U32Ty
      lm22_u32_prim rfl rfl)
    rfl rfl lm22_u32_prim

theorem lm22Padded_validStructLayout :
    ValidStructLayout (translateTy lm22PaddedTy lm22PaddedLayoutTable).layout
      lm22PaddedFields := by
  refine
    { fields_in_bounds := fun i hi => by
        match i with
        | 0 | 1 => decide +revert
        | _ + 2 => simp [lm22PaddedFields] at hi; omega
      fields_disjoint := fun i j hi hj hne => by
        match i, j with
        | 0, 0 | 1, 1 => exact False.elim (hne rfl)
        | 0, 1 => left; decide +revert
        | 1, 0 => right; decide +revert
        | _ + 2, _ => simp [lm22PaddedFields] at hi; omega
        | _, _ + 2 => simp [lm22PaddedFields] at hj; omega
      fields_aligned := fun i hi => by
        match i with
        | 0 | 1 => decide +revert
        | _ + 2 => simp [lm22PaddedFields] at hi; omega
      fields_shape_valid := Or.inr (ValidStructLayout.arbitrary_flat #[0, 1] rfl (by decide)) }

theorem lm22Padded_interfield_padding_bytes :
    isStructPaddingByte lm22PaddedFields (Miri.ABI.Size.ofBytes 8) 1 ∧
    isStructPaddingByte lm22PaddedFields (Miri.ABI.Size.ofBytes 8) 2 ∧
    isStructPaddingByte lm22PaddedFields (Miri.ABI.Size.ofBytes 8) 3 := by
  refine ⟨⟨by decide, ?_⟩, ⟨by decide, ?_⟩, ⟨by decide, ?_⟩⟩ <;>
    (intro f hf
     cases hf with
     | head => right; decide
     | tail _ hf2 =>
       cases hf2 with
       | head => left; decide
       | tail _ hnil => cases hnil)

/-- Direct byte-level instantiation of `writeField_preserves_other_fields_and_padding`
on `PaddedOuter { tag: u8, inner: InnerU32 }`: writing `inner.0 = 99_u32` into a
fresh uninitialized 8-byte allocation initializes `[4, 8)` while leaving padding
bytes `1, 2, 3` `.uninit`. -/
theorem lm22Padded_writeField_preserves_witness :
    ∃ (A' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)),
      (∃ raw,
        Miri.Memory.Allocation.tryNew (Miri.ABI.Size.ofBytes 8)
          (translateAlignBytes 4) .Uninit annealZeroedStorage = .ok raw ∧
        Miri.Memory.Allocation.writeScalar annealTargetDataLayout
          (Miri.Memory.allocRange (Miri.ABI.Size.ofBytes 4) (Miri.ABI.Size.ofBytes 4))
          (Miri.Memory.Scalar.fromScalarInt (Miri.Memory.ScalarInt.ofUInt32 99))
          (raw.withExtra (none : Option Miri.TreeBorrows.BorrowTree)) = .ok () A') ∧
      A'.initializationMask.isRangeInitialized
        (Miri.Memory.allocRange (Miri.ABI.Size.ofBytes 4) (Miri.ABI.Size.ofBytes 4)) = .ok (.ok ()) ∧
      A'.initializationMask.get (Miri.ABI.Size.ofBytes 1) = .ok false ∧
      A'.initializationMask.get (Miri.ABI.Size.ofBytes 2) = .ok false ∧
      A'.initializationMask.get (Miri.ABI.Size.ofBytes 3) = .ok false := by
  let extra0 : Option Miri.TreeBorrows.BorrowTree := none
  obtain ⟨raw, htry, hbs, hlen, hmut, hpmap, hmask⟩ :=
    tryNew_uninit_of_pow2_le_29 (Miri.ABI.Size.ofBytes 8) (translateAlignBytes 4) (by decide)
  have hmask0 : InitMaskWordRel (raw.withExtra extra0).initializationMask
      (raw.withExtra extra0).byteSize (initWordsFalse (raw.withExtra extra0).byteSize) := by
    rw [hmask, hbs]; exact initMaskWordRel_new_false
  have hrel99 : ScalarRel ⟨99, 4⟩ (Miri.Memory.ScalarInt.ofUInt32 99) :=
    ⟨Or.inr (Or.inr (Or.inl rfl)), by rw [scalarModulus_eq_two_pow]; decide, rfl, rfl⟩
  obtain ⟨A', _, hw, _, _, _, _, _, _, hinit1, _, _, hpad⟩ :=
    writeField_preserves_other_fields_and_padding lm22Padded_validStructLayout
      (i := 1) (by decide) hrel99 rfl hbs (hlen.trans (by rw [hbs])) hmut hpmap hmask0
  have hp0 : ∀ q : Nat, q < 8 →
      (raw.withExtra extra0).initializationMask.get (Miri.ABI.Size.ofBytes (UInt64.ofNat q)) =
        .ok false := by
    intro q hq
    rw [hmask]
    exact (initMaskWordRel_get
      (initMaskWordRel_new_false (len := Miri.ABI.Size.ofBytes 8)) hq).trans
      (by simp)
  exact ⟨A', ⟨raw, htry, hw⟩, hinit1,
    (hpad 1 lm22Padded_interfield_padding_bytes.1).trans (hp0 1 (by decide)),
    (hpad 2 lm22Padded_interfield_padding_bytes.2.1).trans (hp0 2 (by decide)),
    (hpad 3 lm22Padded_interfield_padding_bytes.2.2).trans (hp0 3 (by decide))⟩

def lm22PaddedBody : CapturedMir where
  defPath := "lm_2_2_witness::padded_outer"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [lm22U32Decl, lm22PaddedDecl, lm22InnerU32Decl]
  basicBlocks := [
    { statements := [
        mkStmt22 (.storageLive 1),
        mkStmt22 (.storageLive 2),
        mkStmt22 (.assign ⟨2, []⟩
          (.aggregate (.adt "lm22::InnerU32" 0 .none) [.constant (lm22ConstU32 42)])),
        mkStmt22 (.assign ⟨1, []⟩
          (.aggregate (.adt "lm22::PaddedOuter" 0 .none)
            [.constant (constU8 7), .move ⟨2, []⟩])),
        mkStmt22 (.assign ⟨1, [.field 1 lm22InnerU32Ty, .field 0 lm22U32Ty]⟩
          (.use (.constant (lm22ConstU32 99)))),
        mkStmt22 (.assign ⟨0, []⟩
          (.use (.copy ⟨1, [.field 1 lm22InnerU32Ty, .field 0 lm22U32Ty]⟩))),
        mkStmt22 (.storageDead 2),
        mkStmt22 (.storageDead 1)],
      terminator := mkTerm22 .return_,
      isCleanup := false }]
  fnAbi := lm22FnAbiU32
  layouts := lm22PaddedLayoutTable
  allocations := []

def lm22PaddedMiriInit : AnnealStepState :=
  { stack := ⟨#[{
      body := translateBody lm22PaddedBody
      bodyIdentity := .ofCanonicalIndex 0
      functionInstance := { kind := .Item 0, args := #[] }
      extra := ()
      returnContinuation := .stop false
      returnPlace :=
        .frameLocal 0 0 none (translateTy lm22U32Ty lm22PaddedLayoutTable) (.ofAllocationToken 0)
      localsIdentity := .ofAllocationToken 0
      locals := #[
        { value := .live (.immediate .uninit), layout := none },
        { value := .dead, layout := none },
        { value := .dead, layout := none }]
      vaList := #[]
      trackCallerArg := none
      location := .mir ⟨0, 0⟩ }]⟩
    machine := AnnealMachine.empty }

theorem lm22Padded_phase : ∀ p, lm22PaddedBody.phase ≠ .other p := by
  intro p h; cases h

theorem lm22Padded_stateRelLM2_2_init :
    StateRelLM2_2 lm22PaddedBody lm22PaddedEnv { initLocals := [], immLocals := [0] } 3
      (initMachineState lm22PaddedBody []) lm22PaddedMiriInit := by
  refine .mk _ rfl rfl ⟨translateTy lm22U32Ty lm22PaddedLayoutTable, rfl⟩ ?_
    (fun _ h => nomatch h)
    (fun j hj mp l => by simp at hj; subst hj; dsimp [lm22PaddedMiriInit]; nofun)
    (Or.inr (AllocIdWatermark.empty 3 (by decide))) rfl rfl rfl rfl rfl
    (by intro i _ _ _ _ _ _ hi _; revert hi; match i with | 0 | 1 | 2 | _ + 3 => rintro ⟨⟩)
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro i decl slot mls hdecl hslot hmls
  match i with
  | 0 =>
    cases Option.some.inj hdecl
    cases Option.some.inj hslot
    cases Option.some.inj hmls
    exact .base .uninit _ rfl (.immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩))
  | 1 =>
    cases Option.some.inj hdecl
    cases Option.some.inj hslot
    cases Option.some.inj hmls
    exact .structDead lm22PaddedFields lm22PaddedPaths none rfl (fun _ h => nomatch h)
  | 2 =>
    cases Option.some.inj hdecl
    cases Option.some.inj hslot
    cases Option.some.inj hmls
    exact .structDead [lm22InnerU32Field0] [[.field 0 lm22U32Ty]] none rfl (fun _ h => nomatch h)
  | _ + 3 => simp [lm22PaddedBody, get?] at hdecl

theorem lm22Padded_projChain_inner0 :
    ValidFieldProjChain lm22PaddedLayoutTable
      (translateTy lm22PaddedTy lm22PaddedLayoutTable)
      [.field 1 lm22InnerU32Ty, .field 0 lm22U32Ty] lm22U32Ty
      (Miri.ABI.Size.ofBytes 4) := by
  have h : Miri.ABI.Size.ofBytes ((Miri.ABI.Size.ofBytes 4).bytes + Miri.ABI.Size.ZERO.bytes) =
      Miri.ABI.Size.ofBytes 4 := rfl
  rw [← h]
  exact .cons (translateTy lm22PaddedTy lm22PaddedLayoutTable) 1 lm22InnerU32Ty
    [.field 0 lm22U32Ty] lm22U32Ty (Miri.ABI.Size.ofBytes 4) Miri.ABI.Size.ZERO
    (Or.inr (Or.inr ⟨"lm22::InnerU32", [], rfl⟩)) rfl rfl (by decide)
    (.single (translateTy lm22InnerU32Ty lm22PaddedLayoutTable) 0 lm22U32Ty
      Miri.ABI.Size.ZERO (Or.inl lm22_u32_prim) rfl rfl (by decide))

/-- Full lockstep trace for `lm22PaddedBody` (`InnerU32` `.Scalar` wrapper inside
padded `PaddedOuter` `.Memory`), proving:
1. `StructMemPlaceRel` + inter-field alignment padding bytes `1, 2, 3` `.uninit`
   (`InitMask.get = .ok false` + `isRangeInitialized ≠ .ok (.ok ())`) after nested
   write `_1.1.0 = const 99_u32`,
2. `StateRelLM2_2` at step 7 while `_1` (`PaddedOuter`) is live `.indirect` in
   stack memory with padding bytes `1, 2, 3` uninitialized (a state the base
   `StateRel` cannot express), and
3. bounded execution return agreement (`some 99`). -/
theorem lm22Padded_full_trace_and_returns_agree :
    (∃ mp localAlloc,
      StructMemPlaceRel
        (lm22StepMiriN lm22PaddedBody 5 lm22PaddedMiriInit).machine
        lm22PaddedTy lm22PaddedLayoutTable lm22PaddedFields lm22PaddedPaths
        (.aggregate 0 [.scalar ⟨7, 1⟩, .aggregate 0 [.scalar ⟨99, 4⟩]]) mp ∧
      (∃ allocId,
        (∃ tag, mp.ptr.provenance = some (.concrete allocId tag)) ∧
        (lm22StepMiriN lm22PaddedBody 5 lm22PaddedMiriInit).machine.memory.live.find?
          (fun (k, _) => k == allocId) = some (allocId, localAlloc)) ∧
      localAlloc.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 1) = .ok false ∧
      localAlloc.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 2) = .ok false ∧
      localAlloc.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 3) = .ok false ∧
      localAlloc.allocation.initializationMask.isRangeInitialized
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8)) ≠ .ok (.ok ())) ∧
    StateRelLM2_2 lm22PaddedBody lm22PaddedEnv
      { initLocals := [2, 0, 1], immLocals := [2, 0, 2, 0] } 0
      (lm22StepAnnealN lm22PaddedBody 7 (initMachineState lm22PaddedBody []))
      (lm22StepMiriN lm22PaddedBody 7 lm22PaddedMiriInit) ∧
    annealOutcomeScalarBits 4
      (runAnnealBounded lm22PaddedBody 9 (initMachineState lm22PaddedBody [])) = some 99 ∧
    miriOutcomeScalarBits 4
      (runMiriBoundedLM2_2 lm22PaddedBody 9 lm22PaddedMiriInit) = some 99 := by
  have hs0 : StateRelLM2_2 lm22PaddedBody lm22PaddedEnv { initLocals := [], immLocals := [0] } 3
      (lm22StepAnnealN lm22PaddedBody 0 (initMachineState lm22PaddedBody []))
      (lm22StepMiriN lm22PaddedBody 0 lm22PaddedMiriInit) :=
    lm22Padded_stateRelLM2_2_init
  have ⟨hs1, ha0, hm0⟩ := lm22_trace_step ⟨[], [1, 0]⟩ (fuel := 8) hs0
    lm22Padded_phase rfl rfl (.storageLive _ 3 1 lm22PaddedDecl _ rfl) rfl rfl
  have ⟨hs2, ha1, hm1⟩ := lm22_trace_step ⟨[], [2, 1, 0]⟩ (fuel := 7) hs1
    lm22Padded_phase rfl rfl (.storageLive _ 3 2 lm22InnerU32Decl _ rfl) rfl rfl
  have hwt2 : WellTypedLM2_2Stmt lm22PaddedBody lm22PaddedEnv ⟨[], [2, 1, 0]⟩ 3
      (mkStmt22 (.assign ⟨2, []⟩
        (.aggregate (.adt "lm22::InnerU32" 0 .none) [.constant (lm22ConstU32 42)])))
      (aggPostStaticEnv ⟨[], [2, 1, 0]⟩ 2 [.constant (lm22ConstU32 42)]) 2 :=
    .assignAggregate _ 2 2 _ _ _
      (.mk lm22InnerU32Decl [lm22InnerU32Field0] [[.field 0 lm22U32Ty]] _ [] rfl
        (Or.inr ⟨"lm22::InnerU32", rfl⟩) rfl rfl lm22InnerU32_validStructLayout
        (by decide) rfl rfl (by decide)
        (.cons _ 0 0 1 _ [] trivial
          (.primLeaf (by decide) _ (lm22_constU32_wt 42 (by decide) rfl)
            rfl lm22_u32_prim rfl rfl rfl rfl rfl rfl)
          (.nil _ 1)))
  have ⟨hs3, ha2, hm2⟩ := lm22_trace_step ⟨[2], [1, 0]⟩ (fuel := 6) hs2
    lm22Padded_phase rfl rfl hwt2 rfl rfl
  have hwt3 : WellTypedLM2_2Stmt lm22PaddedBody lm22PaddedEnv ⟨[2], [1, 0]⟩ 2
      (mkStmt22 (.assign ⟨1, []⟩
        (.aggregate (.adt "lm22::PaddedOuter" 0 .none)
          [.constant (constU8 7), .move ⟨2, []⟩])))
      (aggPostStaticEnv ⟨[2], [1, 0]⟩ 1 [.constant (constU8 7), .move ⟨2, []⟩]) 1 :=
    .assignAggregate _ 1 1 _ _ _
      (.mk lm22PaddedDecl lm22PaddedFields lm22PaddedPaths _ _ rfl
        (Or.inr ⟨"lm22::PaddedOuter", rfl⟩) rfl rfl lm22Padded_validStructLayout
        (by decide) rfl rfl (by decide)
        (.cons _ 0 0 1 _ _ trivial
          (.primLeaf (by decide) _ (lm22_constU8_wt 7 (by decide) rfl)
            rfl lm22_u8_prim rfl rfl rfl rfl rfl rfl)
          (.cons _ 1 1 2 (.move ⟨2, []⟩) [] (by decide : (2 : Nat) ≠ 1)
            (.scalarWrapSub (by decide) lm22InnerU32Ty lm22InnerU32Field0
              [.field 0 lm22U32Ty] _
              (.immStructLocal true 2 lm22InnerU32Decl [lm22InnerU32Field0]
                [[.field 0 lm22U32Ty]] rfl lm22InnerU32_isImmediateStructTy)
              lm22InnerU32_isImmediateStructTy rfl rfl rfl rfl rfl rfl rfl)
            (.nil _ 2))))
  have ⟨hs4, ha3, hm3⟩ := lm22_trace_step ⟨[1], [2, 0]⟩ (fuel := 5) hs3
    lm22Padded_phase rfl rfl hwt3 rfl rfl
  have hwt4 : WellTypedLM2_2Stmt lm22PaddedBody lm22PaddedEnv ⟨[1], [2, 0]⟩ 1
      (mkStmt22 (.assign ⟨1, [.field 1 lm22InnerU32Ty, .field 0 lm22U32Ty]⟩
        (.use (.constant (lm22ConstU32 99)))))
      (fieldWritePostStaticEnv ⟨[1], [2, 0]⟩ 1 (.constant (lm22ConstU32 99))) 0 :=
    .assignFieldWrite _ 0 1 [.field 1 lm22InnerU32Ty, .field 0 lm22U32Ty]
      (.constant (lm22ConstU32 99)) _
      (.mk lm22PaddedDecl lm22PaddedFields lm22PaddedPaths 1 rfl rfl (by decide)
        rfl (by decide) (by decide) rfl
        (fun j hj hne => by
          match j with
          | 0 => exact .diff_head (by decide)
          | 1 => exact False.elim (hne rfl)
          | _ + 2 => simp [lm22PaddedPaths] at hj; omega)
        lm22Padded_projChain_inner0
        rfl rfl lm22_u32_prim trivial (lm22_constU32_wt 99 (by decide) rfl))
  have ⟨hs5, ha4, hm4⟩ := lm22_trace_step ⟨[1], [2, 0]⟩ (fuel := 4) hs4
    lm22Padded_phase rfl rfl hwt4 rfl rfl
  have hwt5 : WellTypedLM2_2Stmt lm22PaddedBody lm22PaddedEnv ⟨[1], [2, 0]⟩ 0
      (mkStmt22 (.assign ⟨0, []⟩
        (.use (.copy ⟨1, [.field 1 lm22InnerU32Ty, .field 0 lm22U32Ty]⟩))))
      (usePostStaticEnv ⟨[1], [2, 0]⟩ 0
        (.copy ⟨1, [.field 1 lm22InnerU32Ty, .field 0 lm22U32Ty]⟩)) 0 :=
    .assignUse _ 0 0 _ _
      (.mk lm22U32Decl rfl (by decide)
        (.projectedScalar false 1 [.field 1 lm22InnerU32Ty, .field 0 lm22U32Ty]
          lm22U32Ty rfl
          (.mk lm22PaddedDecl lm22PaddedFields lm22PaddedPaths 1 (by decide) (by decide)
            rfl rfl rfl rfl lm22_u32_prim lm22Padded_projChain_inner0)))
  have ⟨hs6, ha5, hm5⟩ := lm22_trace_step ⟨[0, 1], [0, 2, 0]⟩ (fuel := 3) hs5
    lm22Padded_phase rfl rfl hwt5 rfl rfl
  have ⟨hs7, ha6, hm6⟩ := lm22_trace_step ⟨[2, 0, 1], [2, 0, 2, 0]⟩ (fuel := 2) hs6
    lm22Padded_phase rfl rfl (.storageDead _ 0 2 lm22InnerU32Decl _ rfl (by decide)) rfl rfl
  have ⟨hs8, ha7, hm7⟩ := lm22_trace_step ⟨[1, 2, 0, 1], [1, 2, 0, 2, 0]⟩ (fuel := 1) hs7
    lm22Padded_phase rfl rfl (.storageDead _ 0 1 lm22PaddedDecl _ rfl (by decide)) rfl rfl
  have hpad5 :
      ∃ mp localAlloc,
        StructMemPlaceRel
          (lm22StepMiriN lm22PaddedBody 5 lm22PaddedMiriInit).machine
          lm22PaddedTy lm22PaddedLayoutTable lm22PaddedFields lm22PaddedPaths
          (.aggregate 0 [.scalar ⟨7, 1⟩, .aggregate 0 [.scalar ⟨99, 4⟩]]) mp ∧
        (∃ allocId,
          (∃ tag, mp.ptr.provenance = some (.concrete allocId tag)) ∧
          (lm22StepMiriN lm22PaddedBody 5 lm22PaddedMiriInit).machine.memory.live.find?
            (fun (k, _) => k == allocId) = some (allocId, localAlloc)) ∧
        localAlloc.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 1) = .ok false ∧
        localAlloc.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 2) = .ok false ∧
        localAlloc.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 3) = .ok false ∧
        localAlloc.allocation.initializationMask.isRangeInitialized
          (Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8)) ≠ .ok (.ok ()) := by
    rcases lm22_extract_struct_local hs5 (idx := 1) rfl rfl rfl with ⟨_, himm⟩ | ⟨mp, hsmpr⟩
    · exact False.elim (lm22_not_immediateStructRel_of_memory rfl himm)
    · obtain ⟨allocId, localAlloc, hprov, hfind, hpad_fn, hhas_uninit⟩ :=
        hsmpr.has_uninit_of_padding_byte lm22Padded_interfield_padding_bytes.1
      exact ⟨mp, localAlloc, hsmpr, ⟨allocId, hprov, hfind⟩,
        hpad_fn 1 lm22Padded_interfield_padding_bytes.1,
        hpad_fn 2 lm22Padded_interfield_padding_bytes.2.1,
        hpad_fn 3 lm22Padded_interfield_padding_bytes.2.2,
        hhas_uninit⟩
  have hbase8 : StateRel lm22PaddedBody
      (lm22StepAnnealN lm22PaddedBody 8 (initMachineState lm22PaddedBody []))
      (lm22StepMiriN lm22PaddedBody 8 lm22PaddedMiriInit) := by
    refine hs8.toStateRel_of_flat_imm (by rintro ⟨_, _⟩ _ _ h _ _ ⟨⟩; cases h) (fun i _ _ _ _ hdecl henv hslot _ => ?_) ?hunpad
    case hunpad =>
      intro i _ _ _ _ _ _ hdecl henv hslot _
      match i with
      | 0 => cases Option.some.inj hdecl; cases henv
      | 1 =>
        have hdead :
            get? (lm22StepAnnealN lm22PaddedBody 8 (initMachineState lm22PaddedBody [])).frame.locals 1 =
              some .dead := rfl
        rw [hdead] at hslot; cases hslot
      | 2 =>
        have hdead :
            get? (lm22StepAnnealN lm22PaddedBody 8 (initMachineState lm22PaddedBody [])).frame.locals 2 =
              some .dead := rfl
        rw [hdead] at hslot; cases hslot
      | _ + 3 => simp [lm22PaddedBody, get?] at hdecl
    match i with
    | 0 => cases Option.some.inj hdecl; exact False.elim (henv rfl)
    | 1 =>
      have hdead :
          get? (lm22StepAnnealN lm22PaddedBody 8 (initMachineState lm22PaddedBody [])).frame.locals 1 =
            some .dead := rfl
      rw [hdead] at hslot; cases hslot
    | 2 =>
      have hdead :
          get? (lm22StepAnnealN lm22PaddedBody 8 (initMachineState lm22PaddedBody [])).frame.locals 2 =
            some .dead := rfl
      rw [hdead] at hslot; cases hslot
    | _ + 3 => simp [lm22PaddedBody, get?] at hdecl
  have himm0_8 : ∀ tf,
      (lm22StepMiriN lm22PaddedBody 8 lm22PaddedMiriInit).stack.frames = #[tf] →
      IsImmediateFrameLocal tf 0 := by
    intro tf htf mls hmls mp hmp
    rcases hs8 with ⟨tf0, htf0, _, _, _, _, himm_env, _, _, _, _, _, _, _⟩
    cases Array.singleton_inj.mp (htf0.symm.trans htf)
    cases mls with
    | mk val lay => dsimp at hmp; subst hmp; exact himm_env 0 (by decide) mp lay hmls
  obtain ⟨ha_ret, hm_ret⟩ := lm22_return_agree_of_stateRel hbase8 lm22Padded_phase
    rfl rfl rfl rfl rfl rfl lm22_u32_prim himm0_8 rfl
  have ha_tot :
      runAnnealBounded lm22PaddedBody 9 (initMachineState lm22PaddedBody []) =
        runAnnealBounded lm22PaddedBody 1
          (lm22StepAnnealN lm22PaddedBody 8 (initMachineState lm22PaddedBody [])) :=
    ha0.trans (ha1.trans (ha2.trans (ha3.trans (ha4.trans (ha5.trans (ha6.trans ha7))))))
  have hm_tot :
      runMiriBoundedLM2_2 lm22PaddedBody 9 lm22PaddedMiriInit =
        runMiriBoundedLM2_2 lm22PaddedBody 1 (lm22StepMiriN lm22PaddedBody 8 lm22PaddedMiriInit) :=
    hm0.trans (hm1.trans (hm2.trans (hm3.trans (hm4.trans (hm5.trans (hm6.trans hm7))))))
  rw [ha_tot, hm_tot]
  exact ⟨hpad5, hs7, ha_ret, hm_ret⟩


/-! ## 4. 2-Level Nested Struct `NestedOuter { tag: u8, inner: InnerPair { x: u32, y: u16 } }` -/

def lm22InnerPairTy : Ty :=
  { kind := .adt "lm22::InnerPair" [], layoutIdx := 1 }

def lm22InnerPairDecl : LocalDecl :=
  { mutability := .mut, ty := lm22InnerPairTy, debugName := none }

def lm22NestedTy : Ty :=
  { kind := .adt "lm22::NestedOuter" [], layoutIdx := 0 }

def lm22NestedDecl : LocalDecl :=
  { mutability := .mut, ty := lm22NestedTy, debugName := none }

def lm22InnerPairTypeLayout : TypeLayout :=
  { size := { bytes := 8 }
    align := { bytes := 4 }
    backendRepr :=
      .scalarPair
        (.initialized (.int 32 false) { start := 0, end_ := 4294967295 })
        (.initialized (.int 16 false) { start := 0, end_ := 65535 })
    fields := .arbitrary [{ bytes := 0 }, { bytes := 4 }] [0, 1]
    variants := .single 0
    isUninhabited := false
    fieldLayouts := [2, 3] }

def lm22NestedTypeLayout : TypeLayout :=
  { size := { bytes := 12 }
    align := { bytes := 4 }
    backendRepr := .memory
    fields := .arbitrary [{ bytes := 0 }, { bytes := 4 }] [0, 1]
    variants := .single 0
    isUninhabited := false
    fieldLayouts := [4, 1] }

def lm22NestedLayoutTable : LayoutTable :=
  { pointerBits := 64
    isLittleEndian := true
    entries :=
      [lm22NestedTypeLayout, lm22InnerPairTypeLayout,
       lm22U32TypeLayout, lm22U16TypeLayout, lm22U8TypeLayout] }

def lm22InnerPairField0 : StructFieldDesc :=
  { offset := Miri.ABI.Size.ZERO
    ty := lm22U32Ty
    fieldLayout := (translateTy lm22U32Ty lm22NestedLayoutTable).layout }

def lm22InnerPairField1 : StructFieldDesc :=
  { offset := Miri.ABI.Size.ofBytes 4
    ty := u16Ty
    fieldLayout := (translateTy u16Ty lm22NestedLayoutTable).layout }

def lm22InnerPairFields : List StructFieldDesc :=
  [lm22InnerPairField0, lm22InnerPairField1]

def lm22InnerPairPaths : List (List ProjectionElem) :=
  [[.field 0 lm22U32Ty], [.field 1 u16Ty]]

def lm22NestedField0 : StructFieldDesc :=
  { offset := Miri.ABI.Size.ZERO
    ty := u8Ty
    fieldLayout := (translateTy u8Ty lm22NestedLayoutTable).layout }

def lm22NestedField1 : StructFieldDesc :=
  { offset := Miri.ABI.Size.ofBytes 4
    ty := lm22U32Ty
    fieldLayout := (translateTy lm22U32Ty lm22NestedLayoutTable).layout }

def lm22NestedField2 : StructFieldDesc :=
  { offset := Miri.ABI.Size.ofBytes 8
    ty := u16Ty
    fieldLayout := (translateTy u16Ty lm22NestedLayoutTable).layout }

def lm22NestedFields : List StructFieldDesc :=
  [lm22NestedField0, lm22NestedField1, lm22NestedField2]

def lm22NestedPaths : List (List ProjectionElem) :=
  [[.field 0 u8Ty],
   [.field 1 lm22InnerPairTy, .field 0 lm22U32Ty],
   [.field 1 lm22InnerPairTy, .field 1 u16Ty]]

def lm22NestedEnv : StructTypeEnv := fun ty =>
  match ty.kind with
  | .adt "lm22::InnerPair" [] => some (lm22InnerPairFields, lm22InnerPairPaths)
  | .adt "lm22::NestedOuter" [] => some (lm22NestedFields, lm22NestedPaths)
  | _ => none

theorem lm22InnerPair_validStructLayout :
    ValidStructLayout (translateTy lm22InnerPairTy lm22NestedLayoutTable).layout
      lm22InnerPairFields := by
  refine
    { fields_in_bounds := fun i hi => by
        match i with
        | 0 | 1 => decide +revert
        | _ + 2 => simp [lm22InnerPairFields] at hi; omega
      fields_disjoint := fun i j hi hj hne => by
        match i, j with
        | 0, 0 | 1, 1 => exact False.elim (hne rfl)
        | 0, 1 => left; decide +revert
        | 1, 0 => right; decide +revert
        | _ + 2, _ => simp [lm22InnerPairFields] at hi; omega
        | _, _ + 2 => simp [lm22InnerPairFields] at hj; omega
      fields_aligned := fun i hi => by
        match i with
        | 0 | 1 => decide +revert
        | _ + 2 => simp [lm22InnerPairFields] at hi; omega
      fields_shape_valid := Or.inr (ValidStructLayout.arbitrary_flat #[0, 1] rfl (by decide)) }

theorem lm22InnerPair_isImmediateStructTy :
    IsImmediateStructTy lm22NestedEnv lm22NestedLayoutTable lm22InnerPairTy
      lm22InnerPairFields lm22InnerPairPaths :=
  .scalarPair lm22InnerPairField0 lm22InnerPairField1 lm22U32Ty u16Ty [] []
    _ _ (Miri.ABI.Size.ofBytes 4)
    rfl lm22InnerPair_validStructLayout (by decide)
    (Or.inr ⟨"lm22::InnerPair", [], rfl⟩)
    (fun _ h => nomatch h)
    rfl (by decide) (by decide) (by decide) (by decide)
    rfl rfl rfl rfl
    (Or.inl lm22_u32_prim) (Or.inl lm22_u16_prim)
    lm22_u32_prim lm22_u16_prim
    (Or.inl ⟨rfl, rfl⟩) (Or.inl ⟨rfl, rfl⟩)

theorem lm22Nested_validStructLayout :
    ValidStructLayout (translateTy lm22NestedTy lm22NestedLayoutTable).layout
      lm22NestedFields := by
  refine
    { fields_in_bounds := fun i hi => by
        match i with
        | 0 | 1 | 2 => decide +revert
        | _ + 3 => simp [lm22NestedFields] at hi; omega
      fields_disjoint := fun i j hi hj hne => by
        match i, j with
        | 0, 0 | 1, 1 | 2, 2 => exact False.elim (hne rfl)
        | 0, 1 | 0, 2 | 1, 2 => left; decide +revert
        | 1, 0 | 2, 0 | 2, 1 => right; decide +revert
        | _ + 3, _ => simp [lm22NestedFields] at hi; omega
        | _, _ + 3 => simp [lm22NestedFields] at hj; omega
      fields_aligned := fun i hi => by
        match i with
        | 0 | 1 | 2 => decide +revert
        | _ + 3 => simp [lm22NestedFields] at hi; omega
      fields_shape_valid := Or.inr ⟨#[Miri.ABI.Size.ZERO, Miri.ABI.Size.ofBytes 4], #[0, 1],
        rfl, by decide,
        (by
          intro off hoff
          change off ∈ [Miri.ABI.Size.ZERO, Miri.ABI.Size.ofBytes 4] at hoff
          cases hoff with
          | head => exact .head _
          | tail _ h2 =>
            cases h2 with
            | head => exact .tail _ (.head _)
            | tail _ hnil => cases hnil),
        (by
          intro f hf
          cases hf with
          | head => exact ⟨Miri.ABI.Size.ZERO, .head _, by decide⟩
          | tail _ hf2 =>
            cases hf2 with
            | head => exact ⟨Miri.ABI.Size.ofBytes 4, .tail _ (.head _), by decide⟩
            | tail _ hf3 =>
              cases hf3 with
              | head => exact ⟨Miri.ABI.Size.ofBytes 4, .tail _ (.head _), by decide⟩
              | tail _ hnil => cases hnil)⟩ }

theorem lm22Nested_all_five_padding_bytes :
    isStructPaddingByte lm22NestedFields (Miri.ABI.Size.ofBytes 12) 1 ∧
    isStructPaddingByte lm22NestedFields (Miri.ABI.Size.ofBytes 12) 2 ∧
    isStructPaddingByte lm22NestedFields (Miri.ABI.Size.ofBytes 12) 3 ∧
    isStructPaddingByte lm22NestedFields (Miri.ABI.Size.ofBytes 12) 10 ∧
    isStructPaddingByte lm22NestedFields (Miri.ABI.Size.ofBytes 12) 11 := by
  have hp : ∀ b : Nat, b < 12 → (b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 10 ∨ b = 11) →
      isStructPaddingByte lm22NestedFields (Miri.ABI.Size.ofBytes 12) b := by
    intro b hb hcases
    refine ⟨by change b < 12; exact hb, fun f hf => ?_⟩
    rcases hcases with rfl | rfl | rfl | rfl | rfl <;>
      (cases hf with
       | head => right; decide
       | tail _ hf2 =>
         cases hf2 with
         | head => first | (left; decide) | (right; decide)
         | tail _ hf3 =>
           cases hf3 with
           | head => first | (left; decide) | (right; decide)
           | tail _ hnil => cases hnil)
  exact ⟨hp 1 (by decide) (Or.inl rfl),
    hp 2 (by decide) (Or.inr (Or.inl rfl)),
    hp 3 (by decide) (Or.inr (Or.inr (Or.inl rfl))),
    hp 10 (by decide) (Or.inr (Or.inr (Or.inr (Or.inl rfl)))),
    hp 11 (by decide) (Or.inr (Or.inr (Or.inr (Or.inr rfl))))⟩

theorem lm22Nested_projChain_tag :
    ValidFieldProjChain lm22NestedLayoutTable
      (translateTy lm22NestedTy lm22NestedLayoutTable)
      [.field 0 u8Ty] u8Ty Miri.ABI.Size.ZERO :=
  .single (translateTy lm22NestedTy lm22NestedLayoutTable) 0 u8Ty
    Miri.ABI.Size.ZERO (Or.inl lm22_u8_prim) rfl rfl (by decide)

theorem lm22Nested_projChain_inner0 :
    ValidFieldProjChain lm22NestedLayoutTable
      (translateTy lm22NestedTy lm22NestedLayoutTable)
      [.field 1 lm22InnerPairTy, .field 0 lm22U32Ty] lm22U32Ty
      (Miri.ABI.Size.ofBytes 4) := by
  have h : Miri.ABI.Size.ofBytes ((Miri.ABI.Size.ofBytes 4).bytes + Miri.ABI.Size.ZERO.bytes) =
      Miri.ABI.Size.ofBytes 4 := rfl
  rw [← h]
  exact .cons (translateTy lm22NestedTy lm22NestedLayoutTable) 1 lm22InnerPairTy
    [.field 0 lm22U32Ty] lm22U32Ty (Miri.ABI.Size.ofBytes 4) Miri.ABI.Size.ZERO
    (Or.inr (Or.inr ⟨"lm22::InnerPair", [], rfl⟩)) rfl rfl (by decide)
    (.single (translateTy lm22InnerPairTy lm22NestedLayoutTable) 0 lm22U32Ty
      Miri.ABI.Size.ZERO (Or.inl lm22_u32_prim) rfl rfl (by decide))

theorem lm22Nested_projChain_inner1 :
    ValidFieldProjChain lm22NestedLayoutTable
      (translateTy lm22NestedTy lm22NestedLayoutTable)
      [.field 1 lm22InnerPairTy, .field 1 u16Ty] u16Ty
      (Miri.ABI.Size.ofBytes 8) := by
  have h : Miri.ABI.Size.ofBytes
      ((Miri.ABI.Size.ofBytes 4).bytes + (Miri.ABI.Size.ofBytes 4).bytes) =
      Miri.ABI.Size.ofBytes 8 := rfl
  rw [← h]
  exact .cons (translateTy lm22NestedTy lm22NestedLayoutTable) 1 lm22InnerPairTy
    [.field 1 u16Ty] u16Ty (Miri.ABI.Size.ofBytes 4) (Miri.ABI.Size.ofBytes 4)
    (Or.inr (Or.inr ⟨"lm22::InnerPair", [], rfl⟩)) rfl rfl (by decide)
    (.single (translateTy lm22InnerPairTy lm22NestedLayoutTable) 1 u16Ty
      (Miri.ABI.Size.ofBytes 4) (Or.inl lm22_u16_prim) rfl rfl (by decide))

def lm22NestedBody : CapturedMir where
  defPath := "lm_2_2_witness::nested_outer_pair"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u16Decl, lm22InnerPairDecl, lm22NestedDecl, u8Decl, lm22U32Decl]
  basicBlocks := [
    { statements := [
        mkStmt22 (.storageLive 1),
        mkStmt22 (.storageLive 2),
        mkStmt22 (.storageLive 3),
        mkStmt22 (.storageLive 4),
        mkStmt22 (.assign ⟨1, []⟩
          (.aggregate (.adt "lm22::InnerPair" 0 .none)
            [.constant (lm22ConstU32 0x11112222), .constant (constU16 0x3344)])),
        mkStmt22 (.assign ⟨2, []⟩
          (.aggregate (.adt "lm22::NestedOuter" 0 .none)
            [.constant (constU8 7), .move ⟨1, []⟩])),
        mkStmt22 (.assign ⟨2, [.field 1 lm22InnerPairTy, .field 1 u16Ty]⟩
          (.use (.constant (constU16 0xBEEF)))),
        mkStmt22 (.assign ⟨3, []⟩
          (.use (.copy ⟨2, [.field 0 u8Ty]⟩))),
        mkStmt22 (.assign ⟨4, []⟩
          (.use (.copy ⟨2, [.field 1 lm22InnerPairTy, .field 0 lm22U32Ty]⟩))),
        mkStmt22 (.assign ⟨0, []⟩
          (.use (.copy ⟨2, [.field 1 lm22InnerPairTy, .field 1 u16Ty]⟩))),
        mkStmt22 (.storageDead 4),
        mkStmt22 (.storageDead 3),
        mkStmt22 (.storageDead 2),
        mkStmt22 (.storageDead 1)],
      terminator := mkTerm22 .return_,
      isCleanup := false }]
  fnAbi := lm22FnAbiU16
  layouts := lm22NestedLayoutTable
  allocations := []

def lm22NestedMiriInit : AnnealStepState :=
  { stack := ⟨#[{
      body := translateBody lm22NestedBody
      bodyIdentity := .ofCanonicalIndex 0
      functionInstance := { kind := .Item 0, args := #[] }
      extra := ()
      returnContinuation := .stop false
      returnPlace :=
        .frameLocal 0 0 none (translateTy u16Ty lm22NestedLayoutTable) (.ofAllocationToken 0)
      localsIdentity := .ofAllocationToken 0
      locals := #[
        { value := .live (.immediate .uninit), layout := none },
        { value := .dead, layout := none },
        { value := .dead, layout := none },
        { value := .dead, layout := none },
        { value := .dead, layout := none }]
      vaList := #[]
      trackCallerArg := none
      location := .mir ⟨0, 0⟩ }]⟩
    machine := AnnealMachine.empty }

theorem lm22Nested_phase : ∀ p, lm22NestedBody.phase ≠ .other p := by
  intro p h; cases h

theorem lm22Nested_stateRelLM2_2_init :
    StateRelLM2_2 lm22NestedBody lm22NestedEnv { initLocals := [], immLocals := [0] } 3
      (initMachineState lm22NestedBody []) lm22NestedMiriInit := by
  refine .mk _ rfl rfl ⟨translateTy u16Ty lm22NestedLayoutTable, rfl⟩ ?_
    (fun _ h => nomatch h)
    (fun j hj mp l => by simp at hj; subst hj; dsimp [lm22NestedMiriInit]; nofun)
    (Or.inr (AllocIdWatermark.empty 3 (by decide))) rfl rfl rfl rfl rfl
    (by intro i _ _ _ _ _ _ hi _; revert hi
        match i with | 0 | 1 | 2 | 3 | 4 | _ + 5 => rintro ⟨⟩)
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro i decl slot mls hdecl hslot hmls
  match i with
  | 0 =>
    cases Option.some.inj hdecl
    cases Option.some.inj hslot
    cases Option.some.inj hmls
    exact .base .uninit _ rfl (.immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩))
  | 1 =>
    cases Option.some.inj hdecl
    cases Option.some.inj hslot
    cases Option.some.inj hmls
    exact .structDead lm22InnerPairFields lm22InnerPairPaths none rfl (fun _ h => nomatch h)
  | 2 =>
    cases Option.some.inj hdecl
    cases Option.some.inj hslot
    cases Option.some.inj hmls
    exact .structDead lm22NestedFields lm22NestedPaths none rfl (fun _ h => nomatch h)
  | 3 =>
    cases Option.some.inj hdecl
    cases Option.some.inj hslot
    cases Option.some.inj hmls
    exact .base .dead _ rfl (.dead none (fun _ h => nomatch h))
  | 4 =>
    cases Option.some.inj hdecl
    cases Option.some.inj hslot
    cases Option.some.inj hmls
    exact .base .dead _ rfl (.dead none (fun _ h => nomatch h))
  | _ + 5 => simp [lm22NestedBody, get?] at hdecl

theorem lm22Nested_full_trace_and_returns_agree :
    (∃ mp localAlloc,
      StructMemPlaceRel
        (lm22StepMiriN lm22NestedBody 7 lm22NestedMiriInit).machine
        lm22NestedTy lm22NestedLayoutTable lm22NestedFields lm22NestedPaths
        (.aggregate 0 [.scalar ⟨7, 1⟩, .aggregate 0 [.scalar ⟨0x11112222, 4⟩, .scalar ⟨0xBEEF, 2⟩]]) mp ∧
      (∃ allocId,
        (∃ tag, mp.ptr.provenance = some (.concrete allocId tag)) ∧
        (lm22StepMiriN lm22NestedBody 7 lm22NestedMiriInit).machine.memory.live.find?
          (fun (k, _) => k == allocId) = some (allocId, localAlloc)) ∧
      localAlloc.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 1) = .ok false ∧
      localAlloc.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 2) = .ok false ∧
      localAlloc.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 3) = .ok false ∧
      localAlloc.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 10) = .ok false ∧
      localAlloc.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 11) = .ok false ∧
      localAlloc.allocation.initializationMask.isRangeInitialized
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 12)) ≠ .ok (.ok ())) ∧
    StateRelLM2_2 lm22NestedBody lm22NestedEnv
      { initLocals := [0, 4, 3, 2], immLocals := [0, 4, 3, 1, 4, 3, 0] } 0
      (lm22StepAnnealN lm22NestedBody 10 (initMachineState lm22NestedBody []))
      (lm22StepMiriN lm22NestedBody 10 lm22NestedMiriInit) ∧
    get? (lm22StepAnnealN lm22NestedBody 10 (initMachineState lm22NestedBody [])).frame.locals 3 =
      some (.init (.scalar ⟨7, 1⟩)) ∧
    get? (lm22StepAnnealN lm22NestedBody 10 (initMachineState lm22NestedBody [])).frame.locals 4 =
      some (.init (.scalar ⟨0x11112222, 4⟩)) ∧
    annealOutcomeScalarBits 2
      (runAnnealBounded lm22NestedBody 15 (initMachineState lm22NestedBody [])) = some 0xBEEF ∧
    miriOutcomeScalarBits 2
      (runMiriBoundedLM2_2 lm22NestedBody 15 lm22NestedMiriInit) = some 0xBEEF := by
  have hs0 : StateRelLM2_2 lm22NestedBody lm22NestedEnv { initLocals := [], immLocals := [0] } 3
      (lm22StepAnnealN lm22NestedBody 0 (initMachineState lm22NestedBody []))
      (lm22StepMiriN lm22NestedBody 0 lm22NestedMiriInit) :=
    lm22Nested_stateRelLM2_2_init
  have ⟨hs1, ha0, hm0⟩ := lm22_trace_step ⟨[], [1, 0]⟩ (fuel := 14) hs0
    lm22Nested_phase rfl rfl (.storageLive _ 3 1 lm22InnerPairDecl _ rfl) rfl rfl
  have ⟨hs2, ha1, hm1⟩ := lm22_trace_step ⟨[], [2, 1, 0]⟩ (fuel := 13) hs1
    lm22Nested_phase rfl rfl (.storageLive _ 3 2 lm22NestedDecl _ rfl) rfl rfl
  have ⟨hs3, ha2, hm2⟩ := lm22_trace_step ⟨[], [3, 2, 1, 0]⟩ (fuel := 12) hs2
    lm22Nested_phase rfl rfl (.storageLive _ 3 3 u8Decl _ rfl) rfl rfl
  have ⟨hs4, ha3, hm3⟩ := lm22_trace_step ⟨[], [4, 3, 2, 1, 0]⟩ (fuel := 11) hs3
    lm22Nested_phase rfl rfl (.storageLive _ 3 4 lm22U32Decl _ rfl) rfl rfl
  have hwt4 : WellTypedLM2_2Stmt lm22NestedBody lm22NestedEnv ⟨[], [4, 3, 2, 1, 0]⟩ 3
      (mkStmt22 (.assign ⟨1, []⟩
        (.aggregate (.adt "lm22::InnerPair" 0 .none)
          [.constant (lm22ConstU32 0x11112222), .constant (constU16 0x3344)])))
      (aggPostStaticEnv ⟨[], [4, 3, 2, 1, 0]⟩ 1
        [.constant (lm22ConstU32 0x11112222), .constant (constU16 0x3344)]) 2 :=
    .assignAggregate _ 2 1 _ _ _
      (.mk lm22InnerPairDecl lm22InnerPairFields lm22InnerPairPaths _ _ rfl
        (Or.inr ⟨"lm22::InnerPair", rfl⟩) rfl rfl lm22InnerPair_validStructLayout
        (by decide) rfl rfl (by decide)
        (.cons _ 0 0 1 _ _ trivial
          (.primLeaf (by decide) _ (lm22_constU32_wt 0x11112222 (by decide) rfl)
            rfl lm22_u32_prim rfl rfl rfl rfl rfl rfl)
          (.cons _ 1 1 2 _ [] trivial
            (.primLeaf (by decide) _ (lm22_constU16_wt 0x3344 (by decide) rfl)
              rfl lm22_u16_prim rfl rfl rfl rfl rfl rfl)
            (.nil _ 2))))
  have ⟨hs5, ha4, hm4⟩ := lm22_trace_step ⟨[1], [4, 3, 2, 0]⟩ (fuel := 10) hs4
    lm22Nested_phase rfl rfl hwt4 rfl rfl
  have hwt5 : WellTypedLM2_2Stmt lm22NestedBody lm22NestedEnv ⟨[1], [4, 3, 2, 0]⟩ 2
      (mkStmt22 (.assign ⟨2, []⟩
        (.aggregate (.adt "lm22::NestedOuter" 0 .none)
          [.constant (constU8 7), .move ⟨1, []⟩])))
      (aggPostStaticEnv ⟨[1], [4, 3, 2, 0]⟩ 2 [.constant (constU8 7), .move ⟨1, []⟩]) 1 :=
    .assignAggregate _ 1 2 _ _ _
      (.mk lm22NestedDecl lm22NestedFields lm22NestedPaths _ _ rfl
        (Or.inr ⟨"lm22::NestedOuter", rfl⟩) rfl rfl lm22Nested_validStructLayout
        (by decide) rfl rfl (by decide)
        (.cons _ 0 0 1 _ _ trivial
          (.primLeaf (by decide) _ (lm22_constU8_wt 7 (by decide) rfl)
            rfl lm22_u8_prim rfl rfl rfl rfl rfl rfl)
          (.cons _ 1 1 3 (.move ⟨1, []⟩) [] (by decide : (1 : Nat) ≠ 2)
            (.scalarPairSub (by decide) lm22InnerPairTy lm22InnerPairField0 lm22InnerPairField1
              lm22U32Ty u16Ty [] [] _ _ _ (Miri.ABI.Size.ofBytes 4)
              (.immStructLocal true 1 lm22InnerPairDecl lm22InnerPairFields
                lm22InnerPairPaths rfl lm22InnerPair_isImmediateStructTy)
              lm22InnerPair_isImmediateStructTy
              rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide))
            (.nil _ 2))))
  have hwt6 : ∀ stMid, stMid = aggPostStaticEnv ⟨[1], [4, 3, 2, 0]⟩ 2
        [.constant (constU8 7), .move ⟨1, []⟩] →
      WellTypedLM2_2Stmt lm22NestedBody lm22NestedEnv stMid 1
        (mkStmt22 (.assign ⟨2, [.field 1 lm22InnerPairTy, .field 1 u16Ty]⟩
          (.use (.constant (constU16 0xBEEF)))))
        (fieldWritePostStaticEnv stMid 2 (.constant (constU16 0xBEEF))) 0 := by
    intro stMid hst; subst hst
    exact .assignFieldWrite _ 0 2 [.field 1 lm22InnerPairTy, .field 1 u16Ty]
      (.constant (constU16 0xBEEF)) _
      (.mk lm22NestedDecl lm22NestedFields lm22NestedPaths 2 rfl rfl (by decide)
        rfl (by decide) (by decide) rfl
        (fun j hj hne => by
          match j with
          | 0 => exact .diff_head (by decide)
          | 1 => exact .same_head (.diff_head (by decide))
          | 2 => exact False.elim (hne rfl)
          | _ + 3 => simp [lm22NestedPaths] at hj; omega)
        lm22Nested_projChain_inner1
        rfl rfl lm22_u16_prim trivial (lm22_constU16_wt 0xBEEF (by decide) rfl))
  have htwo_5_6 := step_two_stmts_lm2_2_simulation hs5 lm22Nested_phase rfl rfl rfl
    hwt5 (hwt6 _ rfl)
  rcases htwo_5_6 with ⟨hub5, _⟩ | ⟨_, _, _, _, _, _⟩
  · cases hub5
  · have ⟨hs6, ha5, hm5⟩ := lm22_trace_step ⟨[2], [1, 4, 3, 0]⟩ (fuel := 9) hs5
      lm22Nested_phase rfl rfl hwt5 rfl rfl
    have ⟨hs7, ha6, hm6⟩ := lm22_trace_step ⟨[2], [1, 4, 3, 0]⟩ (fuel := 8) hs6
      lm22Nested_phase rfl rfl (hwt6 _ rfl) rfl rfl
    have hwt7 : WellTypedLM2_2Stmt lm22NestedBody lm22NestedEnv ⟨[2], [1, 4, 3, 0]⟩ 0
        (mkStmt22 (.assign ⟨3, []⟩ (.use (.copy ⟨2, [.field 0 u8Ty]⟩))))
        (usePostStaticEnv ⟨[2], [1, 4, 3, 0]⟩ 3 (.copy ⟨2, [.field 0 u8Ty]⟩)) 0 :=
      .assignUse _ 0 3 _ _
        (.mk u8Decl rfl (by decide)
          (.projectedScalar false 2 [.field 0 u8Ty] u8Ty rfl
            (.mk lm22NestedDecl lm22NestedFields lm22NestedPaths 0 (by decide) (by decide)
              rfl rfl rfl rfl lm22_u8_prim lm22Nested_projChain_tag)))
    have ⟨hs8, ha7, hm7⟩ := lm22_trace_step ⟨[3, 2], [3, 1, 4, 3, 0]⟩ (fuel := 7) hs7
      lm22Nested_phase rfl rfl hwt7 rfl rfl
    have hwt8 : WellTypedLM2_2Stmt lm22NestedBody lm22NestedEnv ⟨[3, 2], [3, 1, 4, 3, 0]⟩ 0
        (mkStmt22 (.assign ⟨4, []⟩
          (.use (.copy ⟨2, [.field 1 lm22InnerPairTy, .field 0 lm22U32Ty]⟩))))
        (usePostStaticEnv ⟨[3, 2], [3, 1, 4, 3, 0]⟩ 4
          (.copy ⟨2, [.field 1 lm22InnerPairTy, .field 0 lm22U32Ty]⟩)) 0 :=
      .assignUse _ 0 4 _ _
        (.mk lm22U32Decl rfl (by decide)
          (.projectedScalar false 2 [.field 1 lm22InnerPairTy, .field 0 lm22U32Ty]
            lm22U32Ty rfl
            (.mk lm22NestedDecl lm22NestedFields lm22NestedPaths 1 (by decide) (by decide)
              rfl rfl rfl rfl lm22_u32_prim lm22Nested_projChain_inner0)))
    have ⟨hs9, ha8, hm8⟩ := lm22_trace_step ⟨[4, 3, 2], [4, 3, 1, 4, 3, 0]⟩ (fuel := 6) hs8
      lm22Nested_phase rfl rfl hwt8 rfl rfl
    have hwt9 : WellTypedLM2_2Stmt lm22NestedBody lm22NestedEnv ⟨[4, 3, 2], [4, 3, 1, 4, 3, 0]⟩ 0
        (mkStmt22 (.assign ⟨0, []⟩
          (.use (.copy ⟨2, [.field 1 lm22InnerPairTy, .field 1 u16Ty]⟩))))
        (usePostStaticEnv ⟨[4, 3, 2], [4, 3, 1, 4, 3, 0]⟩ 0
          (.copy ⟨2, [.field 1 lm22InnerPairTy, .field 1 u16Ty]⟩)) 0 :=
      .assignUse _ 0 0 _ _
        (.mk u16Decl rfl (by decide)
          (.projectedScalar false 2 [.field 1 lm22InnerPairTy, .field 1 u16Ty]
            u16Ty rfl
            (.mk lm22NestedDecl lm22NestedFields lm22NestedPaths 2 (by decide) (by decide)
              rfl rfl rfl rfl lm22_u16_prim lm22Nested_projChain_inner1)))
    have ⟨hs10, ha9, hm9⟩ := lm22_trace_step ⟨[0, 4, 3, 2], [0, 4, 3, 1, 4, 3, 0]⟩ (fuel := 5) hs9
      lm22Nested_phase rfl rfl hwt9 rfl rfl
    have ⟨hs11, ha10, hm10⟩ := lm22_trace_step ⟨[4, 0, 4, 3, 2], [4, 0, 4, 3, 1, 4, 3, 0]⟩ (fuel := 4) hs10
      lm22Nested_phase rfl rfl (.storageDead _ 0 4 lm22U32Decl _ rfl (by decide)) rfl rfl
    have ⟨hs12, ha11, hm11⟩ := lm22_trace_step ⟨[3, 4, 0, 4, 3, 2], [3, 4, 0, 4, 3, 1, 4, 3, 0]⟩ (fuel := 3) hs11
      lm22Nested_phase rfl rfl (.storageDead _ 0 3 u8Decl _ rfl (by decide)) rfl rfl
    have ⟨hs13, ha12, hm12⟩ := lm22_trace_step ⟨[2, 3, 4, 0, 4, 3, 2], [2, 3, 4, 0, 4, 3, 1, 4, 3, 0]⟩ (fuel := 2) hs12
      lm22Nested_phase rfl rfl (.storageDead _ 0 2 lm22NestedDecl _ rfl (by decide)) rfl rfl
    have ⟨hs14, ha13, hm13⟩ := lm22_trace_step ⟨[1, 2, 3, 4, 0, 4, 3, 2], [1, 2, 3, 4, 0, 4, 3, 1, 4, 3, 0]⟩ (fuel := 1) hs13
      lm22Nested_phase rfl rfl (.storageDead _ 0 1 lm22InnerPairDecl _ rfl (by decide)) rfl rfl
    rw [show (((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1 = 14 from rfl] at hs14
    have hpad7 :
        ∃ mp localAlloc,
          StructMemPlaceRel
            (lm22StepMiriN lm22NestedBody 7 lm22NestedMiriInit).machine
            lm22NestedTy lm22NestedLayoutTable lm22NestedFields lm22NestedPaths
            (.aggregate 0 [.scalar ⟨7, 1⟩, .aggregate 0 [.scalar ⟨0x11112222, 4⟩, .scalar ⟨0xBEEF, 2⟩]]) mp ∧
          (∃ allocId,
            (∃ tag, mp.ptr.provenance = some (.concrete allocId tag)) ∧
            (lm22StepMiriN lm22NestedBody 7 lm22NestedMiriInit).machine.memory.live.find?
              (fun (k, _) => k == allocId) = some (allocId, localAlloc)) ∧
          localAlloc.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 1) = .ok false ∧
          localAlloc.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 2) = .ok false ∧
          localAlloc.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 3) = .ok false ∧
          localAlloc.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 10) = .ok false ∧
          localAlloc.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 11) = .ok false ∧
          localAlloc.allocation.initializationMask.isRangeInitialized
            (Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 12)) ≠ .ok (.ok ()) := by
      rcases lm22_extract_struct_local hs7 (idx := 2) rfl rfl rfl with ⟨_, himm⟩ | ⟨mp, hsmpr⟩
      · exact False.elim (lm22_not_immediateStructRel_of_memory rfl himm)
      · obtain ⟨p1, p2, p3, p10, p11⟩ := lm22Nested_all_five_padding_bytes
        obtain ⟨allocId, localAlloc, hprov, hfind, hpad_fn, hhas_uninit⟩ :=
          hsmpr.has_uninit_of_padding_byte p1
        exact ⟨mp, localAlloc, hsmpr, ⟨allocId, hprov, hfind⟩,
          hpad_fn 1 p1, hpad_fn 2 p2, hpad_fn 3 p3, hpad_fn 10 p10, hpad_fn 11 p11, hhas_uninit⟩
    have hbase14 : StateRel lm22NestedBody
        (lm22StepAnnealN lm22NestedBody 14 (initMachineState lm22NestedBody []))
        (lm22StepMiriN lm22NestedBody 14 lm22NestedMiriInit) := by
      refine hs14.toStateRel_of_flat_imm (by rintro ⟨_, _⟩ _ _ h _ _ ⟨⟩; cases h) (fun i _ _ _ _ hdecl henv hslot _ => ?_) ?hunpad
      case hunpad =>
        intro i _ _ _ _ _ _ hdecl henv hslot _
        match i with
        | 0 | 3 | 4 => cases Option.some.inj hdecl; cases henv
        | 1 =>
          have hd1 :
              get? (lm22StepAnnealN lm22NestedBody 14 (initMachineState lm22NestedBody [])).frame.locals 1 =
                some .dead := rfl
          rw [hd1] at hslot; cases hslot
        | 2 =>
          have hd2 :
              get? (lm22StepAnnealN lm22NestedBody 14 (initMachineState lm22NestedBody [])).frame.locals 2 =
                some .dead := rfl
          rw [hd2] at hslot; cases hslot
        | _ + 5 => simp [lm22NestedBody, get?] at hdecl
      match i with
      | 0 => cases Option.some.inj hdecl; exact False.elim (henv rfl)
      | 1 =>
        have hd1 :
            get? (lm22StepAnnealN lm22NestedBody 14 (initMachineState lm22NestedBody [])).frame.locals 1 =
              some .dead := rfl
        rw [hd1] at hslot; cases hslot
      | 2 =>
        have hd2 :
            get? (lm22StepAnnealN lm22NestedBody 14 (initMachineState lm22NestedBody [])).frame.locals 2 =
              some .dead := rfl
        rw [hd2] at hslot; cases hslot
      | 3 | 4 => cases Option.some.inj hdecl; exact False.elim (henv rfl)
      | _ + 5 => simp [lm22NestedBody, get?] at hdecl
    have himm0_14 := lm22_imm_of_mem_immLocals hs14 (idx := 0) (by decide)
    obtain ⟨ha_ret, hm_ret⟩ := lm22_return_agree_of_stateRel hbase14 lm22Nested_phase
      rfl rfl rfl rfl rfl rfl lm22_u16_prim himm0_14 rfl
    have ha_tot :
        runAnnealBounded lm22NestedBody 15 (initMachineState lm22NestedBody []) =
          runAnnealBounded lm22NestedBody 1
            (lm22StepAnnealN lm22NestedBody 14 (initMachineState lm22NestedBody [])) :=
      ha0.trans (ha1.trans (ha2.trans (ha3.trans (ha4.trans (ha5.trans (ha6.trans
        (ha7.trans (ha8.trans (ha9.trans (ha10.trans (ha11.trans (ha12.trans ha13))))))))))))
    have hm_tot :
        runMiriBoundedLM2_2 lm22NestedBody 15 lm22NestedMiriInit =
          runMiriBoundedLM2_2 lm22NestedBody 1 (lm22StepMiriN lm22NestedBody 14 lm22NestedMiriInit) :=
      hm0.trans (hm1.trans (hm2.trans (hm3.trans (hm4.trans (hm5.trans (hm6.trans
        (hm7.trans (hm8.trans (hm9.trans (hm10.trans (hm11.trans (hm12.trans hm13))))))))))))
    rw [ha_tot, hm_tot]
    exact ⟨hpad7, hs10, rfl, rfl, ha_ret, hm_ret⟩

/-! ## 5. Whole-Value Reassignment of a Memory-Backed `ScalarPair` Struct (`lm22ReassignBody`)

`_1 = (a, b)` followed by `_1.0 = c` leaves `_1` in a stack allocation (upstream
`forceAllocation`). The later whole-value assignment `_1 = copy _2` must then
write through `_1`'s `MemPlace`, as upstream `writePlaceImmediateNoValidate`
does; before `annealWriteImmediateLM2_2` routed unprojected `.indirect` writes through
memory this statement failed closed with `StepError.unsupported`. -/

/-- `Runtime(PostCleanup)` MIR constructing two `(u32, u16)` tuples, forcing `_1`
into memory with a field write, overwriting the whole memory-backed `_1` with
`_1 = copy _2`, and reading both fields of `_1` back. -/
def lm22ReassignBody : CapturedMir where
  defPath := "lm_2_2_witness::reassign_memory_pair"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [lm22U32Decl, lm22PairDecl, lm22PairDecl, u16Decl]
  basicBlocks := [
    { statements := [
        mkStmt22 (.storageLive 1),
        mkStmt22 (.storageLive 2),
        mkStmt22 (.storageLive 3),
        mkStmt22 (.assign ⟨1, []⟩
          (.aggregate .tuple
            [.constant (lm22ConstU32 0x11223344), .constant (constU16 0x5566)])),
        mkStmt22 (.assign ⟨2, []⟩
          (.aggregate .tuple
            [.constant (lm22ConstU32 0xAABBCCDD), .constant (constU16 0x7788)])),
        mkStmt22 (.assign ⟨1, [.field 0 lm22U32Ty]⟩
          (.use (.constant (lm22ConstU32 0x01020304)))),
        mkStmt22 (.assign ⟨1, []⟩ (.use (.copy ⟨2, []⟩))),
        mkStmt22 (.assign ⟨3, []⟩ (.use (.copy ⟨1, [.field 1 u16Ty]⟩))),
        mkStmt22 (.assign ⟨0, []⟩ (.use (.copy ⟨1, [.field 0 lm22U32Ty]⟩))),
        mkStmt22 (.storageDead 3),
        mkStmt22 (.storageDead 2),
        mkStmt22 (.storageDead 1)],
      terminator := mkTerm22 .return_,
      isCleanup := false }]
  fnAbi := lm22FnAbiU32
  layouts := lm22PairLayoutTable
  allocations := []

def lm22ReassignMiriInit : AnnealStepState :=
  { stack := ⟨#[
      { body := translateBody lm22ReassignBody
        bodyIdentity := .ofCanonicalIndex 0
        functionInstance := { kind := .Item 0, args := #[] }
        extra := ()
        returnContinuation := .stop false
        returnPlace :=
          .frameLocal 0 0 none (translateTy lm22U32Ty lm22PairLayoutTable) (.ofAllocationToken 0)
        localsIdentity := .ofAllocationToken 0
        locals := #[
          { value := .live (.immediate .uninit), layout := none },
          { value := .dead, layout := none },
          { value := .dead, layout := none },
          { value := .dead, layout := none }]
        vaList := #[]
        trackCallerArg := none
        location := .mir ⟨0, 0⟩ }]⟩
    machine := AnnealMachine.empty }

theorem lm22Reassign_phase : ∀ p, lm22ReassignBody.phase ≠ .other p := by
  intro p h; cases h

theorem lm22Reassign_stateRelLM2_2_init :
    StateRelLM2_2 lm22ReassignBody lm22PairEnv { initLocals := [], immLocals := [0] } 3
      (initMachineState lm22ReassignBody []) lm22ReassignMiriInit := by
  refine .mk _ rfl rfl ⟨translateTy lm22U32Ty lm22PairLayoutTable, rfl⟩ ?_
    (fun _ h => nomatch h)
    (fun j hj mp l => by simp at hj; subst hj; dsimp [lm22ReassignMiriInit]; nofun)
    (Or.inr (AllocIdWatermark.empty 3 (by decide))) rfl rfl rfl rfl rfl
    (by intro i _ _ _ _ _ _ hi _; revert hi
        match i with | 0 | 1 | 2 | 3 | _ + 4 => rintro ⟨⟩)
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro i decl slot mls hdecl hslot hmls
  match i with
  | 0 =>
    cases Option.some.inj hdecl
    cases Option.some.inj hslot
    cases Option.some.inj hmls
    exact .base .uninit _ rfl (.immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩))
  | 1 | 2 =>
    cases Option.some.inj hdecl
    cases Option.some.inj hslot
    cases Option.some.inj hmls
    exact .structDead lm22PairFields lm22PairPaths none rfl (fun _ h => nomatch h)
  | 3 =>
    cases Option.some.inj hdecl
    cases Option.some.inj hslot
    cases Option.some.inj hmls
    exact .base .dead _ rfl (.dead none (fun _ h => nomatch h))
  | _ + 4 => simp [lm22ReassignBody, get?] at hdecl

theorem lm22Reassign_isImmediateStructTy :
    IsImmediateStructTy lm22PairEnv lm22ReassignBody.layouts lm22PairTy
      lm22PairFields lm22PairPaths :=
  lm22Pair_isImmediateStructTy

theorem lm22Reassign_agg_wt (stEnv : LM2_2StaticEnv) (k dst a b : Nat)
    (hdst : get? lm22ReassignBody.localDecls dst = some lm22PairDecl)
    (ha : a < 4294967296) (hb : b < 65536) :
    WellTypedLM2_2Stmt lm22ReassignBody lm22PairEnv stEnv (k + 1)
      (mkStmt22 (.assign ⟨dst, []⟩
        (.aggregate .tuple [.constant (lm22ConstU32 a), .constant (constU16 b)])))
      (aggPostStaticEnv stEnv dst [.constant (lm22ConstU32 a), .constant (constU16 b)]) k :=
  .assignAggregate stEnv k dst .tuple _ _
    (.mk lm22PairDecl lm22PairFields lm22PairPaths _ _ rfl (Or.inl rfl) hdst rfl
      lm22Pair_validStructLayout (by decide) rfl rfl (by decide)
      (.cons stEnv 0 0 1 _ _ trivial
        (.primLeaf (by decide) _ (lm22_constU32_wt a ha rfl)
          rfl lm22_u32_prim rfl rfl rfl rfl rfl rfl)
        (.cons _ 1 1 2 _ [] trivial
          (.primLeaf (by decide) _ (lm22_constU16_wt b hb rfl)
            rfl lm22_u16_prim rfl rfl rfl rfl rfl rfl)
          (.nil _ 2))))

theorem lm22Reassign_fw (stEnv : LM2_2StaticEnv) (h1_init : 1 ∈ stEnv.initLocals) :
    WellTypedLM2_2FieldWrite lm22ReassignBody lm22PairEnv stEnv
      1 [.field 0 lm22U32Ty] (.constant (lm22ConstU32 0x01020304)) :=
  .mk lm22PairDecl lm22PairFields lm22PairPaths 0 rfl rfl h1_init rfl (by decide)
    (by decide) rfl
    (fun j hj hne => by
      match j with
      | 0 => exact False.elim (hne rfl)
      | 1 => exact .diff_head (by decide)
      | _ + 2 => simp [lm22PairPaths] at hj; omega)
    (.single (translateTy lm22PairTy lm22PairLayoutTable) 0 lm22U32Ty
      Miri.ABI.Size.ZERO (Or.inl lm22_u32_prim) rfl rfl (by decide))
    rfl rfl lm22_u32_prim trivial (lm22_constU32_wt 0x01020304 (by decide) rfl)

theorem lm22Reassign_fw_wt (stEnv : LM2_2StaticEnv) (k : Nat) (h1_init : 1 ∈ stEnv.initLocals) :
    WellTypedLM2_2Stmt lm22ReassignBody lm22PairEnv stEnv (k + 1)
      (mkStmt22 (.assign ⟨1, [.field 0 lm22U32Ty]⟩
        (.use (.constant (lm22ConstU32 0x01020304)))))
      (fieldWritePostStaticEnv stEnv 1 (.constant (lm22ConstU32 0x01020304))) k :=
  .assignFieldWrite stEnv k 1 [.field 0 lm22U32Ty] (.constant (lm22ConstU32 0x01020304)) _
    (lm22Reassign_fw stEnv h1_init)

/-- `_1 = copy _2` is typed by `WellTypedLM2_2UseAssignStruct`, which places no
requirement on how `_1` is currently stored. -/
theorem lm22Reassign_useStruct_wt (stEnv : LM2_2StaticEnv) (k : Nat) :
    WellTypedLM2_2Stmt lm22ReassignBody lm22PairEnv stEnv k
      (mkStmt22 (.assign ⟨1, []⟩ (.use (.copy ⟨2, []⟩))))
      (useStructPostStaticEnv stEnv 1 (.copy ⟨2, []⟩)) k :=
  .assignUseStruct stEnv k 1 (.copy ⟨2, []⟩) _
    (.mk lm22PairDecl lm22PairFields lm22PairPaths rfl lm22Reassign_isImmediateStructTy
      (.immStructLocal false 2 lm22PairDecl lm22PairFields lm22PairPaths rfl
        lm22Reassign_isImmediateStructTy))

theorem lm22Reassign_read1_wt (stEnv : LM2_2StaticEnv) (k : Nat)
    (h3_imm : 3 ∈ stEnv.immLocals) :
    WellTypedLM2_2Stmt lm22ReassignBody lm22PairEnv stEnv k
      (mkStmt22 (.assign ⟨3, []⟩ (.use (.copy ⟨1, [.field 1 u16Ty]⟩))))
      (usePostStaticEnv stEnv 3 (.copy ⟨1, [.field 1 u16Ty]⟩)) k :=
  .assignUse stEnv k 3 (.copy ⟨1, [.field 1 u16Ty]⟩) _
    (.mk u16Decl rfl h3_imm
      (.projectedScalar false 1 [.field 1 u16Ty] u16Ty rfl
        (.mk lm22PairDecl lm22PairFields lm22PairPaths 1 (by decide) (by decide)
          rfl rfl rfl rfl lm22_u16_prim
          (.single (translateTy lm22PairTy lm22PairLayoutTable) 1 u16Ty
            (Miri.ABI.Size.ofBytes 4) (Or.inl lm22_u16_prim) rfl rfl
            (by decide)))))

theorem lm22Reassign_read0_wt (stEnv : LM2_2StaticEnv) (k : Nat)
    (h0_imm : 0 ∈ stEnv.immLocals) :
    WellTypedLM2_2Stmt lm22ReassignBody lm22PairEnv stEnv k
      (mkStmt22 (.assign ⟨0, []⟩ (.use (.copy ⟨1, [.field 0 lm22U32Ty]⟩))))
      (usePostStaticEnv stEnv 0 (.copy ⟨1, [.field 0 lm22U32Ty]⟩)) k :=
  .assignUse stEnv k 0 (.copy ⟨1, [.field 0 lm22U32Ty]⟩) _
    (.mk lm22U32Decl rfl h0_imm
      (.projectedScalar false 1 [.field 0 lm22U32Ty] lm22U32Ty rfl
        (.mk lm22PairDecl lm22PairFields lm22PairPaths 0 (by decide) (by decide)
          rfl rfl rfl rfl lm22_u32_prim
          (.single (translateTy lm22PairTy lm22PairLayoutTable) 0 lm22U32Ty
            Miri.ABI.Size.ZERO (Or.inl lm22_u32_prim) rfl rfl (by decide)))))

/-- Lockstep trace across `lm22ReassignBody`:
1. right before `_1 = copy _2`, the `lean-miri` local `_1` is `.live (.indirect mp)`
   (memory-backed, from the strengthened
   `step_assign_nested_field_write_post_structMemPlaceRel`) and `mp` holds
   `(0x01020304, 0x5566)` under `StructMemPlaceRel`;
2. `step_assign_use_struct_lm2_2_simulation` steps `_1 = copy _2` in lockstep,
   after which Anneal's `_1` is `(0xAABBCCDD, 0x7788)`;
3. both fields read back from `_1` agree (`_3 = 0x7788_u16`, return value
   `0xAABBCCDD_u32` on both sides). -/
theorem lm22Reassign_full_trace_and_returns_agree :
    (∃ tf mp lay,
      (lm22StepMiriN lm22ReassignBody 6 lm22ReassignMiriInit).stack.frames = #[tf] ∧
      tf.locals[1]? = some ⟨.live (.indirect mp), lay⟩ ∧
      StructMemPlaceRel (lm22StepMiriN lm22ReassignBody 6 lm22ReassignMiriInit).machine
        lm22PairTy lm22PairLayoutTable lm22PairFields lm22PairPaths
        (.aggregate 0 [.scalar ⟨0x01020304, 4⟩, .scalar ⟨0x5566, 2⟩]) mp) ∧
    get? (lm22StepAnnealN lm22ReassignBody 7 (initMachineState lm22ReassignBody [])).frame.locals 1 =
      some (.init (.aggregate 0 [.scalar ⟨0xAABBCCDD, 4⟩, .scalar ⟨0x7788, 2⟩])) ∧
    StateRelLM2_2 lm22ReassignBody lm22PairEnv
      { initLocals := [1, 2, 1], immLocals := [3, 0] } 0
      (lm22StepAnnealN lm22ReassignBody 7 (initMachineState lm22ReassignBody []))
      (lm22StepMiriN lm22ReassignBody 7 lm22ReassignMiriInit) ∧
    get? (lm22StepAnnealN lm22ReassignBody 9 (initMachineState lm22ReassignBody [])).frame.locals 3 =
      some (.init (.scalar ⟨0x7788, 2⟩)) ∧
    annealOutcomeScalarBits 4
      (runAnnealBounded lm22ReassignBody 13 (initMachineState lm22ReassignBody [])) =
        some 0xAABBCCDD ∧
    miriOutcomeScalarBits 4
      (runMiriBoundedLM2_2 lm22ReassignBody 13 lm22ReassignMiriInit) = some 0xAABBCCDD := by
  have hs0 : StateRelLM2_2 lm22ReassignBody lm22PairEnv { initLocals := [], immLocals := [0] } 3
      (lm22StepAnnealN lm22ReassignBody 0 (initMachineState lm22ReassignBody []))
      (lm22StepMiriN lm22ReassignBody 0 lm22ReassignMiriInit) :=
    lm22Reassign_stateRelLM2_2_init
  have ⟨hs1, ha0, hm0⟩ := lm22_trace_step ⟨[], [1, 0]⟩ (fuel := 12) hs0
    lm22Reassign_phase rfl rfl (.storageLive _ 3 1 lm22PairDecl _ rfl) rfl rfl
  have ⟨hs2, ha1, hm1⟩ := lm22_trace_step ⟨[], [2, 1, 0]⟩ (fuel := 11) hs1
    lm22Reassign_phase rfl rfl (.storageLive _ 3 2 lm22PairDecl _ rfl) rfl rfl
  have ⟨hs3, ha2, hm2⟩ := lm22_trace_step ⟨[], [3, 2, 1, 0]⟩ (fuel := 10) hs2
    lm22Reassign_phase rfl rfl (.storageLive _ 3 3 u16Decl _ rfl) rfl rfl
  have ⟨hs4, ha3, hm3⟩ := lm22_trace_step ⟨[1], [3, 2, 0]⟩ (fuel := 9) hs3
    lm22Reassign_phase rfl rfl
    (lm22Reassign_agg_wt _ 2 1 0x11223344 0x5566 rfl (by decide) (by decide)) rfl rfl
  have ⟨hs5, ha4, hm4⟩ := lm22_trace_step ⟨[2, 1], [3, 0]⟩ (fuel := 8) hs4
    lm22Reassign_phase rfl rfl
    (lm22Reassign_agg_wt _ 1 2 0xAABBCCDD 0x7788 rfl (by decide) (by decide)) rfl rfl
  have hmem6 :
      ∃ tf mp lay,
        (lm22StepMiriN lm22ReassignBody 6 lm22ReassignMiriInit).stack.frames = #[tf] ∧
        tf.locals[1]? = some ⟨.live (.indirect mp), lay⟩ ∧
        StructMemPlaceRel (lm22StepMiriN lm22ReassignBody 6 lm22ReassignMiriInit).machine
          lm22PairTy lm22PairLayoutTable lm22PairFields lm22PairPaths
          (.aggregate 0 [.scalar ⟨0x01020304, 4⟩, .scalar ⟨0x5566, 2⟩]) mp := by
    obtain ⟨decl6, fs6, ps6, rv6, mp6, hd6, he6, hsl6, hsmpr6, tf6, lay6, htf6, hloc6⟩ :=
      step_assign_nested_field_write_post_structMemPlaceRel hs5 lm22Reassign_phase rfl rfl
        (lm22Reassign_fw _ (by decide))
        (stepMirFn_eq_step_lm22StepAnnealN lm22ReassignBody 5
          (initMachineState lm22ReassignBody []) rfl)
    cases Option.some.inj hd6
    rcases Prod.mk.inj (Option.some.inj he6) with ⟨rfl, rfl⟩
    have hrv_eq : rv6 = .aggregate 0 [.scalar ⟨0x01020304, 4⟩, .scalar ⟨0x5566, 2⟩] := by
      have hr : get? (lm22StepAnnealN lm22ReassignBody 6
          (initMachineState lm22ReassignBody [])).frame.locals 1 =
          some (.init (.aggregate 0 [.scalar ⟨0x01020304, 4⟩, .scalar ⟨0x5566, 2⟩])) := rfl
      have hsome := Option.some.inj (hsl6.symm.trans hr)
      injection hsome
    subst hrv_eq
    exact ⟨tf6, mp6, lay6, htf6, hloc6, hsmpr6⟩
  have ⟨hs6, ha5, hm5⟩ := lm22_trace_step ⟨[2, 1], [3, 0]⟩ (fuel := 7) hs5
    lm22Reassign_phase rfl rfl (lm22Reassign_fw_wt _ 0 (by decide)) rfl rfl
  have ⟨hs7, ha6, hm6⟩ := lm22_trace_step ⟨[1, 2, 1], [3, 0]⟩ (fuel := 6) hs6
    lm22Reassign_phase rfl rfl (lm22Reassign_useStruct_wt _ 0) rfl rfl
  have ⟨hs8, ha7, hm7⟩ := lm22_trace_step ⟨[3, 1, 2, 1], [3, 3, 0]⟩ (fuel := 5) hs7
    lm22Reassign_phase rfl rfl (lm22Reassign_read1_wt _ 0 (by decide)) rfl rfl
  have ⟨hs9, ha8, hm8⟩ := lm22_trace_step ⟨[0, 3, 1, 2, 1], [0, 3, 3, 0]⟩ (fuel := 4) hs8
    lm22Reassign_phase rfl rfl (lm22Reassign_read0_wt _ 0 (by decide)) rfl rfl
  have ⟨hs10, ha9, hm9⟩ := lm22_trace_step ⟨[3, 0, 3, 1, 2, 1], [3, 0, 3, 3, 0]⟩ (fuel := 3) hs9
    lm22Reassign_phase rfl rfl (.storageDead _ 0 3 u16Decl _ rfl (by decide)) rfl rfl
  have ⟨hs11, ha10, hm10⟩ := lm22_trace_step ⟨[2, 3, 0, 3, 1, 2, 1], [2, 3, 0, 3, 3, 0]⟩
    (fuel := 2) hs10
    lm22Reassign_phase rfl rfl (.storageDead _ 0 2 lm22PairDecl _ rfl (by decide)) rfl rfl
  have ⟨hs12, ha11, hm11⟩ := lm22_trace_step ⟨[1, 2, 3, 0, 3, 1, 2, 1], [1, 2, 3, 0, 3, 3, 0]⟩
    (fuel := 1) hs11
    lm22Reassign_phase rfl rfl (.storageDead _ 0 1 lm22PairDecl _ rfl (by decide)) rfl rfl
  have hbase12 : StateRel lm22ReassignBody
      (lm22StepAnnealN lm22ReassignBody 12 (initMachineState lm22ReassignBody []))
      (lm22StepMiriN lm22ReassignBody 12 lm22ReassignMiriInit) := by
    refine hs12.toStateRel_of_flat_imm (by rintro ⟨_, _⟩ _ _ h _ _ ⟨⟩; cases h) (fun i _ _ _ _ hdecl henv hslot _ => ?_) ?hunpad
    case hunpad =>
      intro i _ _ _ _ _ _ hdecl henv hslot _
      match i with
      | 0 | 3 => cases Option.some.inj hdecl; cases henv
      | 1 =>
        have hdead :
            get? (lm22StepAnnealN lm22ReassignBody 12
              (initMachineState lm22ReassignBody [])).frame.locals 1 = some .dead := rfl
        rw [hdead] at hslot; cases hslot
      | 2 =>
        have hdead :
            get? (lm22StepAnnealN lm22ReassignBody 12
              (initMachineState lm22ReassignBody [])).frame.locals 2 = some .dead := rfl
        rw [hdead] at hslot; cases hslot
      | _ + 4 => simp [lm22ReassignBody, get?] at hdecl
    match i with
    | 0 | 3 => exact False.elim (henv (by cases Option.some.inj hdecl; rfl))
    | 1 =>
      have hdead :
          get? (lm22StepAnnealN lm22ReassignBody 12
            (initMachineState lm22ReassignBody [])).frame.locals 1 = some .dead := rfl
      rw [hdead] at hslot; cases hslot
    | 2 =>
      have hdead :
          get? (lm22StepAnnealN lm22ReassignBody 12
            (initMachineState lm22ReassignBody [])).frame.locals 2 = some .dead := rfl
      rw [hdead] at hslot; cases hslot
    | _ + 4 => simp [lm22ReassignBody, get?] at hdecl
  have himm0_12 := lm22_imm_of_mem_immLocals hs12 (idx := 0) (by decide)
  obtain ⟨ha_ret, hm_ret⟩ := lm22_return_agree_of_stateRel hbase12 lm22Reassign_phase
    rfl rfl rfl rfl rfl rfl lm22_u32_prim himm0_12 rfl
  have ha_tot :
      runAnnealBounded lm22ReassignBody 13 (initMachineState lm22ReassignBody []) =
        runAnnealBounded lm22ReassignBody 1
          (lm22StepAnnealN lm22ReassignBody 12 (initMachineState lm22ReassignBody [])) :=
    ha0.trans (ha1.trans (ha2.trans (ha3.trans (ha4.trans (ha5.trans (ha6.trans
      (ha7.trans (ha8.trans (ha9.trans (ha10.trans ha11))))))))))
  have hm_tot :
      runMiriBoundedLM2_2 lm22ReassignBody 13 lm22ReassignMiriInit =
        runMiriBoundedLM2_2 lm22ReassignBody 1 (lm22StepMiriN lm22ReassignBody 12 lm22ReassignMiriInit) :=
    hm0.trans (hm1.trans (hm2.trans (hm3.trans (hm4.trans (hm5.trans (hm6.trans
      (hm7.trans (hm8.trans (hm9.trans (hm10.trans hm11))))))))))
  rw [ha_tot, hm_tot]
  exact ⟨hmem6, rfl, hs7, rfl, ha_ret, hm_ret⟩

/-- The statements of `lm22ReassignBody`'s only basic block. -/
def lm22ReassignStmts : List MirAst.Statement :=
  (lm22ReassignBody.basicBlocks.head?.map (·.statements)).getD []

/-- `WellTypedLM2_2Stmts` derivation for the whole block of `lm22ReassignBody`,
from the initial static environment and allocation budget `3` down to budget `0`. -/
theorem lm22Reassign_block_wt :
    WellTypedLM2_2Stmts lm22ReassignBody lm22PairEnv { initLocals := [], immLocals := [0] } 3
      lm22ReassignStmts
      { initLocals := [1, 2, 3, 0, 3, 1, 2, 1], immLocals := [1, 2, 3, 0, 3, 3, 0] } 0 :=
  .cons (.storageLive _ 3 1 lm22PairDecl _ rfl) <|
  .cons (.storageLive _ 3 2 lm22PairDecl _ rfl) <|
  .cons (.storageLive _ 3 3 u16Decl _ rfl) <|
  .cons (lm22Reassign_agg_wt _ 2 1 0x11223344 0x5566 rfl (by decide) (by decide)) <|
  .cons (lm22Reassign_agg_wt _ 1 2 0xAABBCCDD 0x7788 rfl (by decide) (by decide)) <|
  .cons (lm22Reassign_fw_wt _ 0 (by decide)) <|
  .cons (lm22Reassign_useStruct_wt _ 0) <|
  .cons (lm22Reassign_read1_wt _ 0 (by decide)) <|
  .cons (lm22Reassign_read0_wt _ 0 (by decide)) <|
  .cons (.storageDead _ 0 3 u16Decl _ rfl (by decide)) <|
  .cons (.storageDead _ 0 2 lm22PairDecl _ rfl (by decide)) <|
  .cons (.storageDead _ 0 1 lm22PairDecl _ rfl (by decide)) <|
  .nil _ 0

/-- `step_stmts_lm2_2_simulation` instantiated on the whole 12-statement block of
`lm22ReassignBody` in one application: both machines run the block in lockstep
to `StateRelLM2_2`-related states at the block terminator. The UB alternative is
refuted by Anneal's concrete execution. -/
theorem lm22Reassign_block_stmts_simulation :
    ∃ s' m',
      runAnnealBounded lm22ReassignBody 12 (initMachineState lm22ReassignBody []) = .running s' ∧
      runMiriBoundedLM2_2 lm22ReassignBody 12 lm22ReassignMiriInit = .running m' ∧
      StateRelLM2_2 lm22ReassignBody lm22PairEnv
        { initLocals := [1, 2, 3, 0, 3, 1, 2, 1], immLocals := [1, 2, 3, 0, 3, 3, 0] } 0 s' m' ∧
      s'.frame.blockIdx = 0 ∧ s'.frame.stmtIdx = 12 := by
  have hsim := step_stmts_lm2_2_simulation lm22Reassign_phase (bb := _)
    lm22Reassign_block_wt lm22Reassign_stateRelLM2_2_init rfl
    (fun i hi => by
      show get? lm22ReassignStmts (0 + i) = some (lm22ReassignStmts[i]'hi)
      rw [Nat.zero_add, get?_eq_getElem?]
      exact List.getElem?_eq_getElem hi)
  rcases hsim with ⟨hub, _⟩ | ⟨s', m', hra, hrm, hst, hblk, hidx⟩
  · have hrun : runAnnealBounded lm22ReassignBody lm22ReassignStmts.length
        (initMachineState lm22ReassignBody []) =
        .running (lm22StepAnnealN lm22ReassignBody 12 (initMachineState lm22ReassignBody [])) := rfl
    rw [hrun] at hub; cases hub
  · exact ⟨s', m', hra, hrm, hst, hblk, hidx⟩

/-! ## 6. Non-Leaf `ScalarPair` Sub-Struct Read (`_3 = copy _2.1`) & Write (`_2.1 = move _4`) (`lm22SubStructBody`)

On `NestedOuter { tag: u8, inner: InnerPair }` (`inner` at offset `4`), a single
`ProjectionElem.field 1 InnerPair` projects to the whole `InnerPair` (`ScalarPair`)
sub-struct at offset `4`. This witness exercises both:
1. reading the whole `InnerPair` sub-struct from memory into an immediate local
   (`_3 = copy _2.1`, via `WellTypedLM2_2Operand.projectedSubStruct` and
   `evalOperand_nested_substruct_read_simulation`), and
2. writing a whole `InnerPair` sub-struct into memory at the projected offset
   (`_2.1 = move _4`, via `WellTypedLM2_2SubStructWrite` and
   `step_assign_nested_substruct_write_simulation`), preserving `_2.0 = 7_u8`
   and keeping all five alignment padding bytes (`1, 2, 3, 10, 11`) `.uninit`. -/

theorem lm22Nested_projChain_inner_substruct :
    ValidFieldProjChain lm22NestedLayoutTable
      (translateTy lm22NestedTy lm22NestedLayoutTable)
      [.field 1 lm22InnerPairTy] lm22InnerPairTy
      (Miri.ABI.Size.ofBytes 4) :=
  .single (translateTy lm22NestedTy lm22NestedLayoutTable) 1 lm22InnerPairTy
    (Miri.ABI.Size.ofBytes 4)
    (Or.inr (Or.inr ⟨"lm22::InnerPair", [], rfl⟩)) rfl rfl (by decide)

def lm22SubStructBody : CapturedMir where
  defPath := "lm_2_2_witness::nested_substruct_read_write"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls :=
    [u16Decl, lm22InnerPairDecl, lm22NestedDecl, lm22InnerPairDecl, lm22InnerPairDecl]
  basicBlocks := [
    { statements := [
        mkStmt22 (.storageLive 1),
        mkStmt22 (.storageLive 2),
        mkStmt22 (.storageLive 3),
        mkStmt22 (.storageLive 4),
        mkStmt22 (.assign ⟨1, []⟩
          (.aggregate (.adt "lm22::InnerPair" 0 .none)
            [.constant (lm22ConstU32 0x11112222), .constant (constU16 0x3344)])),
        mkStmt22 (.assign ⟨2, []⟩
          (.aggregate (.adt "lm22::NestedOuter" 0 .none)
            [.constant (constU8 7), .move ⟨1, []⟩])),
        mkStmt22 (.assign ⟨3, []⟩
          (.use (.copy ⟨2, [.field 1 lm22InnerPairTy]⟩))),
        mkStmt22 (.assign ⟨4, []⟩
          (.aggregate (.adt "lm22::InnerPair" 0 .none)
            [.constant (lm22ConstU32 0x55556666), .constant (constU16 0x7788)])),
        mkStmt22 (.assign ⟨2, [.field 1 lm22InnerPairTy]⟩
          (.use (.move ⟨4, []⟩))),
        mkStmt22 (.assign ⟨0, []⟩
          (.use (.copy ⟨2, [.field 1 lm22InnerPairTy, .field 1 u16Ty]⟩))),
        mkStmt22 (.storageDead 4),
        mkStmt22 (.storageDead 3),
        mkStmt22 (.storageDead 2),
        mkStmt22 (.storageDead 1)],
      terminator := mkTerm22 .return_,
      isCleanup := false }]
  fnAbi := lm22FnAbiU16
  layouts := lm22NestedLayoutTable
  allocations := []

def lm22SubStructMiriInit : AnnealStepState :=
  { stack := ⟨#[{
      body := translateBody lm22SubStructBody
      bodyIdentity := .ofCanonicalIndex 0
      functionInstance := { kind := .Item 0, args := #[] }
      extra := ()
      returnContinuation := .stop false
      returnPlace :=
        .frameLocal 0 0 none (translateTy u16Ty lm22NestedLayoutTable) (.ofAllocationToken 0)
      localsIdentity := .ofAllocationToken 0
      locals := #[
        { value := .live (.immediate .uninit), layout := none },
        { value := .dead, layout := none },
        { value := .dead, layout := none },
        { value := .dead, layout := none },
        { value := .dead, layout := none }]
      vaList := #[]
      trackCallerArg := none
      location := .mir ⟨0, 0⟩ }]⟩
    machine := AnnealMachine.empty }

theorem lm22SubStruct_phase : ∀ p, lm22SubStructBody.phase ≠ .other p := by
  intro p h; cases h

theorem lm22SubStruct_stateRelLM2_2_init :
    StateRelLM2_2 lm22SubStructBody lm22NestedEnv { initLocals := [], immLocals := [0] } 4
      (initMachineState lm22SubStructBody []) lm22SubStructMiriInit := by
  refine .mk _ rfl rfl ⟨translateTy u16Ty lm22NestedLayoutTable, rfl⟩ ?_
    (fun _ h => nomatch h)
    (fun j hj mp l => by simp at hj; subst hj; dsimp [lm22SubStructMiriInit]; nofun)
    (Or.inr (AllocIdWatermark.empty 4 (by decide))) rfl rfl rfl rfl rfl
    (by intro i _ _ _ _ _ _ hi _; revert hi
        match i with | 0 | 1 | 2 | 3 | 4 | _ + 5 => rintro ⟨⟩)
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro i decl slot mls hdecl hslot hmls
  match i with
  | 0 =>
    cases Option.some.inj hdecl
    cases Option.some.inj hslot
    cases Option.some.inj hmls
    exact .base .uninit _ rfl (.immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩))
  | 1 | 3 | 4 =>
    cases Option.some.inj hdecl
    cases Option.some.inj hslot
    cases Option.some.inj hmls
    exact .structDead lm22InnerPairFields lm22InnerPairPaths none rfl (fun _ h => nomatch h)
  | 2 =>
    cases Option.some.inj hdecl
    cases Option.some.inj hslot
    cases Option.some.inj hmls
    exact .structDead lm22NestedFields lm22NestedPaths none rfl (fun _ h => nomatch h)
  | _ + 5 => simp [lm22SubStructBody, get?] at hdecl

theorem lm22SubStruct_read_wt :
    WellTypedLM2_2ProjectedSubStructRead lm22SubStructBody lm22NestedEnv
      2 [.field 1 lm22InnerPairTy] lm22InnerPairTy
      lm22InnerPairField0 lm22InnerPairField1 lm22U32Ty u16Ty :=
  .mk lm22NestedDecl lm22NestedFields lm22NestedPaths 1 2
    (by decide) (by decide) (by decide) (by decide)
    (Miri.ABI.Size.ofBytes 4) (Miri.ABI.Size.ofBytes 4) _ _
    rfl rfl rfl (by decide) rfl rfl rfl rfl rfl rfl rfl (by decide)
    rfl rfl rfl rfl rfl rfl
    lm22InnerPair_validStructLayout (by decide) (by decide)
    (Or.inr ⟨"lm22::InnerPair", [], rfl⟩)
    (fun _ h => nomatch h)
    rfl (by decide) (by decide) (by decide) (by decide)
    (Or.inl lm22_u32_prim) (Or.inl lm22_u16_prim)
    lm22_u32_prim lm22_u16_prim
    lm22Nested_projChain_inner_substruct

theorem lm22SubStruct_write_wt (stEnv : LM2_2StaticEnv) (h2_init : 2 ∈ stEnv.initLocals) :
    WellTypedLM2_2SubStructWrite lm22SubStructBody lm22NestedEnv stEnv
      2 [.field 1 lm22InnerPairTy] (.move ⟨4, []⟩) :=
  .mk lm22NestedDecl lm22NestedFields lm22NestedPaths 1 2
    (by decide) (by decide) (by decide) (by decide)
    lm22InnerPairTy lm22InnerPairField0 lm22InnerPairField1 lm22U32Ty u16Ty _ _
    (Miri.ABI.Size.ofBytes 4)
    rfl rfl h2_init (by decide) rfl rfl
    (fun j hj hne1 hne2 => by
      match j with
      | 0 => exact .diff_head (by decide)
      | 1 => exact False.elim (hne1 rfl)
      | 2 => exact False.elim (hne2 rfl)
      | _ + 3 => simp [lm22NestedPaths] at hj; omega)
    lm22Nested_projChain_inner_substruct
    rfl rfl rfl lm22InnerPair_isImmediateStructTy
    rfl rfl rfl rfl
    (by decide : (4 : Nat) ≠ 2)
    (.immStructLocal true 4 lm22InnerPairDecl lm22InnerPairFields lm22InnerPairPaths
      rfl lm22InnerPair_isImmediateStructTy)

/-- Full lockstep trace for `lm22SubStructBody`:
1. `_3 = copy _2.1` reads the whole `InnerPair` (`ScalarPair`) sub-struct at offset `4`
   into `_3` as `.aggregate 0 [.scalar ⟨0x11112222, 4⟩, .scalar ⟨0x3344, 2⟩]` in Anneal
   and `ImmediateStructRel` (`ScalarPair`) in `lean-miri`;
2. `_2.1 = move _4` overwrites the whole `InnerPair` sub-struct at offset `4` with
   `(0x55556666, 0x7788)`, preserving `_2.0 = 7_u8` and keeping all five padding
   bytes (`1, 2, 3, 10, 11`) `.uninit`;
3. bounded execution returns `some 0x7788` on both sides. -/
theorem lm22SubStruct_full_trace_and_returns_agree :
    (get? (lm22StepAnnealN lm22SubStructBody 7 (initMachineState lm22SubStructBody [])).frame.locals 3 =
      some (.init (.aggregate 0 [.scalar ⟨0x11112222, 4⟩, .scalar ⟨0x3344, 2⟩])) ∧
     ∃ imm,
      ImmediateStructRel lm22InnerPairTy lm22NestedLayoutTable
        lm22InnerPairFields lm22InnerPairPaths
        (.aggregate 0 [.scalar ⟨0x11112222, 4⟩, .scalar ⟨0x3344, 2⟩]) imm) ∧
    (∃ mp localAlloc,
      StructMemPlaceRel
        (lm22StepMiriN lm22SubStructBody 9 lm22SubStructMiriInit).machine
        lm22NestedTy lm22NestedLayoutTable lm22NestedFields lm22NestedPaths
        (.aggregate 0 [.scalar ⟨7, 1⟩, .aggregate 0 [.scalar ⟨0x55556666, 4⟩, .scalar ⟨0x7788, 2⟩]]) mp ∧
      (∃ allocId,
        (∃ tag, mp.ptr.provenance = some (.concrete allocId tag)) ∧
        (lm22StepMiriN lm22SubStructBody 9 lm22SubStructMiriInit).machine.memory.live.find?
          (fun (k, _) => k == allocId) = some (allocId, localAlloc)) ∧
      localAlloc.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 1) = .ok false ∧
      localAlloc.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 2) = .ok false ∧
      localAlloc.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 3) = .ok false ∧
      localAlloc.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 10) = .ok false ∧
      localAlloc.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 11) = .ok false ∧
      localAlloc.allocation.initializationMask.isRangeInitialized
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 12)) ≠ .ok (.ok ())) ∧
    annealOutcomeScalarBits 2
      (runAnnealBounded lm22SubStructBody 15 (initMachineState lm22SubStructBody [])) = some 0x7788 ∧
    miriOutcomeScalarBits 2
      (runMiriBoundedLM2_2 lm22SubStructBody 15 lm22SubStructMiriInit) = some 0x7788 := by
  have hs0 : StateRelLM2_2 lm22SubStructBody lm22NestedEnv { initLocals := [], immLocals := [0] } 4
      (lm22StepAnnealN lm22SubStructBody 0 (initMachineState lm22SubStructBody []))
      (lm22StepMiriN lm22SubStructBody 0 lm22SubStructMiriInit) :=
    lm22SubStruct_stateRelLM2_2_init
  have ⟨hs1, ha0, hm0⟩ := lm22_trace_step ⟨[], [1, 0]⟩ (fuel := 14) hs0
    lm22SubStruct_phase rfl rfl (.storageLive _ 4 1 lm22InnerPairDecl _ rfl) rfl rfl
  have ⟨hs2, ha1, hm1⟩ := lm22_trace_step ⟨[], [2, 1, 0]⟩ (fuel := 13) hs1
    lm22SubStruct_phase rfl rfl (.storageLive _ 4 2 lm22NestedDecl _ rfl) rfl rfl
  have ⟨hs3, ha2, hm2⟩ := lm22_trace_step ⟨[], [3, 2, 1, 0]⟩ (fuel := 12) hs2
    lm22SubStruct_phase rfl rfl (.storageLive _ 4 3 lm22InnerPairDecl _ rfl) rfl rfl
  have ⟨hs4, ha3, hm3⟩ := lm22_trace_step ⟨[], [4, 3, 2, 1, 0]⟩ (fuel := 11) hs3
    lm22SubStruct_phase rfl rfl (.storageLive _ 4 4 lm22InnerPairDecl _ rfl) rfl rfl
  have hwt4 : WellTypedLM2_2Stmt lm22SubStructBody lm22NestedEnv ⟨[], [4, 3, 2, 1, 0]⟩ 4
      (mkStmt22 (.assign ⟨1, []⟩
        (.aggregate (.adt "lm22::InnerPair" 0 .none)
          [.constant (lm22ConstU32 0x11112222), .constant (constU16 0x3344)])))
      (aggPostStaticEnv ⟨[], [4, 3, 2, 1, 0]⟩ 1
        [.constant (lm22ConstU32 0x11112222), .constant (constU16 0x3344)]) 3 :=
    .assignAggregate _ 3 1 _ _ _
      (.mk lm22InnerPairDecl lm22InnerPairFields lm22InnerPairPaths _ _ rfl
        (Or.inr ⟨"lm22::InnerPair", rfl⟩) rfl rfl lm22InnerPair_validStructLayout
        (by decide) rfl rfl (by decide)
        (.cons _ 0 0 1 _ _ trivial
          (.primLeaf (by decide) _ (lm22_constU32_wt 0x11112222 (by decide) rfl)
            rfl lm22_u32_prim rfl rfl rfl rfl rfl rfl)
          (.cons _ 1 1 2 _ [] trivial
            (.primLeaf (by decide) _ (lm22_constU16_wt 0x3344 (by decide) rfl)
              rfl lm22_u16_prim rfl rfl rfl rfl rfl rfl)
            (.nil _ 2))))
  have ⟨hs5, ha4, hm4⟩ := lm22_trace_step ⟨[1], [4, 3, 2, 0]⟩ (fuel := 10) hs4
    lm22SubStruct_phase rfl rfl hwt4 rfl rfl
  have hwt5 : WellTypedLM2_2Stmt lm22SubStructBody lm22NestedEnv ⟨[1], [4, 3, 2, 0]⟩ 3
      (mkStmt22 (.assign ⟨2, []⟩
        (.aggregate (.adt "lm22::NestedOuter" 0 .none)
          [.constant (constU8 7), .move ⟨1, []⟩])))
      (aggPostStaticEnv ⟨[1], [4, 3, 2, 0]⟩ 2 [.constant (constU8 7), .move ⟨1, []⟩]) 2 :=
    .assignAggregate _ 2 2 _ _ _
      (.mk lm22NestedDecl lm22NestedFields lm22NestedPaths _ _ rfl
        (Or.inr ⟨"lm22::NestedOuter", rfl⟩) rfl rfl lm22Nested_validStructLayout
        (by decide) rfl rfl (by decide)
        (.cons _ 0 0 1 _ _ trivial
          (.primLeaf (by decide) _ (lm22_constU8_wt 7 (by decide) rfl)
            rfl lm22_u8_prim rfl rfl rfl rfl rfl rfl)
          (.cons _ 1 1 3 (.move ⟨1, []⟩) [] (by decide : (1 : Nat) ≠ 2)
            (.scalarPairSub (by decide) lm22InnerPairTy lm22InnerPairField0 lm22InnerPairField1
              lm22U32Ty u16Ty [] [] _ _ _ (Miri.ABI.Size.ofBytes 4)
              (.immStructLocal true 1 lm22InnerPairDecl lm22InnerPairFields
                lm22InnerPairPaths rfl lm22InnerPair_isImmediateStructTy)
              lm22InnerPair_isImmediateStructTy
              rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide))
            (.nil _ 2))))
  have ⟨hs6, ha5, hm5⟩ := lm22_trace_step ⟨[2], [1, 4, 3, 0]⟩ (fuel := 9) hs5
    lm22SubStruct_phase rfl rfl hwt5 rfl rfl
  have hwt6 : WellTypedLM2_2Stmt lm22SubStructBody lm22NestedEnv ⟨[2], [1, 4, 3, 0]⟩ 2
      (mkStmt22 (.assign ⟨3, []⟩ (.use (.copy ⟨2, [.field 1 lm22InnerPairTy]⟩))))
      (usePostStaticEnv ⟨[2], [1, 4, 3, 0]⟩ 3 (.copy ⟨2, [.field 1 lm22InnerPairTy]⟩)) 2 :=
    .assignUse _ 2 3 (.copy ⟨2, [.field 1 lm22InnerPairTy]⟩) _
      (.mk lm22InnerPairDecl rfl (by decide)
        (.projectedSubStruct false 2 [.field 1 lm22InnerPairTy] lm22InnerPairTy
          lm22InnerPairField0 lm22InnerPairField1 lm22U32Ty u16Ty
          lm22InnerPair_isImmediateStructTy lm22SubStruct_read_wt))
  have ⟨hs7, ha6, hm6⟩ := lm22_trace_step ⟨[3, 2], [3, 1, 4, 3, 0]⟩ (fuel := 8) hs6
    lm22SubStruct_phase rfl rfl hwt6 rfl rfl
  have hwt7 : WellTypedLM2_2Stmt lm22SubStructBody lm22NestedEnv ⟨[3, 2], [3, 1, 4, 3, 0]⟩ 2
      (mkStmt22 (.assign ⟨4, []⟩
        (.aggregate (.adt "lm22::InnerPair" 0 .none)
          [.constant (lm22ConstU32 0x55556666), .constant (constU16 0x7788)])))
      (aggPostStaticEnv ⟨[3, 2], [3, 1, 4, 3, 0]⟩ 4
        [.constant (lm22ConstU32 0x55556666), .constant (constU16 0x7788)]) 1 :=
    .assignAggregate _ 1 4 _ _ _
      (.mk lm22InnerPairDecl lm22InnerPairFields lm22InnerPairPaths _ _ rfl
        (Or.inr ⟨"lm22::InnerPair", rfl⟩) rfl rfl lm22InnerPair_validStructLayout
        (by decide) rfl rfl (by decide)
        (.cons _ 0 0 1 _ _ trivial
          (.primLeaf (by decide) _ (lm22_constU32_wt 0x55556666 (by decide) rfl)
            rfl lm22_u32_prim rfl rfl rfl rfl rfl rfl)
          (.cons _ 1 1 2 _ [] trivial
            (.primLeaf (by decide) _ (lm22_constU16_wt 0x7788 (by decide) rfl)
              rfl lm22_u16_prim rfl rfl rfl rfl rfl rfl)
            (.nil _ 2))))
  have ⟨hs8, ha7, hm7⟩ := lm22_trace_step ⟨[4, 3, 2], [3, 1, 3, 0]⟩ (fuel := 7) hs7
    lm22SubStruct_phase rfl rfl hwt7 rfl rfl
  have hwt8 : WellTypedLM2_2Stmt lm22SubStructBody lm22NestedEnv ⟨[4, 3, 2], [3, 1, 3, 0]⟩ 1
      (mkStmt22 (.assign ⟨2, [.field 1 lm22InnerPairTy]⟩ (.use (.move ⟨4, []⟩))))
      (fieldWritePostStaticEnv ⟨[4, 3, 2], [3, 1, 3, 0]⟩ 2 (.move ⟨4, []⟩)) 1 :=
    .assignSubStructWrite _ 1 2 [.field 1 lm22InnerPairTy] (.move ⟨4, []⟩) _
      (lm22SubStruct_write_wt _ (by decide))
  have ⟨hs9, ha8, hm8⟩ := lm22_trace_step ⟨[3, 2], [4, 3, 1, 3, 0]⟩ (fuel := 6) hs8
    lm22SubStruct_phase rfl rfl hwt8 rfl rfl
  have hwt9 : WellTypedLM2_2Stmt lm22SubStructBody lm22NestedEnv ⟨[3, 2], [4, 3, 1, 3, 0]⟩ 1
      (mkStmt22 (.assign ⟨0, []⟩
        (.use (.copy ⟨2, [.field 1 lm22InnerPairTy, .field 1 u16Ty]⟩))))
      (usePostStaticEnv ⟨[3, 2], [4, 3, 1, 3, 0]⟩ 0
        (.copy ⟨2, [.field 1 lm22InnerPairTy, .field 1 u16Ty]⟩)) 1 :=
    .assignUse _ 1 0 _ _
      (.mk u16Decl rfl (by decide)
        (.projectedScalar false 2 [.field 1 lm22InnerPairTy, .field 1 u16Ty]
          u16Ty rfl
          (.mk lm22NestedDecl lm22NestedFields lm22NestedPaths 2 (by decide) (by decide)
            rfl rfl rfl rfl lm22_u16_prim lm22Nested_projChain_inner1)))
  have ⟨hs10, ha9, hm9⟩ := lm22_trace_step ⟨[0, 3, 2], [0, 4, 3, 1, 3, 0]⟩ (fuel := 5) hs9
    lm22SubStruct_phase rfl rfl hwt9 rfl rfl
  have ⟨hs11, ha10, hm10⟩ := lm22_trace_step ⟨[4, 0, 3, 2], [4, 0, 4, 3, 1, 3, 0]⟩ (fuel := 4) hs10
    lm22SubStruct_phase rfl rfl (.storageDead _ 1 4 lm22InnerPairDecl _ rfl (by decide)) rfl rfl
  have ⟨hs12, ha11, hm11⟩ := lm22_trace_step ⟨[3, 4, 0, 3, 2], [3, 4, 0, 4, 3, 1, 3, 0]⟩ (fuel := 3) hs11
    lm22SubStruct_phase rfl rfl (.storageDead _ 1 3 lm22InnerPairDecl _ rfl (by decide)) rfl rfl
  have ⟨hs13, ha12, hm12⟩ := lm22_trace_step ⟨[2, 3, 4, 0, 3, 2], [2, 3, 4, 0, 4, 3, 1, 3, 0]⟩ (fuel := 2) hs12
    lm22SubStruct_phase rfl rfl (.storageDead _ 1 2 lm22NestedDecl _ rfl (by decide)) rfl rfl
  have ⟨hs14, ha13, hm13⟩ := lm22_trace_step ⟨[1, 2, 3, 4, 0, 3, 2], [1, 2, 3, 4, 0, 4, 3, 1, 3, 0]⟩ (fuel := 1) hs13
    lm22SubStruct_phase rfl rfl (.storageDead _ 1 1 lm22InnerPairDecl _ rfl (by decide)) rfl rfl
  rw [show (((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1 = 14 from rfl] at hs14
  have hread7 :
      get? (lm22StepAnnealN lm22SubStructBody 7 (initMachineState lm22SubStructBody [])).frame.locals 3 =
        some (.init (.aggregate 0 [.scalar ⟨0x11112222, 4⟩, .scalar ⟨0x3344, 2⟩])) ∧
      ∃ imm,
        ImmediateStructRel lm22InnerPairTy lm22NestedLayoutTable
          lm22InnerPairFields lm22InnerPairPaths
          (.aggregate 0 [.scalar ⟨0x11112222, 4⟩, .scalar ⟨0x3344, 2⟩]) imm := by
    refine ⟨rfl, ?_⟩
    rcases hs7 with ⟨tf7, htf7, _, _, hfr7, _, himm7, _, _, _, _, _, _, _⟩
    obtain ⟨_, mls7, _, _, hslot7, hmls7, _, hloc7⟩ :=
      hfr7.lookup_local (idx := 3) (decl := lm22InnerPairDecl) rfl
    have hsl7_eq : get? (lm22StepAnnealN lm22SubStructBody 7
        (initMachineState lm22SubStructBody [])).frame.locals 3 =
        some (.init (.aggregate 0 [.scalar ⟨0x11112222, 4⟩, .scalar ⟨0x3344, 2⟩])) := rfl
    rw [hsl7_eq] at hslot7; cases Option.some.inj hslot7
    cases hloc7 with
    | base _ _ he _ => cases he
    | structImm fs ps _ imm _ henv' _ himm =>
      rcases Prod.mk.inj (Option.some.inj henv') with ⟨rfl, rfl⟩
      exact ⟨imm, himm⟩
    | structInd _ _ _ mp lay _ _ _ =>
      exact False.elim (himm7 3 (by decide) mp lay hmls7)
  have hpad9 :
      ∃ mp localAlloc,
        StructMemPlaceRel
          (lm22StepMiriN lm22SubStructBody 9 lm22SubStructMiriInit).machine
          lm22NestedTy lm22NestedLayoutTable lm22NestedFields lm22NestedPaths
          (.aggregate 0 [.scalar ⟨7, 1⟩, .aggregate 0 [.scalar ⟨0x55556666, 4⟩, .scalar ⟨0x7788, 2⟩]]) mp ∧
        (∃ allocId,
          (∃ tag, mp.ptr.provenance = some (.concrete allocId tag)) ∧
          (lm22StepMiriN lm22SubStructBody 9 lm22SubStructMiriInit).machine.memory.live.find?
            (fun (k, _) => k == allocId) = some (allocId, localAlloc)) ∧
        localAlloc.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 1) = .ok false ∧
        localAlloc.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 2) = .ok false ∧
        localAlloc.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 3) = .ok false ∧
        localAlloc.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 10) = .ok false ∧
        localAlloc.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 11) = .ok false ∧
        localAlloc.allocation.initializationMask.isRangeInitialized
          (Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 12)) ≠ .ok (.ok ()) := by
    rcases lm22_extract_struct_local hs9 (idx := 2) rfl rfl rfl with ⟨_, himm⟩ | ⟨mp, hsmpr⟩
    · exact False.elim (lm22_not_immediateStructRel_of_memory rfl himm)
    · obtain ⟨p1, p2, p3, p10, p11⟩ := lm22Nested_all_five_padding_bytes
      obtain ⟨allocId, localAlloc, hprov, hfind, hpad_fn, hhas_uninit⟩ :=
        hsmpr.has_uninit_of_padding_byte p1
      exact ⟨mp, localAlloc, hsmpr, ⟨allocId, hprov, hfind⟩,
        hpad_fn 1 p1, hpad_fn 2 p2, hpad_fn 3 p3, hpad_fn 10 p10, hpad_fn 11 p11, hhas_uninit⟩
  have hbase14 : StateRel lm22SubStructBody
      (lm22StepAnnealN lm22SubStructBody 14 (initMachineState lm22SubStructBody []))
      (lm22StepMiriN lm22SubStructBody 14 lm22SubStructMiriInit) := by
    refine hs14.toStateRel_of_flat_imm (by rintro ⟨_, _⟩ _ _ h _ _ ⟨⟩; cases h) (fun i _ _ _ _ hdecl henv hslot _ => ?_) ?hunpad
    case hunpad =>
      intro i _ _ _ _ _ _ hdecl henv hslot _
      match i with
      | 0 => cases Option.some.inj hdecl; cases henv
      | 1 =>
        have hd1 :
            get? (lm22StepAnnealN lm22SubStructBody 14 (initMachineState lm22SubStructBody [])).frame.locals 1 =
              some .dead := rfl
        rw [hd1] at hslot; cases hslot
      | 2 =>
        have hd2 :
            get? (lm22StepAnnealN lm22SubStructBody 14 (initMachineState lm22SubStructBody [])).frame.locals 2 =
              some .dead := rfl
        rw [hd2] at hslot; cases hslot
      | 3 =>
        have hd3 :
            get? (lm22StepAnnealN lm22SubStructBody 14 (initMachineState lm22SubStructBody [])).frame.locals 3 =
              some .dead := rfl
        rw [hd3] at hslot; cases hslot
      | 4 =>
        have hd4 :
            get? (lm22StepAnnealN lm22SubStructBody 14 (initMachineState lm22SubStructBody [])).frame.locals 4 =
              some .dead := rfl
        rw [hd4] at hslot; cases hslot
      | _ + 5 => simp [lm22SubStructBody, get?] at hdecl
    match i with
    | 0 => cases Option.some.inj hdecl; exact False.elim (henv rfl)
    | 1 =>
      have hd1 :
          get? (lm22StepAnnealN lm22SubStructBody 14 (initMachineState lm22SubStructBody [])).frame.locals 1 =
            some .dead := rfl
      rw [hd1] at hslot; cases hslot
    | 2 =>
      have hd2 :
          get? (lm22StepAnnealN lm22SubStructBody 14 (initMachineState lm22SubStructBody [])).frame.locals 2 =
            some .dead := rfl
      rw [hd2] at hslot; cases hslot
    | 3 =>
      have hd3 :
          get? (lm22StepAnnealN lm22SubStructBody 14 (initMachineState lm22SubStructBody [])).frame.locals 3 =
            some .dead := rfl
      rw [hd3] at hslot; cases hslot
    | 4 =>
      have hd4 :
          get? (lm22StepAnnealN lm22SubStructBody 14 (initMachineState lm22SubStructBody [])).frame.locals 4 =
            some .dead := rfl
      rw [hd4] at hslot; cases hslot
    | _ + 5 => simp [lm22SubStructBody, get?] at hdecl
  have himm0_14 := lm22_imm_of_mem_immLocals hs14 (idx := 0) (by decide)
  obtain ⟨ha_ret, hm_ret⟩ := lm22_return_agree_of_stateRel hbase14 lm22SubStruct_phase
    rfl rfl rfl rfl rfl rfl lm22_u16_prim himm0_14 rfl
  have ha_tot :
      runAnnealBounded lm22SubStructBody 15 (initMachineState lm22SubStructBody []) =
        runAnnealBounded lm22SubStructBody 1
          (lm22StepAnnealN lm22SubStructBody 14 (initMachineState lm22SubStructBody [])) :=
    ha0.trans (ha1.trans (ha2.trans (ha3.trans (ha4.trans (ha5.trans (ha6.trans
      (ha7.trans (ha8.trans (ha9.trans (ha10.trans (ha11.trans (ha12.trans ha13))))))))))))
  have hm_tot :
      runMiriBoundedLM2_2 lm22SubStructBody 15 lm22SubStructMiriInit =
        runMiriBoundedLM2_2 lm22SubStructBody 1 (lm22StepMiriN lm22SubStructBody 14 lm22SubStructMiriInit) :=
    hm0.trans (hm1.trans (hm2.trans (hm3.trans (hm4.trans (hm5.trans (hm6.trans
      (hm7.trans (hm8.trans (hm9.trans (hm10.trans (hm11.trans (hm12.trans hm13))))))))))))
  rw [ha_tot, hm_tot]
  exact ⟨hread7, hpad9, ha_ret, hm_ret⟩

/-! ## 7. Multi-Block `InitMask` Struct Larger Than 64 Bytes (`LargePadded80`, `80` Bytes)

`LargePadded80` has `size = 80` bytes (`> 64`), spanning two 64-byte `UInt64`
blocks in `InitMask` (`words.size = 80 / 64 + 1 = 2`):
- field 0 (`u8`) at byte offset `0` (block 0),
- field 1 (`u32`) at byte offset `4` (block 0),
- field 2 (`u32`) at byte offset `68` (block 1, `≥ 64`),
with inter-field padding across `[1, 4)` (block 0) and `[8, 68)` (crossing from
block 0 into block 1 at byte `64`) and trailing padding `[72, 80)` (block 1). -/

def lm22LargeTy : Ty :=
  { kind := .adt "lm22::LargePadded80" [], layoutIdx := 0 }

def lm22LargeDecl : LocalDecl :=
  { mutability := .mut, ty := lm22LargeTy, debugName := none }

def lm22LargeTypeLayout : TypeLayout :=
  { size := { bytes := 80 }
    align := { bytes := 4 }
    backendRepr := .memory
    fields := .arbitrary [{ bytes := 0 }, { bytes := 4 }, { bytes := 68 }] [0, 1, 2]
    variants := .single 0
    isUninhabited := false
    fieldLayouts := [2, 1, 1] }

def lm22LargeLayoutTable : LayoutTable :=
  { pointerBits := 64
    isLittleEndian := true
    entries := [lm22LargeTypeLayout, lm22U32TypeLayout, lm22U8TypeLayout] }

def lm22LargeField0 : StructFieldDesc :=
  { offset := Miri.ABI.Size.ZERO
    ty := u8Ty
    fieldLayout := (translateTy u8Ty lm22LargeLayoutTable).layout }

def lm22LargeField1 : StructFieldDesc :=
  { offset := Miri.ABI.Size.ofBytes 4
    ty := lm22U32Ty
    fieldLayout := (translateTy lm22U32Ty lm22LargeLayoutTable).layout }

def lm22LargeField2 : StructFieldDesc :=
  { offset := Miri.ABI.Size.ofBytes 68
    ty := lm22U32Ty
    fieldLayout := (translateTy lm22U32Ty lm22LargeLayoutTable).layout }

def lm22LargeFields : List StructFieldDesc :=
  [lm22LargeField0, lm22LargeField1, lm22LargeField2]

def lm22LargePaths : List (List ProjectionElem) :=
  [[.field 0 u8Ty], [.field 1 lm22U32Ty], [.field 2 lm22U32Ty]]

def lm22LargeEnv : StructTypeEnv := fun ty =>
  match ty.kind with
  | .adt "lm22::LargePadded80" [] => some (lm22LargeFields, lm22LargePaths)
  | _ => none

theorem lm22Large_validStructLayout :
    ValidStructLayout (translateTy lm22LargeTy lm22LargeLayoutTable).layout
      lm22LargeFields := by
  refine
    { fields_in_bounds := fun i hi => by
        match i with
        | 0 | 1 | 2 => decide +revert
        | _ + 3 => simp [lm22LargeFields] at hi; omega
      fields_disjoint := fun i j hi hj hne => by
        match i, j with
        | 0, 0 | 1, 1 | 2, 2 => exact False.elim (hne rfl)
        | 0, 1 | 0, 2 | 1, 2 => left; decide +revert
        | 1, 0 | 2, 0 | 2, 1 => right; decide +revert
        | _ + 3, _ => simp [lm22LargeFields] at hi; omega
        | _, _ + 3 => simp [lm22LargeFields] at hj; omega
      fields_aligned := fun i hi => by
        match i with
        | 0 | 1 | 2 => decide +revert
        | _ + 3 => simp [lm22LargeFields] at hi; omega
      fields_shape_valid := Or.inr (ValidStructLayout.arbitrary_flat #[0, 1, 2] rfl (by decide)) }

theorem lm22Large_multi_block_padding_bytes :
    isStructPaddingByte lm22LargeFields (Miri.ABI.Size.ofBytes 80) 1 ∧
    isStructPaddingByte lm22LargeFields (Miri.ABI.Size.ofBytes 80) 64 ∧
    isStructPaddingByte lm22LargeFields (Miri.ABI.Size.ofBytes 80) 72 := by
  have hp : ∀ b : Nat, b < 80 → (b = 1 ∨ b = 64 ∨ b = 72) →
      isStructPaddingByte lm22LargeFields (Miri.ABI.Size.ofBytes 80) b := by
    intro b hb hcases
    refine ⟨by change b < 80; exact hb, fun f hf => ?_⟩
    rcases hcases with rfl | rfl | rfl <;>
      (cases hf with
       | head => right; decide
       | tail _ hf2 =>
         cases hf2 with
         | head => first | (left; decide) | (right; decide)
         | tail _ hf3 =>
           cases hf3 with
           | head => first | (left; decide) | (right; decide)
           | tail _ hnil => cases hnil)
  exact ⟨hp 1 (by decide) (Or.inl rfl),
    hp 64 (by decide) (Or.inr (Or.inl rfl)),
    hp 72 (by decide) (Or.inr (Or.inr rfl))⟩

def lm22LargeBody : CapturedMir where
  defPath := "lm_2_2_witness::large_padded_80"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [lm22U32Decl, lm22LargeDecl]
  basicBlocks := [
    { statements := [
        mkStmt22 (.storageLive 1),
        mkStmt22 (.assign ⟨1, []⟩
          (.aggregate (.adt "lm22::LargePadded80" 0 .none)
            [.constant (constU8 5),
             .constant (lm22ConstU32 100),
             .constant (lm22ConstU32 200)])),
        mkStmt22 (.assign ⟨1, [.field 2 lm22U32Ty]⟩
          (.use (.constant (lm22ConstU32 999)))),
        mkStmt22 (.assign ⟨0, []⟩
          (.use (.copy ⟨1, [.field 2 lm22U32Ty]⟩))),
        mkStmt22 (.storageDead 1)],
      terminator := mkTerm22 .return_,
      isCleanup := false }]
  fnAbi := lm22FnAbiU32
  layouts := lm22LargeLayoutTable
  allocations := []

def lm22LargeMiriInit : AnnealStepState :=
  { stack := ⟨#[{
      body := translateBody lm22LargeBody
      bodyIdentity := .ofCanonicalIndex 0
      functionInstance := { kind := .Item 0, args := #[] }
      extra := ()
      returnContinuation := .stop false
      returnPlace :=
        .frameLocal 0 0 none (translateTy lm22U32Ty lm22LargeLayoutTable) (.ofAllocationToken 0)
      localsIdentity := .ofAllocationToken 0
      locals := #[
        { value := .live (.immediate .uninit), layout := none },
        { value := .dead, layout := none }]
      vaList := #[]
      trackCallerArg := none
      location := .mir ⟨0, 0⟩ }]⟩
    machine := AnnealMachine.empty }

theorem lm22Large_phase : ∀ p, lm22LargeBody.phase ≠ .other p := by
  intro p h; cases h

theorem lm22Large_stateRelLM2_2_init :
    StateRelLM2_2 lm22LargeBody lm22LargeEnv { initLocals := [], immLocals := [0] } 2
      (initMachineState lm22LargeBody []) lm22LargeMiriInit := by
  refine .mk _ rfl rfl ⟨translateTy lm22U32Ty lm22LargeLayoutTable, rfl⟩ ?_
    (fun _ h => nomatch h)
    (fun j hj mp l => by simp at hj; subst hj; dsimp [lm22LargeMiriInit]; nofun)
    (Or.inr (AllocIdWatermark.empty 2 (by decide))) rfl rfl rfl rfl rfl
    (by intro i _ _ _ _ _ _ hi _; revert hi; match i with | 0 | 1 | _ + 2 => rintro ⟨⟩)
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro i decl slot mls hdecl hslot hmls
  match i with
  | 0 =>
    cases Option.some.inj hdecl
    cases Option.some.inj hslot
    cases Option.some.inj hmls
    exact .base .uninit _ rfl (.immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩))
  | 1 =>
    cases Option.some.inj hdecl
    cases Option.some.inj hslot
    cases Option.some.inj hmls
    exact .structDead lm22LargeFields lm22LargePaths none rfl (fun _ h => nomatch h)
  | _ + 2 => simp [lm22LargeBody, get?] at hdecl

/-- Full lockstep trace for the 80-byte (`> 64`) multi-block `LargePadded80` struct:
1. after constructing `_1` (`80` bytes) and writing field 2 at offset `68` (in the
   second 64-byte `InitMask` block, `≥ 64`), `StructMemPlaceRel` holds for `_1`,
2. padding bytes in both `InitMask` block 0 (`byte 1`) and `InitMask` block 1
   (`byte 64` and `byte 72`) remain `.uninit` (`InitMask.get = .ok false`), and
3. bounded execution returns `some 999` on both Anneal and `lean-miri`. -/
theorem lm22Large_full_trace_and_returns_agree :
    (∃ mp localAlloc,
      StructMemPlaceRel
        (lm22StepMiriN lm22LargeBody 3 lm22LargeMiriInit).machine
        lm22LargeTy lm22LargeLayoutTable lm22LargeFields lm22LargePaths
        (.aggregate 0 [.scalar ⟨5, 1⟩, .scalar ⟨100, 4⟩, .scalar ⟨999, 4⟩]) mp ∧
      (∃ allocId,
        (∃ tag, mp.ptr.provenance = some (.concrete allocId tag)) ∧
        (lm22StepMiriN lm22LargeBody 3 lm22LargeMiriInit).machine.memory.live.find?
          (fun (k, _) => k == allocId) = some (allocId, localAlloc)) ∧
      localAlloc.allocation.byteSize = Miri.ABI.Size.ofBytes 80 ∧
      localAlloc.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 1) = .ok false ∧
      localAlloc.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 64) = .ok false ∧
      localAlloc.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 72) = .ok false ∧
      localAlloc.allocation.initializationMask.isRangeInitialized
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 80)) ≠ .ok (.ok ())) ∧
    annealOutcomeScalarBits 4
      (runAnnealBounded lm22LargeBody 6 (initMachineState lm22LargeBody [])) = some 999 ∧
    miriOutcomeScalarBits 4
      (runMiriBoundedLM2_2 lm22LargeBody 6 lm22LargeMiriInit) = some 999 := by
  have hs0 : StateRelLM2_2 lm22LargeBody lm22LargeEnv { initLocals := [], immLocals := [0] } 2
      (lm22StepAnnealN lm22LargeBody 0 (initMachineState lm22LargeBody []))
      (lm22StepMiriN lm22LargeBody 0 lm22LargeMiriInit) :=
    lm22Large_stateRelLM2_2_init
  have ⟨hs1, ha0, hm0⟩ := lm22_trace_step ⟨[], [1, 0]⟩ (fuel := 5) hs0
    lm22Large_phase rfl rfl (.storageLive _ 2 1 lm22LargeDecl _ rfl) rfl rfl
  have hwt1 : WellTypedLM2_2Stmt lm22LargeBody lm22LargeEnv ⟨[], [1, 0]⟩ 2
      (mkStmt22 (.assign ⟨1, []⟩
        (.aggregate (.adt "lm22::LargePadded80" 0 .none)
          [.constant (constU8 5),
           .constant (lm22ConstU32 100),
           .constant (lm22ConstU32 200)])))
      (aggPostStaticEnv ⟨[], [1, 0]⟩ 1
        [.constant (constU8 5), .constant (lm22ConstU32 100), .constant (lm22ConstU32 200)]) 1 :=
    .assignAggregate _ 1 1 _ _ _
      (.mk lm22LargeDecl lm22LargeFields lm22LargePaths _ _ rfl
        (Or.inr ⟨"lm22::LargePadded80", rfl⟩) rfl rfl lm22Large_validStructLayout
        (by decide) rfl rfl (by decide)
        (.cons _ 0 0 1 _ _ trivial
          (.primLeaf (by decide) _ (lm22_constU8_wt 5 (by decide) rfl)
            rfl lm22_u8_prim rfl rfl rfl rfl rfl rfl)
          (.cons _ 1 1 2 _ _ trivial
            (.primLeaf (by decide) _ (lm22_constU32_wt 100 (by decide) rfl)
              rfl lm22_u32_prim rfl rfl rfl rfl rfl rfl)
            (.cons _ 2 2 3 _ [] trivial
              (.primLeaf (by decide) _ (lm22_constU32_wt 200 (by decide) rfl)
                rfl lm22_u32_prim rfl rfl rfl rfl rfl rfl)
              (.nil _ 3)))))
  have ⟨hs2, ha1, hm1⟩ := lm22_trace_step ⟨[1], [0]⟩ (fuel := 4) hs1
    lm22Large_phase rfl rfl hwt1 rfl rfl
  have hwt2 : WellTypedLM2_2Stmt lm22LargeBody lm22LargeEnv ⟨[1], [0]⟩ 1
      (mkStmt22 (.assign ⟨1, [.field 2 lm22U32Ty]⟩ (.use (.constant (lm22ConstU32 999)))))
      (fieldWritePostStaticEnv ⟨[1], [0]⟩ 1 (.constant (lm22ConstU32 999))) 0 :=
    .assignFieldWrite _ 0 1 [.field 2 lm22U32Ty] (.constant (lm22ConstU32 999)) _
      (.mk lm22LargeDecl lm22LargeFields lm22LargePaths 2 rfl rfl (by decide)
        rfl (by decide) (by decide) rfl
        (fun j hj hne => by
          match j with
          | 0 => exact .diff_head (by decide)
          | 1 => exact .diff_head (by decide)
          | 2 => exact False.elim (hne rfl)
          | _ + 3 => simp [lm22LargePaths] at hj; omega)
        (.single (translateTy lm22LargeTy lm22LargeLayoutTable) 2 lm22U32Ty
          (Miri.ABI.Size.ofBytes 68) (Or.inl lm22_u32_prim) rfl rfl (by decide))
        rfl rfl lm22_u32_prim trivial (lm22_constU32_wt 999 (by decide) rfl))
  have ⟨hs3, ha2, hm2⟩ := lm22_trace_step ⟨[1], [0]⟩ (fuel := 3) hs2
    lm22Large_phase rfl rfl hwt2 rfl rfl
  have hwt3 : WellTypedLM2_2Stmt lm22LargeBody lm22LargeEnv ⟨[1], [0]⟩ 0
      (mkStmt22 (.assign ⟨0, []⟩ (.use (.copy ⟨1, [.field 2 lm22U32Ty]⟩))))
      (usePostStaticEnv ⟨[1], [0]⟩ 0 (.copy ⟨1, [.field 2 lm22U32Ty]⟩)) 0 :=
    .assignUse _ 0 0 _ _
      (.mk lm22U32Decl rfl (by decide)
        (.projectedScalar false 1 [.field 2 lm22U32Ty] lm22U32Ty rfl
          (.mk lm22LargeDecl lm22LargeFields lm22LargePaths 2 (by decide) (by decide)
            rfl rfl rfl rfl lm22_u32_prim
            (.single (translateTy lm22LargeTy lm22LargeLayoutTable) 2 lm22U32Ty
              (Miri.ABI.Size.ofBytes 68) (Or.inl lm22_u32_prim) rfl rfl (by decide)))))
  have ⟨hs4, ha3, hm3⟩ := lm22_trace_step ⟨[0, 1], [0, 0]⟩ (fuel := 2) hs3
    lm22Large_phase rfl rfl hwt3 rfl rfl
  have ⟨hs5, ha4, hm4⟩ := lm22_trace_step ⟨[1, 0, 1], [1, 0, 0]⟩ (fuel := 1) hs4
    lm22Large_phase rfl rfl (.storageDead _ 0 1 lm22LargeDecl _ rfl (by decide)) rfl rfl
  have hpad3 :
      ∃ mp localAlloc,
        StructMemPlaceRel
          (lm22StepMiriN lm22LargeBody 3 lm22LargeMiriInit).machine
          lm22LargeTy lm22LargeLayoutTable lm22LargeFields lm22LargePaths
          (.aggregate 0 [.scalar ⟨5, 1⟩, .scalar ⟨100, 4⟩, .scalar ⟨999, 4⟩]) mp ∧
        (∃ allocId,
          (∃ tag, mp.ptr.provenance = some (.concrete allocId tag)) ∧
          (lm22StepMiriN lm22LargeBody 3 lm22LargeMiriInit).machine.memory.live.find?
            (fun (k, _) => k == allocId) = some (allocId, localAlloc)) ∧
        localAlloc.allocation.byteSize = Miri.ABI.Size.ofBytes 80 ∧
        localAlloc.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 1) = .ok false ∧
        localAlloc.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 64) = .ok false ∧
        localAlloc.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 72) = .ok false ∧
        localAlloc.allocation.initializationMask.isRangeInitialized
          (Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 80)) ≠ .ok (.ok ()) := by
    rcases lm22_extract_struct_local hs3 (idx := 1) rfl rfl rfl with ⟨_, himm⟩ | ⟨mp, hsmpr⟩
    · exact False.elim (lm22_not_immediateStructRel_of_memory rfl himm)
    · obtain ⟨p1, p64, p72⟩ := lm22Large_multi_block_padding_bytes
      obtain ⟨allocId, localAlloc, hprov, hfind, hpad_fn, hhas_uninit⟩ :=
        hsmpr.has_uninit_of_padding_byte p1
      have hbs : localAlloc.allocation.byteSize = Miri.ABI.Size.ofBytes 80 := by
        obtain ⟨aid, tag, b, la, hprov', hfind', hbs⟩ := StructMemPlaceRel.byteSize_eq hsmpr
        obtain ⟨tag, hprov_eq⟩ := hprov; cases Option.some.inj (hprov_eq.symm.trans hprov')
        cases Option.some.inj (hfind.symm.trans hfind')
        exact hbs
      exact ⟨mp, localAlloc, hsmpr, ⟨allocId, hprov, hfind⟩, hbs,
        hpad_fn 1 p1, hpad_fn 64 p64, hpad_fn 72 p72, hhas_uninit⟩
  have hbase5 : StateRel lm22LargeBody
      (lm22StepAnnealN lm22LargeBody 5 (initMachineState lm22LargeBody []))
      (lm22StepMiriN lm22LargeBody 5 lm22LargeMiriInit) := by
    refine hs5.toStateRel_of_flat_imm (by rintro ⟨_, _⟩ _ _ h _ _ ⟨⟩; cases h) (fun i _ _ _ _ hdecl henv hslot _ => ?_) ?hunpad
    case hunpad =>
      intro i _ _ _ _ _ _ hdecl henv hslot _
      match i with
      | 0 => cases Option.some.inj hdecl; cases henv
      | 1 =>
        have hdead :
            get? (lm22StepAnnealN lm22LargeBody 5 (initMachineState lm22LargeBody [])).frame.locals 1 =
              some .dead := rfl
        rw [hdead] at hslot; cases hslot
      | _ + 2 => simp [lm22LargeBody, get?] at hdecl
    match i with
    | 0 => cases Option.some.inj hdecl; exact False.elim (henv rfl)
    | 1 =>
      have hdead :
          get? (lm22StepAnnealN lm22LargeBody 5 (initMachineState lm22LargeBody [])).frame.locals 1 =
            some .dead := rfl
      rw [hdead] at hslot; cases hslot
    | _ + 2 => simp [lm22LargeBody, get?] at hdecl
  have himm0_5 := lm22_imm_of_mem_immLocals hs5 (idx := 0) (by decide)
  obtain ⟨ha_ret, hm_ret⟩ := lm22_return_agree_of_stateRel hbase5 lm22Large_phase
    rfl rfl rfl rfl rfl rfl lm22_u32_prim himm0_5 rfl
  have ha_tot :
      runAnnealBounded lm22LargeBody 6 (initMachineState lm22LargeBody []) =
        runAnnealBounded lm22LargeBody 1
          (lm22StepAnnealN lm22LargeBody 5 (initMachineState lm22LargeBody [])) :=
    ha0.trans (ha1.trans (ha2.trans (ha3.trans ha4)))
  have hm_tot :
      runMiriBoundedLM2_2 lm22LargeBody 6 lm22LargeMiriInit =
        runMiriBoundedLM2_2 lm22LargeBody 1 (lm22StepMiriN lm22LargeBody 5 lm22LargeMiriInit) :=
    hm0.trans (hm1.trans (hm2.trans (hm3.trans hm4)))
  rw [ha_tot, hm_tot]
  exact ⟨hpad3, ha_ret, hm_ret⟩


/-! ## 8. Root `Return` While a Padded Struct Is Still Live in Memory (`lm22LiveRetBody`)

The padded body of section 3 without the final `StorageDead(_1)`: the function
returns while `_1 : PaddedOuter` is live in a stack allocation whose padding
bytes `1, 2, 3` are uninitialized. Base `LocalRel.indirect` requires the whole
byte range of an initialized memory-backed local to be initialized, so the base
`StateRel` cannot relate that state; the return is simulated directly from
`StateRelLM2_2` by `step_terminator_return_lm2_2_simulation`. -/

/-- Root-frame `return` agreement from `StateRelLM2_2` via
`step_terminator_return_lm2_2_simulation`, without projecting to base `StateRel`. -/
theorem lm22_return_agree_of_stateRelLM2_2
    {body : CapturedMir} {env : StructTypeEnv} {stEnv : LM2_2StaticEnv} {k : Nat}
    {s : MachineState} {m : AnnealStepState}
    {bb : BasicBlockData} {decl0 : LocalDecl}
    {bits sz : Nat} {mem' : Memory}
    (hstate : StateRelLM2_2 body env stEnv k s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    (hstmt_len : s.frame.stmtIdx = length bb.statements)
    (hcleanup : bb.isCleanup = false)
    (hret : bb.terminator.kind = .return_)
    (hdecl0 : get? body.localDecls 0 = some decl0)
    (henv0 : env decl0.ty = none)
    (hprim0 : IsPrimScalarTy decl0.ty)
    (himm0 : 0 ∈ stEnv.immLocals)
    (ha : stepMirFn body s = .retNormal (.scalar ⟨bits, sz⟩) mem') :
    annealOutcomeScalarBits sz (runAnnealBounded body 1 s) = some bits ∧
    miriOutcomeScalarBits sz (runMiriBoundedLM2_2 body 1 m) = some bits := by
  have hsim := step_terminator_return_lm2_2_simulation hstate hphase hbb hstmt_none
    hstmt_len hcleanup hret hdecl0 henv0 hprim0.size_ne_zero himm0
  have ha_out : annealOutcomeScalarBits sz (runAnnealBounded body 1 s) = some bits := by
    unfold runAnnealBounded annealOutcomeScalarBits
    rw [ha]
    dsimp only [MirStepNode.retNormal]
    simp
  refine ⟨ha_out, ?_⟩
  rw [ha] at hsim
  generalize hm : Miri.Interpreter.Step.step (annealStepHooksLM2_2 body.localDecls body.layouts) () m = r
    at hsim
  cases hsim with
  | retRoot decl0' _ imm0 _ m' hdecl0' hretOp himmRel hm'_eq =>
    have hd_eq := Option.some.inj (hdecl0.symm.trans hdecl0')
    subst hd_eq
    obtain ⟨sc, msc, hsc_eq, rfl, hrel, _, _, _⟩ := himmRel.of_primitive_scalar hprim0
    injection hsc_eq with hsc_eq'
    cases hsc_eq'
    rcases hrel with ⟨hvb, hcan, hsz_r, hdata_r⟩
    have hemp : m'.stack.frames.isEmpty = true := by rw [hm'_eq]; rfl
    have hm_out : runMiriBoundedLM2_2 body 1 m =
        .returned m' (.ok (.immediate (.scalar (.fromScalarInt msc)))) := by
      unfold runMiriBoundedLM2_2
      rw [hm]; dsimp only; rw [hemp, hretOp]; rfl
    rw [hm_out]
    unfold miriOutcomeScalarBits
    have hto : (Miri.Memory.Scalar.fromScalarInt msc : Miri.Memory.Scalar AnnealProv).toScalarInt =
        .ok msc := rfl
    have hsz_eq : (msc.size == Miri.ABI.Size.ofBytes (UInt64.ofNat sz)) = true := by
      rw [hsz_r]; dsimp only
      rcases hvb with rfl | rfl | rfl | rfl | rfl <;> decide
    have hlt128 : bits < 2 ^ 128 := by
      dsimp only at hvb hcan
      rw [scalarModulus_eq_two_pow] at hcan
      rcases hvb with rfl | rfl | rfl | rfl | rfl <;> omega
    have hbits_eq : msc.data.toNat = bits := by
      rw [hdata_r]; dsimp only
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt128]
    simp only [hemp, ↓reduceIte, hto, hsz_eq, hbits_eq]

def lm22LiveRetBody : CapturedMir where
  defPath := "lm_2_2_witness::padded_outer_live_at_return"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [lm22U32Decl, lm22PaddedDecl, lm22InnerU32Decl]
  basicBlocks := [
    { statements := [
        mkStmt22 (.storageLive 1),
        mkStmt22 (.storageLive 2),
        mkStmt22 (.assign ⟨2, []⟩
          (.aggregate (.adt "lm22::InnerU32" 0 .none) [.constant (lm22ConstU32 42)])),
        mkStmt22 (.assign ⟨1, []⟩
          (.aggregate (.adt "lm22::PaddedOuter" 0 .none)
            [.constant (constU8 7), .move ⟨2, []⟩])),
        mkStmt22 (.assign ⟨1, [.field 1 lm22InnerU32Ty, .field 0 lm22U32Ty]⟩
          (.use (.constant (lm22ConstU32 99)))),
        mkStmt22 (.assign ⟨0, []⟩
          (.use (.copy ⟨1, [.field 1 lm22InnerU32Ty, .field 0 lm22U32Ty]⟩))),
        mkStmt22 (.storageDead 2)],
      terminator := mkTerm22 .return_,
      isCleanup := false }]
  fnAbi := lm22FnAbiU32
  layouts := lm22PaddedLayoutTable
  allocations := []

def lm22LiveRetMiriInit : AnnealStepState :=
  { stack := ⟨#[{
      body := translateBody lm22LiveRetBody
      bodyIdentity := .ofCanonicalIndex 0
      functionInstance := { kind := .Item 0, args := #[] }
      extra := ()
      returnContinuation := .stop false
      returnPlace :=
        .frameLocal 0 0 none (translateTy lm22U32Ty lm22PaddedLayoutTable) (.ofAllocationToken 0)
      localsIdentity := .ofAllocationToken 0
      locals := #[
        { value := .live (.immediate .uninit), layout := none },
        { value := .dead, layout := none },
        { value := .dead, layout := none }]
      vaList := #[]
      trackCallerArg := none
      location := .mir ⟨0, 0⟩ }]⟩
    machine := AnnealMachine.empty }

theorem lm22LiveRet_phase : ∀ p, lm22LiveRetBody.phase ≠ .other p := by
  intro p h; cases h

theorem lm22LiveRet_stateRelLM2_2_init :
    StateRelLM2_2 lm22LiveRetBody lm22PaddedEnv { initLocals := [], immLocals := [0] } 3
      (initMachineState lm22LiveRetBody []) lm22LiveRetMiriInit := by
  refine .mk _ rfl rfl ⟨translateTy lm22U32Ty lm22PaddedLayoutTable, rfl⟩ ?_
    (fun _ h => nomatch h)
    (fun j hj mp l => by simp at hj; subst hj; dsimp [lm22LiveRetMiriInit]; nofun)
    (Or.inr (AllocIdWatermark.empty 3 (by decide))) rfl rfl rfl rfl rfl
    (by intro i _ _ _ _ _ _ hi _; revert hi; match i with | 0 | 1 | 2 | _ + 3 => rintro ⟨⟩)
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro i decl slot mls hdecl hslot hmls
  match i with
  | 0 =>
    cases Option.some.inj hdecl
    cases Option.some.inj hslot
    cases Option.some.inj hmls
    exact .base .uninit _ rfl (.immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩))
  | 1 =>
    cases Option.some.inj hdecl
    cases Option.some.inj hslot
    cases Option.some.inj hmls
    exact .structDead lm22PaddedFields lm22PaddedPaths none rfl (fun _ h => nomatch h)
  | 2 =>
    cases Option.some.inj hdecl
    cases Option.some.inj hslot
    cases Option.some.inj hmls
    exact .structDead [lm22InnerU32Field0] [[.field 0 lm22U32Ty]] none rfl (fun _ h => nomatch h)
  | _ + 3 => simp [lm22LiveRetBody, get?] at hdecl

/-- `lm22LiveRetBody` runs in lockstep and returns `99_u32` on both sides while
`_1 : PaddedOuter` is still live in memory with uninitialized padding:
1. right before `return`, `_1` holds `(7, InnerU32(99))` under `StructMemPlaceRel`
   and padding byte `1` is uninitialized;
2. `StateRelLM2_2` relates the pre-return states;
3. `step_terminator_return_lm2_2_simulation` yields return agreement. -/
theorem lm22LiveRet_full_trace_and_returns_agree :
    (∃ mp localAlloc,
      StructMemPlaceRel
        (lm22StepMiriN lm22LiveRetBody 7 lm22LiveRetMiriInit).machine
        lm22PaddedTy lm22PaddedLayoutTable lm22PaddedFields lm22PaddedPaths
        (.aggregate 0 [.scalar ⟨7, 1⟩, .aggregate 0 [.scalar ⟨99, 4⟩]]) mp ∧
      (∃ allocId,
        (∃ tag, mp.ptr.provenance = some (.concrete allocId tag)) ∧
        (lm22StepMiriN lm22LiveRetBody 7 lm22LiveRetMiriInit).machine.memory.live.find?
          (fun (k, _) => k == allocId) = some (allocId, localAlloc)) ∧
      localAlloc.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 1) = .ok false) ∧
    StateRelLM2_2 lm22LiveRetBody lm22PaddedEnv
      { initLocals := [2, 0, 1], immLocals := [2, 0, 2, 0] } 0
      (lm22StepAnnealN lm22LiveRetBody 7 (initMachineState lm22LiveRetBody []))
      (lm22StepMiriN lm22LiveRetBody 7 lm22LiveRetMiriInit) ∧
    annealOutcomeScalarBits 4
      (runAnnealBounded lm22LiveRetBody 8 (initMachineState lm22LiveRetBody [])) = some 99 ∧
    miriOutcomeScalarBits 4
      (runMiriBoundedLM2_2 lm22LiveRetBody 8 lm22LiveRetMiriInit) = some 99 := by
  have hs0 : StateRelLM2_2 lm22LiveRetBody lm22PaddedEnv { initLocals := [], immLocals := [0] } 3
      (lm22StepAnnealN lm22LiveRetBody 0 (initMachineState lm22LiveRetBody []))
      (lm22StepMiriN lm22LiveRetBody 0 lm22LiveRetMiriInit) :=
    lm22LiveRet_stateRelLM2_2_init
  have ⟨hs1, ha0, hm0⟩ := lm22_trace_step ⟨[], [1, 0]⟩ (fuel := 7) hs0
    lm22LiveRet_phase rfl rfl (.storageLive _ 3 1 lm22PaddedDecl _ rfl) rfl rfl
  have ⟨hs2, ha1, hm1⟩ := lm22_trace_step ⟨[], [2, 1, 0]⟩ (fuel := 6) hs1
    lm22LiveRet_phase rfl rfl (.storageLive _ 3 2 lm22InnerU32Decl _ rfl) rfl rfl
  have hwt2 : WellTypedLM2_2Stmt lm22LiveRetBody lm22PaddedEnv ⟨[], [2, 1, 0]⟩ 3
      (mkStmt22 (.assign ⟨2, []⟩
        (.aggregate (.adt "lm22::InnerU32" 0 .none) [.constant (lm22ConstU32 42)])))
      (aggPostStaticEnv ⟨[], [2, 1, 0]⟩ 2 [.constant (lm22ConstU32 42)]) 2 :=
    .assignAggregate _ 2 2 _ _ _
      (.mk lm22InnerU32Decl [lm22InnerU32Field0] [[.field 0 lm22U32Ty]] _ [] rfl
        (Or.inr ⟨"lm22::InnerU32", rfl⟩) rfl rfl lm22InnerU32_validStructLayout
        (by decide) rfl rfl (by decide)
        (.cons _ 0 0 1 _ [] trivial
          (.primLeaf (by decide) _ (lm22_constU32_wt 42 (by decide) rfl)
            rfl lm22_u32_prim rfl rfl rfl rfl rfl rfl)
          (.nil _ 1)))
  have ⟨hs3, ha2, hm2⟩ := lm22_trace_step ⟨[2], [1, 0]⟩ (fuel := 5) hs2
    lm22LiveRet_phase rfl rfl hwt2 rfl rfl
  have hwt3 : WellTypedLM2_2Stmt lm22LiveRetBody lm22PaddedEnv ⟨[2], [1, 0]⟩ 2
      (mkStmt22 (.assign ⟨1, []⟩
        (.aggregate (.adt "lm22::PaddedOuter" 0 .none)
          [.constant (constU8 7), .move ⟨2, []⟩])))
      (aggPostStaticEnv ⟨[2], [1, 0]⟩ 1 [.constant (constU8 7), .move ⟨2, []⟩]) 1 :=
    .assignAggregate _ 1 1 _ _ _
      (.mk lm22PaddedDecl lm22PaddedFields lm22PaddedPaths _ _ rfl
        (Or.inr ⟨"lm22::PaddedOuter", rfl⟩) rfl rfl lm22Padded_validStructLayout
        (by decide) rfl rfl (by decide)
        (.cons _ 0 0 1 _ _ trivial
          (.primLeaf (by decide) _ (lm22_constU8_wt 7 (by decide) rfl)
            rfl lm22_u8_prim rfl rfl rfl rfl rfl rfl)
          (.cons _ 1 1 2 (.move ⟨2, []⟩) [] (by decide : (2 : Nat) ≠ 1)
            (.scalarWrapSub (by decide) lm22InnerU32Ty lm22InnerU32Field0
              [.field 0 lm22U32Ty] _
              (.immStructLocal true 2 lm22InnerU32Decl [lm22InnerU32Field0]
                [[.field 0 lm22U32Ty]] rfl lm22InnerU32_isImmediateStructTy)
              lm22InnerU32_isImmediateStructTy rfl rfl rfl rfl rfl rfl rfl)
            (.nil _ 2))))
  have ⟨hs4, ha3, hm3⟩ := lm22_trace_step ⟨[1], [2, 0]⟩ (fuel := 4) hs3
    lm22LiveRet_phase rfl rfl hwt3 rfl rfl
  have hwt4 : WellTypedLM2_2Stmt lm22LiveRetBody lm22PaddedEnv ⟨[1], [2, 0]⟩ 1
      (mkStmt22 (.assign ⟨1, [.field 1 lm22InnerU32Ty, .field 0 lm22U32Ty]⟩
        (.use (.constant (lm22ConstU32 99)))))
      (fieldWritePostStaticEnv ⟨[1], [2, 0]⟩ 1 (.constant (lm22ConstU32 99))) 0 :=
    .assignFieldWrite _ 0 1 [.field 1 lm22InnerU32Ty, .field 0 lm22U32Ty]
      (.constant (lm22ConstU32 99)) _
      (.mk lm22PaddedDecl lm22PaddedFields lm22PaddedPaths 1 rfl rfl (by decide)
        rfl (by decide) (by decide) rfl
        (fun j hj hne => by
          match j with
          | 0 => exact .diff_head (by decide)
          | 1 => exact False.elim (hne rfl)
          | _ + 2 => simp [lm22PaddedPaths] at hj; omega)
        lm22Padded_projChain_inner0
        rfl rfl lm22_u32_prim trivial (lm22_constU32_wt 99 (by decide) rfl))
  have ⟨hs5, ha4, hm4⟩ := lm22_trace_step ⟨[1], [2, 0]⟩ (fuel := 3) hs4
    lm22LiveRet_phase rfl rfl hwt4 rfl rfl
  have hwt5 : WellTypedLM2_2Stmt lm22LiveRetBody lm22PaddedEnv ⟨[1], [2, 0]⟩ 0
      (mkStmt22 (.assign ⟨0, []⟩
        (.use (.copy ⟨1, [.field 1 lm22InnerU32Ty, .field 0 lm22U32Ty]⟩))))
      (usePostStaticEnv ⟨[1], [2, 0]⟩ 0
        (.copy ⟨1, [.field 1 lm22InnerU32Ty, .field 0 lm22U32Ty]⟩)) 0 :=
    .assignUse _ 0 0 _ _
      (.mk lm22U32Decl rfl (by decide)
        (.projectedScalar false 1 [.field 1 lm22InnerU32Ty, .field 0 lm22U32Ty]
          lm22U32Ty rfl
          (.mk lm22PaddedDecl lm22PaddedFields lm22PaddedPaths 1 (by decide) (by decide)
            rfl rfl rfl rfl lm22_u32_prim lm22Padded_projChain_inner0)))
  have ⟨hs6, ha5, hm5⟩ := lm22_trace_step ⟨[0, 1], [0, 2, 0]⟩ (fuel := 2) hs5
    lm22LiveRet_phase rfl rfl hwt5 rfl rfl
  have ⟨hs7, ha6, hm6⟩ := lm22_trace_step ⟨[2, 0, 1], [2, 0, 2, 0]⟩ (fuel := 1) hs6
    lm22LiveRet_phase rfl rfl (.storageDead _ 0 2 lm22InnerU32Decl _ rfl (by decide)) rfl rfl
  have hpad7 :
      ∃ mp localAlloc,
        StructMemPlaceRel
          (lm22StepMiriN lm22LiveRetBody 7 lm22LiveRetMiriInit).machine
          lm22PaddedTy lm22PaddedLayoutTable lm22PaddedFields lm22PaddedPaths
          (.aggregate 0 [.scalar ⟨7, 1⟩, .aggregate 0 [.scalar ⟨99, 4⟩]]) mp ∧
        (∃ allocId,
          (∃ tag, mp.ptr.provenance = some (.concrete allocId tag)) ∧
          (lm22StepMiriN lm22LiveRetBody 7 lm22LiveRetMiriInit).machine.memory.live.find?
            (fun (k, _) => k == allocId) = some (allocId, localAlloc)) ∧
        localAlloc.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 1) = .ok false := by
    rcases lm22_extract_struct_local hs7 (idx := 1) rfl rfl rfl with ⟨_, himm⟩ | ⟨mp, hsmpr⟩
    · exact False.elim (lm22_not_immediateStructRel_of_memory rfl himm)
    · obtain ⟨allocId, localAlloc, hprov, hfind, hpad_fn, _⟩ :=
        hsmpr.has_uninit_of_padding_byte lm22Padded_interfield_padding_bytes.1
      exact ⟨mp, localAlloc, hsmpr, ⟨allocId, hprov, hfind⟩,
        hpad_fn 1 lm22Padded_interfield_padding_bytes.1⟩
  obtain ⟨ha_ret, hm_ret⟩ := lm22_return_agree_of_stateRelLM2_2 hs7 lm22LiveRet_phase
    rfl rfl rfl rfl rfl rfl rfl lm22_u32_prim (by decide) rfl
  have ha_tot :
      runAnnealBounded lm22LiveRetBody 8 (initMachineState lm22LiveRetBody []) =
        runAnnealBounded lm22LiveRetBody 1
          (lm22StepAnnealN lm22LiveRetBody 7 (initMachineState lm22LiveRetBody [])) :=
    ha0.trans (ha1.trans (ha2.trans (ha3.trans (ha4.trans (ha5.trans ha6)))))
  have hm_tot :
      runMiriBoundedLM2_2 lm22LiveRetBody 8 lm22LiveRetMiriInit =
        runMiriBoundedLM2_2 lm22LiveRetBody 1 (lm22StepMiriN lm22LiveRetBody 7 lm22LiveRetMiriInit) :=
    hm0.trans (hm1.trans (hm2.trans (hm3.trans (hm4.trans (hm5.trans hm6)))))
  rw [ha_tot, hm_tot]
  exact ⟨hpad7, hs7, ha_ret, hm_ret⟩


/-! ## 9. Whole-Value Move & Copy of Padded `.Memory` Struct `NestedOuter` (`_3 = move _2`, `_4 = copy _3`)

Exercises both paths of `annealStructMemCopyOp` and
`step_assign_use_memory_struct_lm2_2_simulation`:
1. `_3 = move _2` into an uninitialized immediate `.Memory` local `_3` forces a
   fresh stack allocation (`StructMemPlaceRel.of_copy_fresh`), copies all 12
   bytes and `InitMask`, marks `_2` `.uninit`, and preserves all five alignment
   padding bytes (`1, 2, 3, 10, 11`) as `.uninit` in `_3`'s `InitMask`;
2. `_4 = copy _3` into an already-allocated indirect `.Memory` local `_4`
   overwrites `_4`'s disjoint stack allocation (`StructMemPlaceRel.of_copy_overwrite`),
   preserving all five alignment padding bytes (`1, 2, 3, 10, 11`) as `.uninit`
   while leaving `_3` initialized. -/

def lm22MemMoveBody : CapturedMir where
  defPath := "lm_2_2_witness::nested_memory_move_and_copy"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls :=
    [u16Decl, lm22InnerPairDecl, lm22NestedDecl, lm22NestedDecl, lm22NestedDecl]
  basicBlocks := [
    { statements := [
        mkStmt22 (.storageLive 1),
        mkStmt22 (.storageLive 2),
        mkStmt22 (.storageLive 3),
        mkStmt22 (.storageLive 4),
        mkStmt22 (.assign ⟨1, []⟩
          (.aggregate (.adt "lm22::InnerPair" 0 .none)
            [.constant (lm22ConstU32 0x11112222), .constant (constU16 0x3344)])),
        mkStmt22 (.assign ⟨2, []⟩
          (.aggregate (.adt "lm22::NestedOuter" 0 .none)
            [.constant (constU8 7), .move ⟨1, []⟩])),
        mkStmt22 (.assign ⟨3, []⟩ (.use (.move ⟨2, []⟩))),
        mkStmt22 (.assign ⟨1, []⟩
          (.aggregate (.adt "lm22::InnerPair" 0 .none)
            [.constant (lm22ConstU32 0xAAAABBBB), .constant (constU16 0xCCCC)])),
        mkStmt22 (.assign ⟨4, []⟩
          (.aggregate (.adt "lm22::NestedOuter" 0 .none)
            [.constant (constU8 9), .move ⟨1, []⟩])),
        mkStmt22 (.assign ⟨4, []⟩ (.use (.copy ⟨3, []⟩))),
        mkStmt22 (.assign ⟨0, []⟩
          (.use (.copy ⟨4, [.field 1 lm22InnerPairTy, .field 1 u16Ty]⟩))),
        mkStmt22 (.storageDead 4),
        mkStmt22 (.storageDead 3),
        mkStmt22 (.storageDead 2),
        mkStmt22 (.storageDead 1)],
      terminator := mkTerm22 .return_,
      isCleanup := false }]
  fnAbi := lm22FnAbiU16
  layouts := lm22NestedLayoutTable
  allocations := []

def lm22MemMoveMiriInit : AnnealStepState :=
  { stack := ⟨#[{
      body := translateBody lm22MemMoveBody
      bodyIdentity := .ofCanonicalIndex 0
      functionInstance := { kind := .Item 0, args := #[] }
      extra := ()
      returnContinuation := .stop false
      returnPlace :=
        .frameLocal 0 0 none (translateTy u16Ty lm22NestedLayoutTable) (.ofAllocationToken 0)
      localsIdentity := .ofAllocationToken 0
      locals := #[
        { value := .live (.immediate .uninit), layout := none },
        { value := .dead, layout := none },
        { value := .dead, layout := none },
        { value := .dead, layout := none },
        { value := .dead, layout := none }]
      vaList := #[]
      trackCallerArg := none
      location := .mir ⟨0, 0⟩ }]⟩
    machine := AnnealMachine.empty }

theorem lm22MemMove_phase : ∀ p, lm22MemMoveBody.phase ≠ .other p := by
  intro p h; cases h

theorem lm22MemMove_stateRelLM2_2_init :
    StateRelLM2_2 lm22MemMoveBody lm22NestedEnv { initLocals := [], immLocals := [0] } 6
      (initMachineState lm22MemMoveBody []) lm22MemMoveMiriInit := by
  refine .mk _ rfl rfl ⟨translateTy u16Ty lm22NestedLayoutTable, rfl⟩ ?_
    (fun _ h => nomatch h)
    (fun j hj mp l => by simp at hj; subst hj; dsimp [lm22MemMoveMiriInit]; nofun)
    (Or.inr (AllocIdWatermark.empty 6 (by decide))) rfl rfl rfl rfl rfl
    (by intro i _ _ _ _ _ _ hi _; revert hi
        match i with | 0 | 1 | 2 | 3 | 4 | _ + 5 => rintro ⟨⟩)
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro i decl slot mls hdecl hslot hmls
  match i with
  | 0 =>
    cases Option.some.inj hdecl
    cases Option.some.inj hslot
    cases Option.some.inj hmls
    exact .base .uninit _ rfl (.immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩))
  | 1 =>
    cases Option.some.inj hdecl
    cases Option.some.inj hslot
    cases Option.some.inj hmls
    exact .structDead lm22InnerPairFields lm22InnerPairPaths none rfl (fun _ h => nomatch h)
  | 2 | 3 | 4 =>
    cases Option.some.inj hdecl
    cases Option.some.inj hslot
    cases Option.some.inj hmls
    exact .structDead lm22NestedFields lm22NestedPaths none rfl (fun _ h => nomatch h)
  | _ + 5 => simp [lm22MemMoveBody, get?] at hdecl

theorem lm22MemMove_pair_agg_wt (stEnv : LM2_2StaticEnv) (k a b : Nat)
    (ha : a < 4294967296) (hb : b < 65536) :
    WellTypedLM2_2Stmt lm22MemMoveBody lm22NestedEnv stEnv (k + 1)
      (mkStmt22 (.assign ⟨1, []⟩
        (.aggregate (.adt "lm22::InnerPair" 0 .none)
          [.constant (lm22ConstU32 a), .constant (constU16 b)])))
      (aggPostStaticEnv stEnv 1 [.constant (lm22ConstU32 a), .constant (constU16 b)]) k :=
  .assignAggregate stEnv k 1 _ _ _
    (.mk lm22InnerPairDecl lm22InnerPairFields lm22InnerPairPaths _ _ rfl
      (Or.inr ⟨"lm22::InnerPair", rfl⟩) rfl rfl lm22InnerPair_validStructLayout
      (by decide) rfl rfl (by decide)
      (.cons _ 0 0 1 _ _ trivial
        (.primLeaf (by decide) _ (lm22_constU32_wt a ha rfl)
          rfl lm22_u32_prim rfl rfl rfl rfl rfl rfl)
        (.cons _ 1 1 2 _ [] trivial
          (.primLeaf (by decide) _ (lm22_constU16_wt b hb rfl)
            rfl lm22_u16_prim rfl rfl rfl rfl rfl rfl)
          (.nil _ 2))))

theorem lm22MemMove_outer_agg_wt (stEnv : LM2_2StaticEnv) (k dst tag : Nat)
    (hdst : get? lm22MemMoveBody.localDecls dst = some lm22NestedDecl)
    (hne : (1 : Nat) ≠ dst) (htag : tag < 256) :
    WellTypedLM2_2Stmt lm22MemMoveBody lm22NestedEnv stEnv (k + 1)
      (mkStmt22 (.assign ⟨dst, []⟩
        (.aggregate (.adt "lm22::NestedOuter" 0 .none)
          [.constant (constU8 tag), .move ⟨1, []⟩])))
      (aggPostStaticEnv stEnv dst [.constant (constU8 tag), .move ⟨1, []⟩]) k :=
  .assignAggregate stEnv k dst _ _ _
    (.mk lm22NestedDecl lm22NestedFields lm22NestedPaths _ _ rfl
      (Or.inr ⟨"lm22::NestedOuter", rfl⟩) hdst rfl lm22Nested_validStructLayout
      (by decide) rfl rfl (by decide)
      (.cons _ 0 0 1 _ _ trivial
        (.primLeaf (by decide) _ (lm22_constU8_wt tag htag rfl)
          rfl lm22_u8_prim rfl rfl rfl rfl rfl rfl)
        (.cons _ 1 1 3 (.move ⟨1, []⟩) [] hne
          (.scalarPairSub (by decide) lm22InnerPairTy lm22InnerPairField0 lm22InnerPairField1
            lm22U32Ty u16Ty [] [] _ _ _ (Miri.ABI.Size.ofBytes 4)
            (.immStructLocal true 1 lm22InnerPairDecl lm22InnerPairFields
              lm22InnerPairPaths rfl lm22InnerPair_isImmediateStructTy)
            lm22InnerPair_isImmediateStructTy
            rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide))
          (.nil _ 2))))

theorem lm22MemMove_move2to3_wt (stEnv : LM2_2StaticEnv) (k : Nat)
    (h2_init : 2 ∈ stEnv.initLocals) :
    WellTypedLM2_2Stmt lm22MemMoveBody lm22NestedEnv stEnv (k + 1)
      (mkStmt22 (.assign ⟨3, []⟩ (.use (.move ⟨2, []⟩))))
      (useStructPostStaticEnv stEnv 3 (.move ⟨2, []⟩)) k :=
  .assignUseMemStruct stEnv k 3 true 2 _
    (.mk lm22NestedDecl lm22NestedDecl lm22NestedFields lm22NestedPaths _ _
      (by decide) rfl rfl rfl rfl (Or.inl h2_init) rfl rfl (by decide) (by decide) rfl (by decide))

theorem lm22MemMove_copy3to4_wt (stEnv : LM2_2StaticEnv) (k : Nat)
    (h3_init : 3 ∈ stEnv.initLocals) :
    WellTypedLM2_2Stmt lm22MemMoveBody lm22NestedEnv stEnv (k + 1)
      (mkStmt22 (.assign ⟨4, []⟩ (.use (.copy ⟨3, []⟩))))
      (useStructPostStaticEnv stEnv 4 (.copy ⟨3, []⟩)) k :=
  .assignUseMemStruct stEnv k 4 false 3 _
    (.mk lm22NestedDecl lm22NestedDecl lm22NestedFields lm22NestedPaths _ _
      (by decide) rfl rfl rfl rfl (Or.inl h3_init) rfl rfl (by decide) (by decide) rfl (by decide))

theorem lm22MemMove_full_trace_and_returns_agree :
    (get? (lm22StepAnnealN lm22MemMoveBody 7 (initMachineState lm22MemMoveBody [])).frame.locals 2 =
      some .uninit ∧
     ∃ mp3 alloc3,
      StructMemPlaceRel
        (lm22StepMiriN lm22MemMoveBody 7 lm22MemMoveMiriInit).machine
        lm22NestedTy lm22NestedLayoutTable lm22NestedFields lm22NestedPaths
        (.aggregate 0 [.scalar ⟨7, 1⟩, .aggregate 0 [.scalar ⟨0x11112222, 4⟩, .scalar ⟨0x3344, 2⟩]]) mp3 ∧
      (∃ allocId3,
        (∃ tag, mp3.ptr.provenance = some (.concrete allocId3 tag)) ∧
        (lm22StepMiriN lm22MemMoveBody 7 lm22MemMoveMiriInit).machine.memory.live.find?
          (fun (k, _) => k == allocId3) = some (allocId3, alloc3)) ∧
      alloc3.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 1) = .ok false ∧
      alloc3.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 2) = .ok false ∧
      alloc3.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 3) = .ok false ∧
      alloc3.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 10) = .ok false ∧
      alloc3.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 11) = .ok false) ∧
    (∃ mp4 alloc4,
      StructMemPlaceRel
        (lm22StepMiriN lm22MemMoveBody 10 lm22MemMoveMiriInit).machine
        lm22NestedTy lm22NestedLayoutTable lm22NestedFields lm22NestedPaths
        (.aggregate 0 [.scalar ⟨7, 1⟩, .aggregate 0 [.scalar ⟨0x11112222, 4⟩, .scalar ⟨0x3344, 2⟩]]) mp4 ∧
      (∃ allocId4,
        (∃ tag, mp4.ptr.provenance = some (.concrete allocId4 tag)) ∧
        (lm22StepMiriN lm22MemMoveBody 10 lm22MemMoveMiriInit).machine.memory.live.find?
          (fun (k, _) => k == allocId4) = some (allocId4, alloc4)) ∧
      alloc4.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 1) = .ok false ∧
      alloc4.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 2) = .ok false ∧
      alloc4.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 3) = .ok false ∧
      alloc4.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 10) = .ok false ∧
      alloc4.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 11) = .ok false) ∧
    annealOutcomeScalarBits 2
      (runAnnealBounded lm22MemMoveBody 16 (initMachineState lm22MemMoveBody [])) = some 0x3344 ∧
    miriOutcomeScalarBits 2
      (runMiriBoundedLM2_2 lm22MemMoveBody 16 lm22MemMoveMiriInit) = some 0x3344 := by
  have hs0 : StateRelLM2_2 lm22MemMoveBody lm22NestedEnv { initLocals := [], immLocals := [0] } 6
      (lm22StepAnnealN lm22MemMoveBody 0 (initMachineState lm22MemMoveBody []))
      (lm22StepMiriN lm22MemMoveBody 0 lm22MemMoveMiriInit) :=
    lm22MemMove_stateRelLM2_2_init
  have ⟨hs1, ha0, hm0⟩ := lm22_trace_step ⟨[], [1, 0]⟩ (fuel := 15) hs0
    lm22MemMove_phase rfl rfl (.storageLive _ 6 1 lm22InnerPairDecl _ rfl) rfl rfl
  have ⟨hs2, ha1, hm1⟩ := lm22_trace_step ⟨[], [2, 1, 0]⟩ (fuel := 14) hs1
    lm22MemMove_phase rfl rfl (.storageLive _ 6 2 lm22NestedDecl _ rfl) rfl rfl
  have ⟨hs3, ha2, hm2⟩ := lm22_trace_step ⟨[], [3, 2, 1, 0]⟩ (fuel := 13) hs2
    lm22MemMove_phase rfl rfl (.storageLive _ 6 3 lm22NestedDecl _ rfl) rfl rfl
  have ⟨hs4, ha3, hm3⟩ := lm22_trace_step ⟨[], [4, 3, 2, 1, 0]⟩ (fuel := 12) hs3
    lm22MemMove_phase rfl rfl (.storageLive _ 6 4 lm22NestedDecl _ rfl) rfl rfl
  have ⟨hs5, ha4, hm4⟩ := lm22_trace_step ⟨[1], [4, 3, 2, 0]⟩ (fuel := 11) hs4
    lm22MemMove_phase rfl rfl
    (lm22MemMove_pair_agg_wt _ 5 0x11112222 0x3344 (by decide) (by decide)) rfl rfl
  have ⟨hs6, ha5, hm5⟩ := lm22_trace_step ⟨[2], [1, 4, 3, 0]⟩ (fuel := 10) hs5
    lm22MemMove_phase rfl rfl
    (lm22MemMove_outer_agg_wt _ 4 2 7 rfl (by decide) (by decide)) rfl rfl
  have ⟨hs7, ha6, hm6⟩ := lm22_trace_step ⟨[3], [2, 1, 4, 0]⟩ (fuel := 9) hs6
    lm22MemMove_phase rfl rfl (lm22MemMove_move2to3_wt _ 3 (by decide)) rfl rfl
  have ⟨hs8, ha7, hm7⟩ := lm22_trace_step ⟨[1, 3], [2, 4, 0]⟩ (fuel := 8) hs7
    lm22MemMove_phase rfl rfl
    (lm22MemMove_pair_agg_wt _ 2 0xAAAABBBB 0xCCCC (by decide) (by decide)) rfl rfl
  have ⟨hs9, ha8, hm8⟩ := lm22_trace_step ⟨[4, 3], [1, 2, 0]⟩ (fuel := 7) hs8
    lm22MemMove_phase rfl rfl
    (lm22MemMove_outer_agg_wt _ 1 4 9 rfl (by decide) (by decide)) rfl rfl
  have ⟨hs10, ha9, hm9⟩ := lm22_trace_step ⟨[4, 4, 3], [1, 2, 0]⟩ (fuel := 6) hs9
    lm22MemMove_phase rfl rfl (lm22MemMove_copy3to4_wt _ 0 (by decide)) rfl rfl
  have hwt10 : WellTypedLM2_2Stmt lm22MemMoveBody lm22NestedEnv ⟨[4, 4, 3], [1, 2, 0]⟩ 0
      (mkStmt22 (.assign ⟨0, []⟩
        (.use (.copy ⟨4, [.field 1 lm22InnerPairTy, .field 1 u16Ty]⟩))))
      (usePostStaticEnv ⟨[4, 4, 3], [1, 2, 0]⟩ 0
        (.copy ⟨4, [.field 1 lm22InnerPairTy, .field 1 u16Ty]⟩)) 0 :=
    .assignUse _ 0 0 _ _
      (.mk u16Decl rfl (by decide)
        (.projectedScalar false 4 [.field 1 lm22InnerPairTy, .field 1 u16Ty]
          u16Ty rfl
          (.mk lm22NestedDecl lm22NestedFields lm22NestedPaths 2 (by decide) (by decide)
            rfl rfl rfl rfl lm22_u16_prim lm22Nested_projChain_inner1)))
  have ⟨hs11, ha10, hm10⟩ := lm22_trace_step ⟨[0, 4, 4, 3], [0, 1, 2, 0]⟩ (fuel := 5) hs10
    lm22MemMove_phase rfl rfl hwt10 rfl rfl
  have ⟨hs12, ha11, hm11⟩ := lm22_trace_step ⟨[4, 0, 4, 4, 3], [4, 0, 1, 2, 0]⟩ (fuel := 4) hs11
    lm22MemMove_phase rfl rfl (.storageDead _ 0 4 lm22NestedDecl _ rfl (by decide)) rfl rfl
  have ⟨hs13, ha12, hm12⟩ := lm22_trace_step ⟨[3, 4, 0, 4, 4, 3], [3, 4, 0, 1, 2, 0]⟩ (fuel := 3) hs12
    lm22MemMove_phase rfl rfl (.storageDead _ 0 3 lm22NestedDecl _ rfl (by decide)) rfl rfl
  have ⟨hs14, ha13, hm13⟩ := lm22_trace_step ⟨[2, 3, 4, 0, 4, 4, 3], [2, 3, 4, 0, 1, 2, 0]⟩ (fuel := 2) hs13
    lm22MemMove_phase rfl rfl (.storageDead _ 0 2 lm22NestedDecl _ rfl (by decide)) rfl rfl
  have ⟨hs15, ha14, hm14⟩ := lm22_trace_step ⟨[1, 2, 3, 4, 0, 4, 4, 3], [1, 2, 3, 4, 0, 1, 2, 0]⟩ (fuel := 1) hs14
    lm22MemMove_phase rfl rfl (.storageDead _ 0 1 lm22InnerPairDecl _ rfl (by decide)) rfl rfl
  obtain ⟨p1, p2, p3, p10, p11⟩ := lm22Nested_all_five_padding_bytes
  have hpad7 :
      get? (lm22StepAnnealN lm22MemMoveBody 7 (initMachineState lm22MemMoveBody [])).frame.locals 2 =
        some .uninit ∧
      ∃ mp3 alloc3,
        StructMemPlaceRel
          (lm22StepMiriN lm22MemMoveBody 7 lm22MemMoveMiriInit).machine
          lm22NestedTy lm22NestedLayoutTable lm22NestedFields lm22NestedPaths
          (.aggregate 0 [.scalar ⟨7, 1⟩, .aggregate 0 [.scalar ⟨0x11112222, 4⟩, .scalar ⟨0x3344, 2⟩]]) mp3 ∧
        (∃ allocId3,
          (∃ tag, mp3.ptr.provenance = some (.concrete allocId3 tag)) ∧
          (lm22StepMiriN lm22MemMoveBody 7 lm22MemMoveMiriInit).machine.memory.live.find?
            (fun (k, _) => k == allocId3) = some (allocId3, alloc3)) ∧
        alloc3.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 1) = .ok false ∧
        alloc3.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 2) = .ok false ∧
        alloc3.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 3) = .ok false ∧
        alloc3.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 10) = .ok false ∧
        alloc3.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 11) = .ok false := by
    refine ⟨rfl, ?_⟩
    obtain ⟨mp3, _, _, _, _, hsmpr3⟩ :=
      hs7.extract_structMemPlaceRel (idx := 3) (decl := lm22NestedDecl) rfl rfl rfl rfl
    obtain ⟨allocId3, alloc3, hprov3, hfind3, hpad_fn3, _⟩ :=
      hsmpr3.has_uninit_of_padding_byte p1
    exact ⟨mp3, alloc3, hsmpr3, ⟨allocId3, hprov3, hfind3⟩,
      hpad_fn3 1 p1, hpad_fn3 2 p2, hpad_fn3 3 p3, hpad_fn3 10 p10, hpad_fn3 11 p11⟩
  have hpad10 :
      ∃ mp4 alloc4,
        StructMemPlaceRel
          (lm22StepMiriN lm22MemMoveBody 10 lm22MemMoveMiriInit).machine
          lm22NestedTy lm22NestedLayoutTable lm22NestedFields lm22NestedPaths
          (.aggregate 0 [.scalar ⟨7, 1⟩, .aggregate 0 [.scalar ⟨0x11112222, 4⟩, .scalar ⟨0x3344, 2⟩]]) mp4 ∧
        (∃ allocId4,
          (∃ tag, mp4.ptr.provenance = some (.concrete allocId4 tag)) ∧
          (lm22StepMiriN lm22MemMoveBody 10 lm22MemMoveMiriInit).machine.memory.live.find?
            (fun (k, _) => k == allocId4) = some (allocId4, alloc4)) ∧
        alloc4.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 1) = .ok false ∧
        alloc4.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 2) = .ok false ∧
        alloc4.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 3) = .ok false ∧
        alloc4.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 10) = .ok false ∧
        alloc4.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 11) = .ok false := by
    obtain ⟨mp4, _, _, _, _, hsmpr4⟩ :=
      hs10.extract_structMemPlaceRel (idx := 4) (decl := lm22NestedDecl) rfl rfl rfl rfl
    obtain ⟨allocId4, alloc4, hprov4, hfind4, hpad_fn4, _⟩ :=
      hsmpr4.has_uninit_of_padding_byte p1
    exact ⟨mp4, alloc4, hsmpr4, ⟨allocId4, hprov4, hfind4⟩,
      hpad_fn4 1 p1, hpad_fn4 2 p2, hpad_fn4 3 p3, hpad_fn4 10 p10, hpad_fn4 11 p11⟩
  obtain ⟨ha_ret, hm_ret⟩ := lm22_return_agree_of_stateRelLM2_2 hs15 lm22MemMove_phase
    rfl rfl rfl rfl rfl rfl rfl lm22_u16_prim (by decide) rfl
  have ha_tot :
      runAnnealBounded lm22MemMoveBody 16 (initMachineState lm22MemMoveBody []) =
        runAnnealBounded lm22MemMoveBody 1
          (lm22StepAnnealN lm22MemMoveBody 15 (initMachineState lm22MemMoveBody [])) :=
    ha0.trans (ha1.trans (ha2.trans (ha3.trans (ha4.trans (ha5.trans (ha6.trans (ha7.trans
      (ha8.trans (ha9.trans (ha10.trans (ha11.trans (ha12.trans (ha13.trans ha14)))))))))))))
  have hm_tot :
      runMiriBoundedLM2_2 lm22MemMoveBody 16 lm22MemMoveMiriInit =
        runMiriBoundedLM2_2 lm22MemMoveBody 1 (lm22StepMiriN lm22MemMoveBody 15 lm22MemMoveMiriInit) :=
    hm0.trans (hm1.trans (hm2.trans (hm3.trans (hm4.trans (hm5.trans (hm6.trans (hm7.trans
      (hm8.trans (hm9.trans (hm10.trans (hm11.trans (hm12.trans (hm13.trans hm14)))))))))))))
  rw [ha_tot, hm_tot]
  exact ⟨hpad7, hpad10, ha_ret, hm_ret⟩


/-! ## 10. Whole `.Scalar` Wrapper Sub-Struct Read (`_3 = copy _1.1`) & Write (`_1.1 = move _2`) on `PaddedOuter`

On `PaddedOuter { tag: u8, inner: InnerU32 }` (`inner` at offset `4`, alignment
padding at `1, 2, 3`), a single `ProjectionElem.field 1 InnerU32` projects to the
whole 1-field `.Scalar`-ABI wrapper sub-struct `InnerU32`. This witness exercises:
1. `_3 = copy _1.1` via `WellTypedLM2_2Operand.projectedScalarWrap` and
   `evalOperand_nested_scalar_wrap_read_simulation`, reading the whole `InnerU32`
   wrapper from `.Memory`-backed `_1` into `_3`;
2. `_1.1 = move _2` via `WellTypedLM2_2ScalarWrapWrite` and
   `step_assign_nested_scalar_wrap_write_simulation`, overwriting `InnerU32` at
   offset `4` with `0xCAFEBABE_u32` while preserving `_1.0 = 7_u8`, keeping
   inter-field padding bytes `1, 2, 3` `.uninit`, and leaving the earlier copy
   `_3 = InnerU32(42)` intact (`_4 = copy _3.0 = 42_u32`). -/

theorem lm22Padded_projChain_inner_wrap :
    ValidFieldProjChain lm22PaddedLayoutTable
      (translateTy lm22PaddedTy lm22PaddedLayoutTable)
      [.field 1 lm22InnerU32Ty] lm22InnerU32Ty
      (Miri.ABI.Size.ofBytes 4) :=
  .single (translateTy lm22PaddedTy lm22PaddedLayoutTable) 1 lm22InnerU32Ty
    (Miri.ABI.Size.ofBytes 4)
    (Or.inr (Or.inr ⟨"lm22::InnerU32", [], rfl⟩)) rfl rfl (by decide)

def lm22ScalarWrapSubBody : CapturedMir where
  defPath := "lm_2_2_witness::padded_scalar_wrap_substruct_read_write"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls :=
    [lm22U32Decl, lm22PaddedDecl, lm22InnerU32Decl, lm22InnerU32Decl, lm22U32Decl]
  basicBlocks := [
    { statements := [
        mkStmt22 (.storageLive 1),
        mkStmt22 (.storageLive 2),
        mkStmt22 (.storageLive 3),
        mkStmt22 (.storageLive 4),
        mkStmt22 (.assign ⟨2, []⟩
          (.aggregate (.adt "lm22::InnerU32" 0 .none) [.constant (lm22ConstU32 42)])),
        mkStmt22 (.assign ⟨1, []⟩
          (.aggregate (.adt "lm22::PaddedOuter" 0 .none)
            [.constant (constU8 7), .move ⟨2, []⟩])),
        mkStmt22 (.assign ⟨3, []⟩
          (.use (.copy ⟨1, [.field 1 lm22InnerU32Ty]⟩))),
        mkStmt22 (.assign ⟨2, []⟩
          (.aggregate (.adt "lm22::InnerU32" 0 .none) [.constant (lm22ConstU32 0xCAFEBABE)])),
        mkStmt22 (.assign ⟨1, [.field 1 lm22InnerU32Ty]⟩
          (.use (.move ⟨2, []⟩))),
        mkStmt22 (.assign ⟨4, []⟩
          (.use (.copy ⟨3, [.field 0 lm22U32Ty]⟩))),
        mkStmt22 (.assign ⟨0, []⟩
          (.use (.copy ⟨1, [.field 1 lm22InnerU32Ty, .field 0 lm22U32Ty]⟩))),
        mkStmt22 (.storageDead 4),
        mkStmt22 (.storageDead 3),
        mkStmt22 (.storageDead 2),
        mkStmt22 (.storageDead 1)],
      terminator := mkTerm22 .return_,
      isCleanup := false }]
  fnAbi := lm22FnAbiU32
  layouts := lm22PaddedLayoutTable
  allocations := []

def lm22ScalarWrapSubMiriInit : AnnealStepState :=
  { stack := ⟨#[{
      body := translateBody lm22ScalarWrapSubBody
      bodyIdentity := .ofCanonicalIndex 0
      functionInstance := { kind := .Item 0, args := #[] }
      extra := ()
      returnContinuation := .stop false
      returnPlace :=
        .frameLocal 0 0 none (translateTy lm22U32Ty lm22PaddedLayoutTable) (.ofAllocationToken 0)
      localsIdentity := .ofAllocationToken 0
      locals := #[
        { value := .live (.immediate .uninit), layout := none },
        { value := .dead, layout := none },
        { value := .dead, layout := none },
        { value := .dead, layout := none },
        { value := .dead, layout := none }]
      vaList := #[]
      trackCallerArg := none
      location := .mir ⟨0, 0⟩ }]⟩
    machine := AnnealMachine.empty }

theorem lm22ScalarWrapSub_phase : ∀ p, lm22ScalarWrapSubBody.phase ≠ .other p := by
  intro p h; cases h

theorem lm22ScalarWrapSub_stateRelLM2_2_init :
    StateRelLM2_2 lm22ScalarWrapSubBody lm22PaddedEnv { initLocals := [], immLocals := [0] } 4
      (initMachineState lm22ScalarWrapSubBody []) lm22ScalarWrapSubMiriInit := by
  refine .mk _ rfl rfl ⟨translateTy lm22U32Ty lm22PaddedLayoutTable, rfl⟩ ?_
    (fun _ h => nomatch h)
    (fun j hj mp l => by simp at hj; subst hj; dsimp [lm22ScalarWrapSubMiriInit]; nofun)
    (Or.inr (AllocIdWatermark.empty 4 (by decide))) rfl rfl rfl rfl rfl
    (by intro i _ _ _ _ _ _ hi _; revert hi
        match i with | 0 | 1 | 2 | 3 | 4 | _ + 5 => rintro ⟨⟩)
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro i decl slot mls hdecl hslot hmls
  match i with
  | 0 =>
    cases Option.some.inj hdecl
    cases Option.some.inj hslot
    cases Option.some.inj hmls
    exact .base .uninit _ rfl (.immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩))
  | 1 =>
    cases Option.some.inj hdecl
    cases Option.some.inj hslot
    cases Option.some.inj hmls
    exact .structDead lm22PaddedFields lm22PaddedPaths none rfl (fun _ h => nomatch h)
  | 2 | 3 =>
    cases Option.some.inj hdecl
    cases Option.some.inj hslot
    cases Option.some.inj hmls
    exact .structDead [lm22InnerU32Field0] [[.field 0 lm22U32Ty]] none rfl (fun _ h => nomatch h)
  | 4 =>
    cases Option.some.inj hdecl
    cases Option.some.inj hslot
    cases Option.some.inj hmls
    exact .base .dead _ rfl (.dead none (fun _ h => nomatch h))
  | _ + 5 => simp [lm22ScalarWrapSubBody, get?] at hdecl

theorem lm22ScalarWrapSub_read_wt :
    WellTypedLM2_2ProjectedScalarWrapRead lm22ScalarWrapSubBody lm22PaddedEnv
      1 [.field 1 lm22InnerU32Ty] lm22InnerU32Ty lm22InnerU32Field0 lm22U32Ty :=
  .mk lm22PaddedDecl lm22PaddedFields lm22PaddedPaths 1
    (by decide) (by decide) (Miri.ABI.Size.ofBytes 4) _
    rfl rfl rfl rfl rfl rfl rfl (by decide)
    rfl rfl rfl rfl
    lm22InnerU32_validStructLayout (by decide) rfl
    (.single (translateTy lm22InnerU32Ty lm22PaddedLayoutTable) lm22U32Ty lm22_u32_prim rfl rfl)
    lm22_u32_prim lm22Padded_projChain_inner_wrap

theorem lm22ScalarWrapSub_write_wt (stEnv : LM2_2StaticEnv) (h1_init : 1 ∈ stEnv.initLocals) :
    WellTypedLM2_2ScalarWrapWrite lm22ScalarWrapSubBody lm22PaddedEnv stEnv
      1 [.field 1 lm22InnerU32Ty] (.move ⟨2, []⟩) :=
  .mk lm22PaddedDecl lm22PaddedFields lm22PaddedPaths 1
    (by decide) (by decide) lm22InnerU32Ty lm22InnerU32Field0 lm22U32Ty _
    rfl rfl h1_init rfl (by decide) rfl
    (fun j hj hne => by
      match j with
      | 0 => exact .diff_head (by decide)
      | 1 => exact False.elim (hne rfl)
      | _ + 2 => simp [lm22PaddedPaths] at hj; omega)
    lm22Padded_projChain_inner_wrap
    rfl rfl lm22InnerU32_isImmediateStructTy
    rfl rfl
    (by decide : (2 : Nat) ≠ 1)
    (.immStructLocal true 2 lm22InnerU32Decl [lm22InnerU32Field0] [[.field 0 lm22U32Ty]]
      rfl lm22InnerU32_isImmediateStructTy)

theorem lm22ScalarWrapSub_full_trace_and_returns_agree :
    (get? (lm22StepAnnealN lm22ScalarWrapSubBody 7 (initMachineState lm22ScalarWrapSubBody [])).frame.locals 3 =
      some (.init (.aggregate 0 [.scalar ⟨42, 4⟩])) ∧
     ∃ imm,
      ImmediateStructRel lm22InnerU32Ty lm22PaddedLayoutTable
        [lm22InnerU32Field0] [[.field 0 lm22U32Ty]]
        (.aggregate 0 [.scalar ⟨42, 4⟩]) imm) ∧
    (∃ mp localAlloc,
      StructMemPlaceRel
        (lm22StepMiriN lm22ScalarWrapSubBody 9 lm22ScalarWrapSubMiriInit).machine
        lm22PaddedTy lm22PaddedLayoutTable lm22PaddedFields lm22PaddedPaths
        (.aggregate 0 [.scalar ⟨7, 1⟩, .aggregate 0 [.scalar ⟨0xCAFEBABE, 4⟩]]) mp ∧
      (∃ allocId,
        (∃ tag, mp.ptr.provenance = some (.concrete allocId tag)) ∧
        (lm22StepMiriN lm22ScalarWrapSubBody 9 lm22ScalarWrapSubMiriInit).machine.memory.live.find?
          (fun (k, _) => k == allocId) = some (allocId, localAlloc)) ∧
      localAlloc.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 1) = .ok false ∧
      localAlloc.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 2) = .ok false ∧
      localAlloc.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 3) = .ok false ∧
      localAlloc.allocation.initializationMask.isRangeInitialized
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8)) ≠ .ok (.ok ())) ∧
    get? (lm22StepAnnealN lm22ScalarWrapSubBody 10 (initMachineState lm22ScalarWrapSubBody [])).frame.locals 4 =
      some (.init (.scalar ⟨42, 4⟩)) ∧
    annealOutcomeScalarBits 4
      (runAnnealBounded lm22ScalarWrapSubBody 16 (initMachineState lm22ScalarWrapSubBody [])) =
        some 0xCAFEBABE ∧
    miriOutcomeScalarBits 4
      (runMiriBoundedLM2_2 lm22ScalarWrapSubBody 16 lm22ScalarWrapSubMiriInit) = some 0xCAFEBABE := by
  have hs0 : StateRelLM2_2 lm22ScalarWrapSubBody lm22PaddedEnv { initLocals := [], immLocals := [0] } 4
      (lm22StepAnnealN lm22ScalarWrapSubBody 0 (initMachineState lm22ScalarWrapSubBody []))
      (lm22StepMiriN lm22ScalarWrapSubBody 0 lm22ScalarWrapSubMiriInit) :=
    lm22ScalarWrapSub_stateRelLM2_2_init
  have ⟨hs1, ha0, hm0⟩ := lm22_trace_step ⟨[], [1, 0]⟩ (fuel := 15) hs0
    lm22ScalarWrapSub_phase rfl rfl (.storageLive _ 4 1 lm22PaddedDecl _ rfl) rfl rfl
  have ⟨hs2, ha1, hm1⟩ := lm22_trace_step ⟨[], [2, 1, 0]⟩ (fuel := 14) hs1
    lm22ScalarWrapSub_phase rfl rfl (.storageLive _ 4 2 lm22InnerU32Decl _ rfl) rfl rfl
  have ⟨hs3, ha2, hm2⟩ := lm22_trace_step ⟨[], [3, 2, 1, 0]⟩ (fuel := 13) hs2
    lm22ScalarWrapSub_phase rfl rfl (.storageLive _ 4 3 lm22InnerU32Decl _ rfl) rfl rfl
  have ⟨hs4, ha3, hm3⟩ := lm22_trace_step ⟨[], [4, 3, 2, 1, 0]⟩ (fuel := 12) hs3
    lm22ScalarWrapSub_phase rfl rfl (.storageLive _ 4 4 lm22U32Decl _ rfl) rfl rfl
  have hwt_u32 : ∀ stEnv k dst n,
      get? lm22ScalarWrapSubBody.localDecls dst = some lm22InnerU32Decl →
      n < 4294967296 →
      WellTypedLM2_2Stmt lm22ScalarWrapSubBody lm22PaddedEnv stEnv (k + 1)
        (mkStmt22 (.assign ⟨dst, []⟩
          (.aggregate (.adt "lm22::InnerU32" 0 .none) [.constant (lm22ConstU32 n)])))
        (aggPostStaticEnv stEnv dst [.constant (lm22ConstU32 n)]) k := fun stEnv k dst n hd hn =>
    .assignAggregate stEnv k dst _ _ _
      (.mk lm22InnerU32Decl [lm22InnerU32Field0] [[.field 0 lm22U32Ty]] _ [] rfl
        (Or.inr ⟨"lm22::InnerU32", rfl⟩) hd rfl lm22InnerU32_validStructLayout
        (by decide) rfl rfl (by decide)
        (.cons _ 0 0 1 _ [] trivial
          (.primLeaf (by decide) _ (lm22_constU32_wt n hn rfl)
            rfl lm22_u32_prim rfl rfl rfl rfl rfl rfl)
          (.nil _ 1)))
  have ⟨hs5, ha4, hm4⟩ := lm22_trace_step ⟨[2], [4, 3, 1, 0]⟩ (fuel := 11) hs4
    lm22ScalarWrapSub_phase rfl rfl (hwt_u32 _ 3 2 42 rfl (by decide)) rfl rfl
  have hwt5 : WellTypedLM2_2Stmt lm22ScalarWrapSubBody lm22PaddedEnv ⟨[2], [4, 3, 1, 0]⟩ 3
      (mkStmt22 (.assign ⟨1, []⟩
        (.aggregate (.adt "lm22::PaddedOuter" 0 .none)
          [.constant (constU8 7), .move ⟨2, []⟩])))
      (aggPostStaticEnv ⟨[2], [4, 3, 1, 0]⟩ 1 [.constant (constU8 7), .move ⟨2, []⟩]) 2 :=
    .assignAggregate _ 2 1 _ _ _
      (.mk lm22PaddedDecl lm22PaddedFields lm22PaddedPaths _ _ rfl
        (Or.inr ⟨"lm22::PaddedOuter", rfl⟩) rfl rfl lm22Padded_validStructLayout
        (by decide) rfl rfl (by decide)
        (.cons _ 0 0 1 _ _ trivial
          (.primLeaf (by decide) _ (lm22_constU8_wt 7 (by decide) rfl)
            rfl lm22_u8_prim rfl rfl rfl rfl rfl rfl)
          (.cons _ 1 1 2 (.move ⟨2, []⟩) [] (by decide : (2 : Nat) ≠ 1)
            (.scalarWrapSub (by decide) lm22InnerU32Ty lm22InnerU32Field0
              [.field 0 lm22U32Ty] _
              (.immStructLocal true 2 lm22InnerU32Decl [lm22InnerU32Field0]
                [[.field 0 lm22U32Ty]] rfl lm22InnerU32_isImmediateStructTy)
              lm22InnerU32_isImmediateStructTy rfl rfl rfl rfl rfl rfl rfl)
            (.nil _ 2))))
  have ⟨hs6, ha5, hm5⟩ := lm22_trace_step ⟨[1], [2, 4, 3, 0]⟩ (fuel := 10) hs5
    lm22ScalarWrapSub_phase rfl rfl hwt5 rfl rfl
  have hread_imm :
      ∃ imm,
        ImmediateStructRel lm22InnerU32Ty lm22PaddedLayoutTable
          [lm22InnerU32Field0] [[.field 0 lm22U32Ty]]
          (.aggregate 0 [.scalar ⟨42, 4⟩]) imm := by
    rcases hs6 with ⟨tf6, htf6, _, _, hfr6, _, _, _, _, _, _, _, _, _⟩
    have hsim_r := evalOperand_nested_scalar_wrap_read_simulation (isMove := false)
      htf6 hfr6 lm22ScalarWrapSub_read_wt [] none
    have ha_op : evalOperand
        (lm22StepAnnealN lm22ScalarWrapSubBody 6 (initMachineState lm22ScalarWrapSubBody [])).frame.locals
        (mkPlaceOperand false ⟨1, [.field 1 lm22InnerU32Ty]⟩) .nil []
        lm22ScalarWrapSubBody.layouts .nil =
        .ok (.aggregate 0 [.scalar ⟨42, 4⟩])
          (lm22StepAnnealN lm22ScalarWrapSubBody 6 (initMachineState lm22ScalarWrapSubBody [])).frame.locals := rfl
    rw [ha_op] at hsim_r
    generalize hm_op :
      (annealEvalOperand lm22ScalarWrapSubBody.localDecls lm22ScalarWrapSubBody.layouts
          (translateOperand (mkPlaceOperand false ⟨1, [.field 1 lm22InnerU32Ty]⟩)) none >>=
        annealReadImmediateLM2_2)
        (lm22StepMiriN lm22ScalarWrapSubBody ((((((0 + 1) + 1) + 1) + 1) + 1) + 1) lm22ScalarWrapSubMiriInit) = rm
      at hsim_r
    cases hsim_r with
    | ok _ msc₀ _ _ _ himm _ _ _ _ _ => exact ⟨.scalar (.fromScalarInt msc₀), himm⟩
  have hwt6 : WellTypedLM2_2Stmt lm22ScalarWrapSubBody lm22PaddedEnv ⟨[1], [2, 4, 3, 0]⟩ 2
      (mkStmt22 (.assign ⟨3, []⟩ (.use (.copy ⟨1, [.field 1 lm22InnerU32Ty]⟩))))
      (useStructPostStaticEnv ⟨[1], [2, 4, 3, 0]⟩ 3 (.copy ⟨1, [.field 1 lm22InnerU32Ty]⟩)) 2 :=
    .assignUseStruct _ 2 3 (.copy ⟨1, [.field 1 lm22InnerU32Ty]⟩) _
      (.mk lm22InnerU32Decl [lm22InnerU32Field0] [[.field 0 lm22U32Ty]] rfl
        lm22InnerU32_isImmediateStructTy
        (.projectedScalarWrap false 1 [.field 1 lm22InnerU32Ty]
          lm22InnerU32Ty lm22InnerU32Field0 lm22U32Ty
          lm22InnerU32_isImmediateStructTy lm22ScalarWrapSub_read_wt))
  have ⟨hs7, ha6, hm6⟩ := lm22_trace_step ⟨[3, 1], [2, 4, 0]⟩ (fuel := 9) hs6
    lm22ScalarWrapSub_phase rfl rfl hwt6 rfl rfl
  have ⟨hs8, ha7, hm7⟩ := lm22_trace_step ⟨[2, 3, 1], [4, 0]⟩ (fuel := 8) hs7
    lm22ScalarWrapSub_phase rfl rfl (hwt_u32 _ 1 2 0xCAFEBABE rfl (by decide)) rfl rfl
  have hwt8 : WellTypedLM2_2Stmt lm22ScalarWrapSubBody lm22PaddedEnv ⟨[2, 3, 1], [4, 0]⟩ 1
      (mkStmt22 (.assign ⟨1, [.field 1 lm22InnerU32Ty]⟩ (.use (.move ⟨2, []⟩))))
      (fieldWritePostStaticEnv ⟨[2, 3, 1], [4, 0]⟩ 1 (.move ⟨2, []⟩)) 0 :=
    .assignScalarWrapWrite _ 0 1 [.field 1 lm22InnerU32Ty] (.move ⟨2, []⟩) _
      (lm22ScalarWrapSub_write_wt _ (by decide))
  have ⟨hs9, ha8, hm8⟩ := lm22_trace_step ⟨[3, 1], [2, 4, 0]⟩ (fuel := 7) hs8
    lm22ScalarWrapSub_phase rfl rfl hwt8 rfl rfl
  have hwt9 : WellTypedLM2_2Stmt lm22ScalarWrapSubBody lm22PaddedEnv ⟨[3, 1], [2, 4, 0]⟩ 0
      (mkStmt22 (.assign ⟨4, []⟩ (.use (.copy ⟨3, [.field 0 lm22U32Ty]⟩))))
      (usePostStaticEnv ⟨[3, 1], [2, 4, 0]⟩ 4 (.copy ⟨3, [.field 0 lm22U32Ty]⟩)) 0 :=
    .assignUse _ 0 4 _ _
      (.mk lm22U32Decl rfl (by decide)
        (.projectedScalar false 3 [.field 0 lm22U32Ty] lm22U32Ty rfl
          (.mk lm22InnerU32Decl [lm22InnerU32Field0] [[.field 0 lm22U32Ty]] 0
            (by decide) (by decide) rfl rfl rfl rfl lm22_u32_prim
            (.single (translateTy lm22InnerU32Ty lm22PaddedLayoutTable) 0 lm22U32Ty
              Miri.ABI.Size.ZERO (Or.inl lm22_u32_prim) rfl rfl (by decide)))))
  have ⟨hs10, ha9, hm9⟩ := lm22_trace_step ⟨[4, 3, 1], [4, 2, 4, 0]⟩ (fuel := 6) hs9
    lm22ScalarWrapSub_phase rfl rfl hwt9 rfl rfl
  have hwt10 : WellTypedLM2_2Stmt lm22ScalarWrapSubBody lm22PaddedEnv ⟨[4, 3, 1], [4, 2, 4, 0]⟩ 0
      (mkStmt22 (.assign ⟨0, []⟩
        (.use (.copy ⟨1, [.field 1 lm22InnerU32Ty, .field 0 lm22U32Ty]⟩))))
      (usePostStaticEnv ⟨[4, 3, 1], [4, 2, 4, 0]⟩ 0
        (.copy ⟨1, [.field 1 lm22InnerU32Ty, .field 0 lm22U32Ty]⟩)) 0 :=
    .assignUse _ 0 0 _ _
      (.mk lm22U32Decl rfl (by decide)
        (.projectedScalar false 1 [.field 1 lm22InnerU32Ty, .field 0 lm22U32Ty]
          lm22U32Ty rfl
          (.mk lm22PaddedDecl lm22PaddedFields lm22PaddedPaths 1 (by decide) (by decide)
            rfl rfl rfl rfl lm22_u32_prim lm22Padded_projChain_inner0)))
  have ⟨hs11, ha10, hm10⟩ := lm22_trace_step ⟨[0, 4, 3, 1], [0, 4, 2, 4, 0]⟩ (fuel := 5) hs10
    lm22ScalarWrapSub_phase rfl rfl hwt10 rfl rfl
  have ⟨hs12, ha11, hm11⟩ := lm22_trace_step ⟨[4, 0, 4, 3, 1], [4, 0, 4, 2, 4, 0]⟩ (fuel := 4) hs11
    lm22ScalarWrapSub_phase rfl rfl (.storageDead _ 0 4 lm22U32Decl _ rfl (by decide)) rfl rfl
  have ⟨hs13, ha12, hm12⟩ := lm22_trace_step ⟨[3, 4, 0, 4, 3, 1], [3, 4, 0, 4, 2, 4, 0]⟩ (fuel := 3) hs12
    lm22ScalarWrapSub_phase rfl rfl (.storageDead _ 0 3 lm22InnerU32Decl _ rfl (by decide)) rfl rfl
  have ⟨hs14, ha13, hm13⟩ := lm22_trace_step ⟨[2, 3, 4, 0, 4, 3, 1], [2, 3, 4, 0, 4, 2, 4, 0]⟩ (fuel := 2) hs13
    lm22ScalarWrapSub_phase rfl rfl (.storageDead _ 0 2 lm22InnerU32Decl _ rfl (by decide)) rfl rfl
  have ⟨hs15, ha14, hm14⟩ := lm22_trace_step ⟨[1, 2, 3, 4, 0, 4, 3, 1], [1, 2, 3, 4, 0, 4, 2, 4, 0]⟩ (fuel := 1) hs14
    lm22ScalarWrapSub_phase rfl rfl (.storageDead _ 0 1 lm22PaddedDecl _ rfl (by decide)) rfl rfl
  have hpad9 :
      ∃ mp localAlloc,
        StructMemPlaceRel
          (lm22StepMiriN lm22ScalarWrapSubBody 9 lm22ScalarWrapSubMiriInit).machine
          lm22PaddedTy lm22PaddedLayoutTable lm22PaddedFields lm22PaddedPaths
          (.aggregate 0 [.scalar ⟨7, 1⟩, .aggregate 0 [.scalar ⟨0xCAFEBABE, 4⟩]]) mp ∧
        (∃ allocId,
          (∃ tag, mp.ptr.provenance = some (.concrete allocId tag)) ∧
          (lm22StepMiriN lm22ScalarWrapSubBody 9 lm22ScalarWrapSubMiriInit).machine.memory.live.find?
            (fun (k, _) => k == allocId) = some (allocId, localAlloc)) ∧
        localAlloc.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 1) = .ok false ∧
        localAlloc.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 2) = .ok false ∧
        localAlloc.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 3) = .ok false ∧
        localAlloc.allocation.initializationMask.isRangeInitialized
          (Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8)) ≠ .ok (.ok ()) := by
    obtain ⟨mp, _, _, _, _, hsmpr⟩ :=
      hs9.extract_structMemPlaceRel (idx := 1) (decl := lm22PaddedDecl) rfl rfl rfl rfl
    obtain ⟨p1, p2, p3⟩ := lm22Padded_interfield_padding_bytes
    obtain ⟨allocId, localAlloc, hprov, hfind, hpad_fn, hhas_uninit⟩ :=
      hsmpr.has_uninit_of_padding_byte p1
    exact ⟨mp, localAlloc, hsmpr, ⟨allocId, hprov, hfind⟩,
      hpad_fn 1 p1, hpad_fn 2 p2, hpad_fn 3 p3, hhas_uninit⟩
  obtain ⟨ha_ret, hm_ret⟩ := lm22_return_agree_of_stateRelLM2_2 hs15 lm22ScalarWrapSub_phase
    rfl rfl rfl rfl rfl rfl rfl lm22_u32_prim (by decide) rfl
  have ha_tot :
      runAnnealBounded lm22ScalarWrapSubBody 16 (initMachineState lm22ScalarWrapSubBody []) =
        runAnnealBounded lm22ScalarWrapSubBody 1
          (lm22StepAnnealN lm22ScalarWrapSubBody 15 (initMachineState lm22ScalarWrapSubBody [])) :=
    ha0.trans (ha1.trans (ha2.trans (ha3.trans (ha4.trans (ha5.trans (ha6.trans (ha7.trans
      (ha8.trans (ha9.trans (ha10.trans (ha11.trans (ha12.trans (ha13.trans ha14)))))))))))))
  have hm_tot :
      runMiriBoundedLM2_2 lm22ScalarWrapSubBody 16 lm22ScalarWrapSubMiriInit =
        runMiriBoundedLM2_2 lm22ScalarWrapSubBody 1
          (lm22StepMiriN lm22ScalarWrapSubBody 15 lm22ScalarWrapSubMiriInit) :=
    hm0.trans (hm1.trans (hm2.trans (hm3.trans (hm4.trans (hm5.trans (hm6.trans (hm7.trans
      (hm8.trans (hm9.trans (hm10.trans (hm11.trans (hm12.trans (hm13.trans hm14)))))))))))))
  rw [ha_tot, hm_tot]
  exact ⟨⟨rfl, hread_imm⟩, hpad9, rfl, ha_ret, hm_ret⟩


/-! ## 11. Realistic `#[repr(C)]` >64-Byte Multi-Block Struct (`RealisticPadded80`, `80` Bytes, `align = 8`)

Models a concrete `rustc` `#[repr(C)]` layout (`size = 80`, `align = 8`) spanning
two 64-byte `UInt64` blocks in `InitMask`:
- field `0` (`u8`) at byte offset `0` (`1` byte), followed by **7 inter-field
  alignment padding bytes `1..7`** in `InitMask` block 0 (`[0, 64)`),
- fields `1..8` (`8 × u64`) at byte offsets `8, 16, 24, 32, 40, 48, 56, 64`
  (`[8, 72)`, crossing the 64-byte `InitMask` word boundary into block 1 at
  field `8`, offset `64`),
- field `9` (`u8`) at byte offset `72` (`1` byte), followed by **7 trailing
  alignment padding bytes `73..79`** in `InitMask` block 1 (`[64, 80)`). -/

def lm22U64Ty : Ty := { kind := .uint .u64, layoutIdx := 0 }
def lm22U64Decl : LocalDecl := { mutability := .mut, ty := lm22U64Ty, debugName := none }

def lm22ConstU64 (n : Nat) : ConstOperand :=
  { ty := lm22U64Ty, val := .scalar (.int ⟨n, 8⟩) }

def lm22U64TypeLayout : TypeLayout :=
  { size := { bytes := 8 }
    align := { bytes := 8 }
    backendRepr :=
      .scalar (.initialized (.int 64 false) { start := 0, end_ := 18446744073709551615 })
    fields := .primitive
    variants := .single 0
    isUninhabited := false }

theorem lm22_u64_prim : IsPrimScalarTy lm22U64Ty :=
  Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))

theorem lm22_constU64_wt {body : CapturedMir} {env : StructTypeEnv}
    {stEnv : LM2_2StaticEnv} (n : Nat) (hn : n < 18446744073709551616)
    (henv : env lm22U64Ty = none) :
    WellTypedLM2_2Operand body env stEnv (.constant (lm22ConstU64 n)) lm22U64Ty :=
  .constScalar _ ⟨n, 8⟩ rfl henv lm22_u64_prim (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    (by rw [scalarModulus_eq_two_pow]; exact hn) rfl nofun nofun

def lm22Realistic80Ty : Ty :=
  { kind := .adt "lm22::RealisticPadded80" [], layoutIdx := 0 }

def lm22Realistic80Decl : LocalDecl :=
  { mutability := .mut, ty := lm22Realistic80Ty, debugName := none }

def lm22Realistic80TypeLayout : TypeLayout :=
  { size := { bytes := 80 }
    align := { bytes := 8 }
    backendRepr := .memory
    fields := .arbitrary
      [{ bytes := 0 }, { bytes := 8 }, { bytes := 16 }, { bytes := 24 }, { bytes := 32 },
       { bytes := 40 }, { bytes := 48 }, { bytes := 56 }, { bytes := 64 }, { bytes := 72 }]
      [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
    variants := .single 0
    isUninhabited := false
    fieldLayouts := [2, 1, 1, 1, 1, 1, 1, 1, 1, 2] }

def lm22Realistic80LayoutTable : LayoutTable :=
  { pointerBits := 64
    isLittleEndian := true
    entries := [lm22Realistic80TypeLayout, lm22U64TypeLayout, lm22U8TypeLayout] }

def lm22Realistic80MkU64Field (offBytes : UInt64) : StructFieldDesc :=
  { offset := Miri.ABI.Size.ofBytes offBytes
    ty := lm22U64Ty
    fieldLayout := (translateTy lm22U64Ty lm22Realistic80LayoutTable).layout }

def lm22Realistic80Fields : List StructFieldDesc :=
  [ { offset := Miri.ABI.Size.ZERO
      ty := u8Ty
      fieldLayout := (translateTy u8Ty lm22Realistic80LayoutTable).layout },
    lm22Realistic80MkU64Field 8,
    lm22Realistic80MkU64Field 16,
    lm22Realistic80MkU64Field 24,
    lm22Realistic80MkU64Field 32,
    lm22Realistic80MkU64Field 40,
    lm22Realistic80MkU64Field 48,
    lm22Realistic80MkU64Field 56,
    lm22Realistic80MkU64Field 64,
    { offset := Miri.ABI.Size.ofBytes 72
      ty := u8Ty
      fieldLayout := (translateTy u8Ty lm22Realistic80LayoutTable).layout } ]

def lm22Realistic80Paths : List (List ProjectionElem) :=
  [ [.field 0 u8Ty],
    [.field 1 lm22U64Ty],
    [.field 2 lm22U64Ty],
    [.field 3 lm22U64Ty],
    [.field 4 lm22U64Ty],
    [.field 5 lm22U64Ty],
    [.field 6 lm22U64Ty],
    [.field 7 lm22U64Ty],
    [.field 8 lm22U64Ty],
    [.field 9 u8Ty] ]

def lm22Realistic80Env : StructTypeEnv := fun ty =>
  match ty.kind with
  | .adt "lm22::RealisticPadded80" [] => some (lm22Realistic80Fields, lm22Realistic80Paths)
  | _ => none

theorem lm22Realistic80_validStructLayout :
    ValidStructLayout (translateTy lm22Realistic80Ty lm22Realistic80LayoutTable).layout
      lm22Realistic80Fields := by
  have hlen_f : lm22Realistic80Fields.length = 10 := rfl
  have hbounds_fin : ∀ a : Fin 10,
      (lm22Realistic80Fields[a.val]'(by rw [hlen_f]; exact a.isLt)).offset.bytes.toNat +
        (lm22Realistic80Fields[a.val]'(by rw [hlen_f]; exact a.isLt)).fieldLayout.size.bytes.toNat ≤
        (translateTy lm22Realistic80Ty lm22Realistic80LayoutTable).layout.size.bytes.toNat := by
    decide +revert
  have hdisj_fin : ∀ a b : Fin 10, a ≠ b →
      (lm22Realistic80Fields[a.val]'(by rw [hlen_f]; exact a.isLt)).offset.bytes.toNat +
        (lm22Realistic80Fields[a.val]'(by rw [hlen_f]; exact a.isLt)).fieldLayout.size.bytes.toNat ≤
        (lm22Realistic80Fields[b.val]'(by rw [hlen_f]; exact b.isLt)).offset.bytes.toNat ∨
      (lm22Realistic80Fields[b.val]'(by rw [hlen_f]; exact b.isLt)).offset.bytes.toNat +
        (lm22Realistic80Fields[b.val]'(by rw [hlen_f]; exact b.isLt)).fieldLayout.size.bytes.toNat ≤
        (lm22Realistic80Fields[a.val]'(by rw [hlen_f]; exact a.isLt)).offset.bytes.toNat := by
    decide +revert
  have halign_fin : ∀ a : Fin 10,
      2 ^ (lm22Realistic80Fields[a.val]'(by rw [hlen_f]; exact a.isLt)).fieldLayout.align.abi.pow2 ∣
        (lm22Realistic80Fields[a.val]'(by rw [hlen_f]; exact a.isLt)).offset.bytes.toNat := by
    decide +revert
  refine
    { fields_in_bounds := fun i hi => hbounds_fin ⟨i, by rw [hlen_f] at hi; exact hi⟩
      fields_disjoint := fun i j hi hj hne =>
        hdisj_fin ⟨i, by rw [hlen_f] at hi; exact hi⟩ ⟨j, by rw [hlen_f] at hj; exact hj⟩
          (fun h => hne (congrArg Fin.val h))
      fields_aligned := fun i hi => halign_fin ⟨i, by rw [hlen_f] at hi; exact hi⟩
      fields_shape_valid :=
        Or.inr (ValidStructLayout.arbitrary_flat #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9] rfl (by decide)) }

theorem lm22Realistic80_all_padding_bytes (b : Nat)
    (hb : (1 ≤ b ∧ b ≤ 7) ∨ (73 ≤ b ∧ b ≤ 79)) :
    isStructPaddingByte lm22Realistic80Fields (Miri.ABI.Size.ofBytes 80) b := by
  refine ⟨by change b < 80; omega, ?_⟩
  intro f hf
  simp only [lm22Realistic80Fields, lm22Realistic80MkU64Field, List.mem_cons,
    List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · right; change 1 ≤ b; omega
  · rcases hb with h0 | h1
    · left; change b < 8; omega
    · right; change 8 + 8 ≤ b; omega
  · rcases hb with h0 | h1
    · left; change b < 16; omega
    · right; change 16 + 8 ≤ b; omega
  · rcases hb with h0 | h1
    · left; change b < 24; omega
    · right; change 24 + 8 ≤ b; omega
  · rcases hb with h0 | h1
    · left; change b < 32; omega
    · right; change 32 + 8 ≤ b; omega
  · rcases hb with h0 | h1
    · left; change b < 40; omega
    · right; change 40 + 8 ≤ b; omega
  · rcases hb with h0 | h1
    · left; change b < 48; omega
    · right; change 48 + 8 ≤ b; omega
  · rcases hb with h0 | h1
    · left; change b < 56; omega
    · right; change 56 + 8 ≤ b; omega
  · rcases hb with h0 | h1
    · left; change b < 64; omega
    · right; change 64 + 8 ≤ b; omega
  · rcases hb with h0 | h1
    · left; change b < 72; omega
    · right; change 72 + 1 ≤ b; omega

def lm22Realistic80InitOps : List MirAst.Operand :=
  [ .constant (constU8 1),
    .constant (lm22ConstU64 10),
    .constant (lm22ConstU64 20),
    .constant (lm22ConstU64 30),
    .constant (lm22ConstU64 40),
    .constant (lm22ConstU64 50),
    .constant (lm22ConstU64 60),
    .constant (lm22ConstU64 70),
    .constant (lm22ConstU64 80),
    .constant (constU8 2) ]

def lm22Realistic80Body : CapturedMir where
  defPath := "lm_2_2_witness::realistic_repr_c_padded_80"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u8Decl, lm22Realistic80Decl, lm22U64Decl]
  basicBlocks := [
    { statements := [
        mkStmt22 (.storageLive 1),
        mkStmt22 (.storageLive 2),
        mkStmt22 (.assign ⟨1, []⟩
          (.aggregate (.adt "lm22::RealisticPadded80" 0 .none) lm22Realistic80InitOps)),
        mkStmt22 (.assign ⟨1, [.field 8 lm22U64Ty]⟩
          (.use (.constant (lm22ConstU64 0x1122334455667788)))),
        mkStmt22 (.assign ⟨1, [.field 9 u8Ty]⟩
          (.use (.constant (constU8 0xAB)))),
        mkStmt22 (.assign ⟨2, []⟩
          (.use (.copy ⟨1, [.field 8 lm22U64Ty]⟩))),
        mkStmt22 (.assign ⟨0, []⟩
          (.use (.copy ⟨1, [.field 9 u8Ty]⟩))),
        mkStmt22 (.storageDead 2),
        mkStmt22 (.storageDead 1)],
      terminator := mkTerm22 .return_,
      isCleanup := false }]
  fnAbi := fnAbi0
  layouts := lm22Realistic80LayoutTable
  allocations := []

def lm22Realistic80MiriInit : AnnealStepState :=
  { stack := ⟨#[{
      body := translateBody lm22Realistic80Body
      bodyIdentity := .ofCanonicalIndex 0
      functionInstance := { kind := .Item 0, args := #[] }
      extra := ()
      returnContinuation := .stop false
      returnPlace :=
        .frameLocal 0 0 none (translateTy u8Ty lm22Realistic80LayoutTable) (.ofAllocationToken 0)
      localsIdentity := .ofAllocationToken 0
      locals := #[
        { value := .live (.immediate .uninit), layout := none },
        { value := .dead, layout := none },
        { value := .dead, layout := none }]
      vaList := #[]
      trackCallerArg := none
      location := .mir ⟨0, 0⟩ }]⟩
    machine := AnnealMachine.empty }

theorem lm22Realistic80_phase : ∀ p, lm22Realistic80Body.phase ≠ .other p := by
  intro p h; cases h

theorem lm22Realistic80_stateRelLM2_2_init :
    StateRelLM2_2 lm22Realistic80Body lm22Realistic80Env { initLocals := [], immLocals := [0] } 3
      (initMachineState lm22Realistic80Body []) lm22Realistic80MiriInit := by
  refine .mk _ rfl rfl ⟨translateTy u8Ty lm22Realistic80LayoutTable, rfl⟩ ?_
    (fun _ h => nomatch h)
    (fun j hj mp l => by simp at hj; subst hj; dsimp [lm22Realistic80MiriInit]; nofun)
    (Or.inr (AllocIdWatermark.empty 3 (by decide))) rfl rfl rfl rfl rfl
    (by intro i _ _ _ _ _ _ hi _; revert hi; match i with | 0 | 1 | 2 | _ + 3 => rintro ⟨⟩)
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro i decl slot mls hdecl hslot hmls
  match i with
  | 0 =>
    cases Option.some.inj hdecl
    cases Option.some.inj hslot
    cases Option.some.inj hmls
    exact .base .uninit _ rfl (.immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩))
  | 1 =>
    cases Option.some.inj hdecl
    cases Option.some.inj hslot
    cases Option.some.inj hmls
    exact .structDead lm22Realistic80Fields lm22Realistic80Paths none rfl (fun _ h => nomatch h)
  | 2 =>
    cases Option.some.inj hdecl
    cases Option.some.inj hslot
    cases Option.some.inj hmls
    exact .base .dead _ rfl (.dead none (fun _ h => nomatch h))
  | _ + 3 => simp [lm22Realistic80Body, get?] at hdecl

theorem lm22Realistic80_agg_wt (stEnv : LM2_2StaticEnv) (k : Nat) :
    WellTypedLM2_2Stmt lm22Realistic80Body lm22Realistic80Env stEnv (k + 1)
      (mkStmt22 (.assign ⟨1, []⟩
        (.aggregate (.adt "lm22::RealisticPadded80" 0 .none) lm22Realistic80InitOps)))
      (aggPostStaticEnv stEnv 1 lm22Realistic80InitOps) k :=
  .assignAggregate stEnv k 1 _ _ _
    (.mk lm22Realistic80Decl lm22Realistic80Fields lm22Realistic80Paths _ _ rfl
      (Or.inr ⟨"lm22::RealisticPadded80", rfl⟩) rfl rfl lm22Realistic80_validStructLayout
      (by decide) rfl rfl (by decide)
      (.cons _ 0 0 1 _ _ trivial
        (.primLeaf (by decide) _ (lm22_constU8_wt 1 (by decide) rfl)
          rfl lm22_u8_prim rfl rfl rfl rfl rfl rfl) <|
      .cons _ 1 1 2 _ _ trivial
        (.primLeaf (by decide) _ (lm22_constU64_wt 10 (by decide) rfl)
          rfl lm22_u64_prim rfl rfl rfl rfl rfl rfl) <|
      .cons _ 2 2 3 _ _ trivial
        (.primLeaf (by decide) _ (lm22_constU64_wt 20 (by decide) rfl)
          rfl lm22_u64_prim rfl rfl rfl rfl rfl rfl) <|
      .cons _ 3 3 4 _ _ trivial
        (.primLeaf (by decide) _ (lm22_constU64_wt 30 (by decide) rfl)
          rfl lm22_u64_prim rfl rfl rfl rfl rfl rfl) <|
      .cons _ 4 4 5 _ _ trivial
        (.primLeaf (by decide) _ (lm22_constU64_wt 40 (by decide) rfl)
          rfl lm22_u64_prim rfl rfl rfl rfl rfl rfl) <|
      .cons _ 5 5 6 _ _ trivial
        (.primLeaf (by decide) _ (lm22_constU64_wt 50 (by decide) rfl)
          rfl lm22_u64_prim rfl rfl rfl rfl rfl rfl) <|
      .cons _ 6 6 7 _ _ trivial
        (.primLeaf (by decide) _ (lm22_constU64_wt 60 (by decide) rfl)
          rfl lm22_u64_prim rfl rfl rfl rfl rfl rfl) <|
      .cons _ 7 7 8 _ _ trivial
        (.primLeaf (by decide) _ (lm22_constU64_wt 70 (by decide) rfl)
          rfl lm22_u64_prim rfl rfl rfl rfl rfl rfl) <|
      .cons _ 8 8 9 _ _ trivial
        (.primLeaf (by decide) _ (lm22_constU64_wt 80 (by decide) rfl)
          rfl lm22_u64_prim rfl rfl rfl rfl rfl rfl) <|
      .cons _ 9 9 10 _ [] trivial
        (.primLeaf (by decide) _ (lm22_constU8_wt 2 (by decide) rfl)
          rfl lm22_u8_prim rfl rfl rfl rfl rfl rfl) <|
      .nil _ 10))

theorem lm22Realistic80_full_trace_and_returns_agree :
    (∃ mp localAlloc,
      StructMemPlaceRel
        (lm22StepMiriN lm22Realistic80Body 5 lm22Realistic80MiriInit).machine
        lm22Realistic80Ty lm22Realistic80LayoutTable
        lm22Realistic80Fields lm22Realistic80Paths
        (.aggregate 0
          [.scalar ⟨1, 1⟩, .scalar ⟨10, 8⟩, .scalar ⟨20, 8⟩, .scalar ⟨30, 8⟩,
           .scalar ⟨40, 8⟩, .scalar ⟨50, 8⟩, .scalar ⟨60, 8⟩, .scalar ⟨70, 8⟩,
           .scalar ⟨0x1122334455667788, 8⟩, .scalar ⟨0xAB, 1⟩]) mp ∧
      (∃ allocId,
        (∃ tag, mp.ptr.provenance = some (.concrete allocId tag)) ∧
        (lm22StepMiriN lm22Realistic80Body 5 lm22Realistic80MiriInit).machine.memory.live.find?
          (fun (k, _) => k == allocId) = some (allocId, localAlloc)) ∧
      localAlloc.allocation.byteSize = Miri.ABI.Size.ofBytes 80 ∧
      (∀ p, ((1 ≤ p ∧ p ≤ 7) ∨ (73 ≤ p ∧ p ≤ 79)) →
        localAlloc.allocation.initializationMask.get
          (Miri.ABI.Size.ofBytes (UInt64.ofNat p)) = .ok false) ∧
      localAlloc.allocation.initializationMask.isRangeInitialized
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 80)) ≠ .ok (.ok ())) ∧
    get? (lm22StepAnnealN lm22Realistic80Body 6 (initMachineState lm22Realistic80Body [])).frame.locals 2 =
      some (.init (.scalar ⟨0x1122334455667788, 8⟩)) ∧
    annealOutcomeScalarBits 1
      (runAnnealBounded lm22Realistic80Body 10 (initMachineState lm22Realistic80Body [])) = some 0xAB ∧
    miriOutcomeScalarBits 1
      (runMiriBoundedLM2_2 lm22Realistic80Body 10 lm22Realistic80MiriInit) = some 0xAB := by
  have hs0 : StateRelLM2_2 lm22Realistic80Body lm22Realistic80Env
      { initLocals := [], immLocals := [0] } 3
      (lm22StepAnnealN lm22Realistic80Body 0 (initMachineState lm22Realistic80Body []))
      (lm22StepMiriN lm22Realistic80Body 0 lm22Realistic80MiriInit) :=
    lm22Realistic80_stateRelLM2_2_init
  have ⟨hs1, ha0, hm0⟩ := lm22_trace_step ⟨[], [1, 0]⟩ (fuel := 9) hs0
    lm22Realistic80_phase rfl rfl (.storageLive _ 3 1 lm22Realistic80Decl _ rfl) rfl rfl
  have ⟨hs2, ha1, hm1⟩ := lm22_trace_step ⟨[], [2, 1, 0]⟩ (fuel := 8) hs1
    lm22Realistic80_phase rfl rfl (.storageLive _ 3 2 lm22U64Decl _ rfl) rfl rfl
  have ⟨hs3, ha2, hm2⟩ := lm22_trace_step ⟨[1], [2, 0]⟩ (fuel := 7) hs2
    lm22Realistic80_phase rfl rfl (lm22Realistic80_agg_wt _ 2) rfl rfl
  have hdisj_head : ∀ (k : Nat) (ty_k : Ty),
      ∀ j (hj : j < lm22Realistic80Paths.length), j ≠ k →
      DisjointFieldPaths [.field k ty_k] (lm22Realistic80Paths[j]'hj) := by
    intro k ty_k j hj hne
    have hlen_p : lm22Realistic80Paths.length = 10 := rfl
    rw [hlen_p] at hj
    match j with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 =>
      exact .diff_head (Ne.symm hne)
    | _ + 10 => omega
  have hwt3 : WellTypedLM2_2Stmt lm22Realistic80Body lm22Realistic80Env ⟨[1], [2, 0]⟩ 2
      (mkStmt22 (.assign ⟨1, [.field 8 lm22U64Ty]⟩
        (.use (.constant (lm22ConstU64 0x1122334455667788)))))
      (fieldWritePostStaticEnv ⟨[1], [2, 0]⟩ 1
        (.constant (lm22ConstU64 0x1122334455667788))) 1 :=
    .assignFieldWrite _ 1 1 [.field 8 lm22U64Ty]
      (.constant (lm22ConstU64 0x1122334455667788)) _
      (.mk lm22Realistic80Decl lm22Realistic80Fields lm22Realistic80Paths 8
        rfl rfl (by decide) rfl (by decide) (by decide) rfl
        (hdisj_head 8 lm22U64Ty)
        (.single (translateTy lm22Realistic80Ty lm22Realistic80LayoutTable) 8 lm22U64Ty
          (Miri.ABI.Size.ofBytes 64) (Or.inl lm22_u64_prim) rfl rfl (by decide))
        rfl rfl lm22_u64_prim trivial
        (lm22_constU64_wt 0x1122334455667788 (by decide) rfl))
  have ⟨hs4, ha3, hm3⟩ := lm22_trace_step ⟨[1], [2, 0]⟩ (fuel := 6) hs3
    lm22Realistic80_phase rfl rfl hwt3 rfl rfl
  have hwt4 : WellTypedLM2_2Stmt lm22Realistic80Body lm22Realistic80Env ⟨[1], [2, 0]⟩ 1
      (mkStmt22 (.assign ⟨1, [.field 9 u8Ty]⟩ (.use (.constant (constU8 0xAB)))))
      (fieldWritePostStaticEnv ⟨[1], [2, 0]⟩ 1 (.constant (constU8 0xAB))) 0 :=
    .assignFieldWrite _ 0 1 [.field 9 u8Ty] (.constant (constU8 0xAB)) _
      (.mk lm22Realistic80Decl lm22Realistic80Fields lm22Realistic80Paths 9
        rfl rfl (by decide) rfl (by decide) (by decide) rfl
        (hdisj_head 9 u8Ty)
        (.single (translateTy lm22Realistic80Ty lm22Realistic80LayoutTable) 9 u8Ty
          (Miri.ABI.Size.ofBytes 72) (Or.inl lm22_u8_prim) rfl rfl (by decide))
        rfl rfl lm22_u8_prim trivial
        (lm22_constU8_wt 0xAB (by decide) rfl))
  have ⟨hs5, ha4, hm4⟩ := lm22_trace_step ⟨[1], [2, 0]⟩ (fuel := 5) hs4
    lm22Realistic80_phase rfl rfl hwt4 rfl rfl
  have hwt5 : WellTypedLM2_2Stmt lm22Realistic80Body lm22Realistic80Env ⟨[1], [2, 0]⟩ 0
      (mkStmt22 (.assign ⟨2, []⟩ (.use (.copy ⟨1, [.field 8 lm22U64Ty]⟩))))
      (usePostStaticEnv ⟨[1], [2, 0]⟩ 2 (.copy ⟨1, [.field 8 lm22U64Ty]⟩)) 0 :=
    .assignUse _ 0 2 _ _
      (.mk lm22U64Decl rfl (by decide)
        (.projectedScalar false 1 [.field 8 lm22U64Ty] lm22U64Ty rfl
          (.mk lm22Realistic80Decl lm22Realistic80Fields lm22Realistic80Paths 8
            (by decide) (by decide) rfl rfl rfl rfl lm22_u64_prim
            (.single (translateTy lm22Realistic80Ty lm22Realistic80LayoutTable) 8 lm22U64Ty
              (Miri.ABI.Size.ofBytes 64) (Or.inl lm22_u64_prim) rfl rfl (by decide)))))
  have ⟨hs6, ha5, hm5⟩ := lm22_trace_step ⟨[2, 1], [2, 2, 0]⟩ (fuel := 4) hs5
    lm22Realistic80_phase rfl rfl hwt5 rfl rfl
  have hwt6 : WellTypedLM2_2Stmt lm22Realistic80Body lm22Realistic80Env ⟨[2, 1], [2, 2, 0]⟩ 0
      (mkStmt22 (.assign ⟨0, []⟩ (.use (.copy ⟨1, [.field 9 u8Ty]⟩))))
      (usePostStaticEnv ⟨[2, 1], [2, 2, 0]⟩ 0 (.copy ⟨1, [.field 9 u8Ty]⟩)) 0 :=
    .assignUse _ 0 0 _ _
      (.mk u8Decl rfl (by decide)
        (.projectedScalar false 1 [.field 9 u8Ty] u8Ty rfl
          (.mk lm22Realistic80Decl lm22Realistic80Fields lm22Realistic80Paths 9
            (by decide) (by decide) rfl rfl rfl rfl lm22_u8_prim
            (.single (translateTy lm22Realistic80Ty lm22Realistic80LayoutTable) 9 u8Ty
              (Miri.ABI.Size.ofBytes 72) (Or.inl lm22_u8_prim) rfl rfl (by decide)))))
  have ⟨hs7, ha6, hm6⟩ := lm22_trace_step ⟨[0, 2, 1], [0, 2, 2, 0]⟩ (fuel := 3) hs6
    lm22Realistic80_phase rfl rfl hwt6 rfl rfl
  have ⟨hs8, ha7, hm7⟩ := lm22_trace_step ⟨[2, 0, 2, 1], [2, 0, 2, 2, 0]⟩ (fuel := 2) hs7
    lm22Realistic80_phase rfl rfl (.storageDead _ 0 2 lm22U64Decl _ rfl (by decide)) rfl rfl
  have ⟨hs9, ha8, hm8⟩ := lm22_trace_step ⟨[1, 2, 0, 2, 1], [1, 2, 0, 2, 2, 0]⟩ (fuel := 1) hs8
    lm22Realistic80_phase rfl rfl (.storageDead _ 0 1 lm22Realistic80Decl _ rfl (by decide)) rfl rfl
  have hpad5 :
      ∃ mp localAlloc,
        StructMemPlaceRel
          (lm22StepMiriN lm22Realistic80Body 5 lm22Realistic80MiriInit).machine
          lm22Realistic80Ty lm22Realistic80LayoutTable
          lm22Realistic80Fields lm22Realistic80Paths
          (.aggregate 0
            [.scalar ⟨1, 1⟩, .scalar ⟨10, 8⟩, .scalar ⟨20, 8⟩, .scalar ⟨30, 8⟩,
             .scalar ⟨40, 8⟩, .scalar ⟨50, 8⟩, .scalar ⟨60, 8⟩, .scalar ⟨70, 8⟩,
             .scalar ⟨0x1122334455667788, 8⟩, .scalar ⟨0xAB, 1⟩]) mp ∧
        (∃ allocId,
          (∃ tag, mp.ptr.provenance = some (.concrete allocId tag)) ∧
          (lm22StepMiriN lm22Realistic80Body 5 lm22Realistic80MiriInit).machine.memory.live.find?
            (fun (k, _) => k == allocId) = some (allocId, localAlloc)) ∧
        localAlloc.allocation.byteSize = Miri.ABI.Size.ofBytes 80 ∧
        (∀ p, ((1 ≤ p ∧ p ≤ 7) ∨ (73 ≤ p ∧ p ≤ 79)) →
          localAlloc.allocation.initializationMask.get
            (Miri.ABI.Size.ofBytes (UInt64.ofNat p)) = .ok false) ∧
        localAlloc.allocation.initializationMask.isRangeInitialized
          (Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 80)) ≠ .ok (.ok ()) := by
    obtain ⟨mp, _, _, _, _, hsmpr⟩ :=
      hs5.extract_structMemPlaceRel (idx := 1) (decl := lm22Realistic80Decl) rfl rfl rfl rfl
    have hp1 := lm22Realistic80_all_padding_bytes 1 (Or.inl ⟨by decide, by decide⟩)
    obtain ⟨allocId, localAlloc, hprov, hfind, hpad_fn, hhas_uninit⟩ :=
      hsmpr.has_uninit_of_padding_byte hp1
    have hbs : localAlloc.allocation.byteSize = Miri.ABI.Size.ofBytes 80 := by
      obtain ⟨aid, tag, b, la, hprov', hfind', hbs⟩ := StructMemPlaceRel.byteSize_eq hsmpr
      obtain ⟨tag, hprov_eq⟩ := hprov; cases Option.some.inj (hprov_eq.symm.trans hprov')
      cases Option.some.inj (hfind.symm.trans hfind')
      exact hbs
    exact ⟨mp, localAlloc, hsmpr, ⟨allocId, hprov, hfind⟩, hbs,
      fun p hp => hpad_fn p (lm22Realistic80_all_padding_bytes p hp), hhas_uninit⟩
  obtain ⟨ha_ret, hm_ret⟩ := lm22_return_agree_of_stateRelLM2_2 hs9 lm22Realistic80_phase
    rfl rfl rfl rfl rfl rfl rfl lm22_u8_prim (by decide) rfl
  have ha_tot :
      runAnnealBounded lm22Realistic80Body 10 (initMachineState lm22Realistic80Body []) =
        runAnnealBounded lm22Realistic80Body 1
          (lm22StepAnnealN lm22Realistic80Body 9 (initMachineState lm22Realistic80Body [])) :=
    ha0.trans (ha1.trans (ha2.trans (ha3.trans (ha4.trans (ha5.trans (ha6.trans (ha7.trans ha8)))))))
  have hm_tot :
      runMiriBoundedLM2_2 lm22Realistic80Body 10 lm22Realistic80MiriInit =
        runMiriBoundedLM2_2 lm22Realistic80Body 1
          (lm22StepMiriN lm22Realistic80Body 9 lm22Realistic80MiriInit) :=
    hm0.trans (hm1.trans (hm2.trans (hm3.trans (hm4.trans (hm5.trans (hm6.trans (hm7.trans hm8)))))))
  rw [ha_tot, hm_tot]
  exact ⟨hpad5, rfl, ha_ret, hm_ret⟩


/-! ## 12. Immediate `.ScalarPair` Outer Aggregate with `.Scalar` Wrapper

`PairWithWrap { a: u32, b: InnerU32 }` witnesses the `LocalRelLM2_2.structImm`
(`ImmediateStructRel.scalarPair`) branch of
`WellTypedLM2_2ProjectedScalarWrapRead` and
`evalOperand_nested_scalar_wrap_read_simulation`:
1. constructs `_1 = PairWithWrap(0x11223344_u32, move _2)` in stack memory
   (`scalarWrapSub`),
2. copies `_3 = copy _1` into an immediate `.structImm` `ScalarPair` local `_3`,
3. reads the whole 1-field `.Scalar` wrapper `_4 = copy _3.1` directly out of
   `.Immediate.scalarPair` without forcing `_3` to memory, and
4. reads `_0 = copy _4.0` (`0x13579BDF_u32`) and returns in lockstep. -/

def lm22PairWrapTy : Ty :=
  { kind := .adt "lm22::PairWithWrap" [], layoutIdx := 0 }

def lm22PairWrapDecl : LocalDecl :=
  { mutability := .mut, ty := lm22PairWrapTy, debugName := none }

def lm22PairWrapTypeLayout : TypeLayout :=
  { size := { bytes := 8 }
    align := { bytes := 4 }
    backendRepr :=
      .scalarPair
        (.initialized (.int 32 false) { start := 0, end_ := 4294967295 })
        (.initialized (.int 32 false) { start := 0, end_ := 4294967295 })
    fields := .arbitrary [{ bytes := 0 }, { bytes := 4 }] [0, 1]
    variants := .single 0
    isUninhabited := false
    fieldLayouts := [2, 1] }

def lm22PairWrapLayoutTable : LayoutTable :=
  { pointerBits := 64
    isLittleEndian := true
    entries :=
      [lm22PairWrapTypeLayout, lm22InnerU32TypeLayout,
       lm22U32TypeLayout, lm22U8TypeLayout] }

def lm22PairWrapField0 : StructFieldDesc :=
  { offset := Miri.ABI.Size.ZERO
    ty := lm22U32Ty
    fieldLayout := (translateTy lm22U32Ty lm22PairWrapLayoutTable).layout }

def lm22PairWrapField1 : StructFieldDesc :=
  { offset := Miri.ABI.Size.ofBytes 4
    ty := lm22U32Ty
    fieldLayout := (translateTy lm22U32Ty lm22PairWrapLayoutTable).layout }

def lm22PairWrapFields : List StructFieldDesc :=
  [lm22PairWrapField0, lm22PairWrapField1]

def lm22PairWrapPaths : List (List ProjectionElem) :=
  [[.field 0 lm22U32Ty], [.field 1 lm22InnerU32Ty, .field 0 lm22U32Ty]]

def lm22PairWrapEnv : StructTypeEnv := fun ty =>
  match ty.kind with
  | .adt "lm22::InnerU32" [] => some ([lm22InnerU32Field0], [[.field 0 lm22U32Ty]])
  | .adt "lm22::PairWithWrap" [] => some (lm22PairWrapFields, lm22PairWrapPaths)
  | _ => none

theorem lm22PairWrap_inner_validStructLayout :
    ValidStructLayout (translateTy lm22InnerU32Ty lm22PairWrapLayoutTable).layout
      [lm22InnerU32Field0] :=
  lm22InnerU32_validStructLayout

theorem lm22PairWrap_inner_isImmediateStructTy :
    IsImmediateStructTy lm22PairWrapEnv lm22PairWrapLayoutTable lm22InnerU32Ty
      [lm22InnerU32Field0] [[.field 0 lm22U32Ty]] :=
  .scalarWrapper lm22InnerU32Field0 [.field 0 lm22U32Ty] _
    rfl lm22PairWrap_inner_validStructLayout rfl rfl nofun
    (.single (translateTy lm22InnerU32Ty lm22PairWrapLayoutTable) lm22U32Ty
      lm22_u32_prim rfl rfl)
    rfl rfl lm22_u32_prim

theorem lm22PairWrap_validStructLayout :
    ValidStructLayout (translateTy lm22PairWrapTy lm22PairWrapLayoutTable).layout
      lm22PairWrapFields := by
  refine
    { fields_in_bounds := fun i hi => by
        match i with
        | 0 | 1 => decide +revert
        | _ + 2 => simp [lm22PairWrapFields] at hi; omega
      fields_disjoint := fun i j hi hj hne => by
        match i, j with
        | 0, 0 | 1, 1 => exact False.elim (hne rfl)
        | 0, 1 => left; decide +revert
        | 1, 0 => right; decide +revert
        | _ + 2, _ => simp [lm22PairWrapFields] at hi; omega
        | _, _ + 2 => simp [lm22PairWrapFields] at hj; omega
      fields_aligned := fun i hi => by
        match i with
        | 0 | 1 => decide +revert
        | _ + 2 => simp [lm22PairWrapFields] at hi; omega
      fields_shape_valid := Or.inr (ValidStructLayout.arbitrary_flat #[0, 1] rfl (by decide)) }

theorem lm22PairWrap_isImmediateStructTy :
    IsImmediateStructTy lm22PairWrapEnv lm22PairWrapLayoutTable lm22PairWrapTy
      lm22PairWrapFields lm22PairWrapPaths :=
  .scalarPair lm22PairWrapField0 lm22PairWrapField1
    lm22U32Ty lm22InnerU32Ty [] [.field 0 lm22U32Ty]
    _ _ (Miri.ABI.Size.ofBytes 4)
    rfl lm22PairWrap_validStructLayout (by decide)
    (Or.inr ⟨"lm22::PairWithWrap", [], rfl⟩)
    (fun _ h => nomatch h)
    rfl (by decide) (by decide) (by decide) (by decide)
    rfl rfl rfl rfl
    (Or.inl lm22_u32_prim) (Or.inr (Or.inr ⟨"lm22::InnerU32", [], rfl⟩))
    lm22_u32_prim lm22_u32_prim
    (Or.inl ⟨rfl, rfl⟩)
    (Or.inr ⟨⟨rfl, rfl, rfl, nofun⟩,
      .single (translateTy lm22InnerU32Ty lm22PairWrapLayoutTable) lm22U32Ty
        lm22_u32_prim rfl rfl⟩)

def lm22PairWrapBody : CapturedMir where
  defPath := "lm_2_2_witness::scalar_pair_with_scalar_wrapper"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls :=
    [lm22U32Decl, lm22PairWrapDecl, lm22InnerU32Decl, lm22PairWrapDecl, lm22InnerU32Decl]
  basicBlocks := [
    { statements := [
        mkStmt22 (.storageLive 1),
        mkStmt22 (.storageLive 2),
        mkStmt22 (.storageLive 3),
        mkStmt22 (.storageLive 4),
        mkStmt22 (.assign ⟨2, []⟩
          (.aggregate (.adt "lm22::InnerU32" 0 .none)
            [.constant (lm22ConstU32 0x13579BDF)])),
        mkStmt22 (.assign ⟨1, []⟩
          (.aggregate (.adt "lm22::PairWithWrap" 0 .none)
            [.constant (lm22ConstU32 0x11223344), .move ⟨2, []⟩])),
        mkStmt22 (.assign ⟨3, []⟩ (.use (.copy ⟨1, []⟩))),
        mkStmt22 (.assign ⟨4, []⟩ (.use (.copy ⟨3, [.field 1 lm22InnerU32Ty]⟩))),
        mkStmt22 (.assign ⟨0, []⟩ (.use (.copy ⟨4, [.field 0 lm22U32Ty]⟩))),
        mkStmt22 (.storageDead 4),
        mkStmt22 (.storageDead 3),
        mkStmt22 (.storageDead 2),
        mkStmt22 (.storageDead 1)],
      terminator := mkTerm22 .return_,
      isCleanup := false }]
  fnAbi := lm22FnAbiU32
  layouts := lm22PairWrapLayoutTable
  allocations := []

def lm22PairWrapMiriInit : AnnealStepState :=
  { stack := ⟨#[{
      body := translateBody lm22PairWrapBody
      bodyIdentity := .ofCanonicalIndex 0
      functionInstance := { kind := .Item 0, args := #[] }
      extra := ()
      returnContinuation := .stop false
      returnPlace :=
        .frameLocal 0 0 none (translateTy lm22U32Ty lm22PairWrapLayoutTable) (.ofAllocationToken 0)
      localsIdentity := .ofAllocationToken 0
      locals := #[
        { value := .live (.immediate .uninit), layout := none },
        { value := .dead, layout := none },
        { value := .dead, layout := none },
        { value := .dead, layout := none },
        { value := .dead, layout := none }]
      vaList := #[]
      trackCallerArg := none
      location := .mir ⟨0, 0⟩ }]⟩
    machine := AnnealMachine.empty }

theorem lm22PairWrap_phase : ∀ p, lm22PairWrapBody.phase ≠ .other p := by
  intro p h; cases h

theorem lm22PairWrap_stateRelLM2_2_init :
    StateRelLM2_2 lm22PairWrapBody lm22PairWrapEnv { initLocals := [], immLocals := [0] } 3
      (initMachineState lm22PairWrapBody []) lm22PairWrapMiriInit := by
  refine .mk _ rfl rfl ⟨translateTy lm22U32Ty lm22PairWrapLayoutTable, rfl⟩ ?_
    (fun _ h => nomatch h)
    (fun j hj mp l => by simp at hj; subst hj; dsimp [lm22PairWrapMiriInit]; nofun)
    (Or.inr (AllocIdWatermark.empty 3 (by decide))) rfl rfl rfl rfl rfl
    (by intro i _ _ _ _ _ _ hi _; revert hi
        match i with | 0 | 1 | 2 | 3 | 4 | _ + 5 => rintro ⟨⟩)
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro i decl slot mls hdecl hslot hmls
  match i with
  | 0 =>
    cases Option.some.inj hdecl
    cases Option.some.inj hslot
    cases Option.some.inj hmls
    exact .base .uninit _ rfl
      (.immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩))
  | 1 | 3 =>
    cases Option.some.inj hdecl
    cases Option.some.inj hslot
    cases Option.some.inj hmls
    exact .structDead lm22PairWrapFields lm22PairWrapPaths none rfl (fun _ h => nomatch h)
  | 2 | 4 =>
    cases Option.some.inj hdecl
    cases Option.some.inj hslot
    cases Option.some.inj hmls
    exact .structDead [lm22InnerU32Field0] [[.field 0 lm22U32Ty]] none rfl (fun _ h => nomatch h)
  | _ + 5 => simp [lm22PairWrapBody, get?] at hdecl

theorem lm22PairWrap_read_wt :
    WellTypedLM2_2ProjectedScalarWrapRead lm22PairWrapBody lm22PairWrapEnv
      3 [.field 1 lm22InnerU32Ty] lm22InnerU32Ty lm22InnerU32Field0 lm22U32Ty :=
  .mk lm22PairWrapDecl lm22PairWrapFields lm22PairWrapPaths 1
    (by decide) (by decide) (Miri.ABI.Size.ofBytes 4) _
    rfl rfl rfl rfl rfl rfl rfl (by decide)
    rfl rfl rfl rfl
    lm22PairWrap_inner_validStructLayout (by decide) rfl
    (.single (translateTy lm22InnerU32Ty lm22PairWrapLayoutTable) lm22U32Ty
      lm22_u32_prim rfl rfl)
    lm22_u32_prim
    (.single (translateTy lm22PairWrapTy lm22PairWrapLayoutTable) 1 lm22InnerU32Ty
      (Miri.ABI.Size.ofBytes 4) (Or.inr (Or.inr ⟨"lm22::InnerU32", [], rfl⟩))
      rfl rfl (by decide))

theorem lm22PairWrap_full_trace_and_returns_agree :
    (∃ imm3,
      ImmediateStructRel lm22PairWrapTy lm22PairWrapLayoutTable
        lm22PairWrapFields lm22PairWrapPaths
        (.aggregate 0 [.scalar ⟨0x11223344, 4⟩, .aggregate 0 [.scalar ⟨0x13579BDF, 4⟩]]) imm3) ∧
    (∃ imm4,
      ImmediateStructRel lm22InnerU32Ty lm22PairWrapLayoutTable
        [lm22InnerU32Field0] [[.field 0 lm22U32Ty]]
        (.aggregate 0 [.scalar ⟨0x13579BDF, 4⟩]) imm4) ∧
    annealOutcomeScalarBits 4
      (runAnnealBounded lm22PairWrapBody 14 (initMachineState lm22PairWrapBody [])) =
        some 0x13579BDF ∧
    miriOutcomeScalarBits 4
      (runMiriBoundedLM2_2 lm22PairWrapBody 14 lm22PairWrapMiriInit) = some 0x13579BDF := by
  have hs0 :
      StateRelLM2_2 lm22PairWrapBody lm22PairWrapEnv { initLocals := [], immLocals := [0] } 3
        (lm22StepAnnealN lm22PairWrapBody 0 (initMachineState lm22PairWrapBody []))
        (lm22StepMiriN lm22PairWrapBody 0 lm22PairWrapMiriInit) :=
    lm22PairWrap_stateRelLM2_2_init
  have ⟨hs1, ha0, hm0⟩ := lm22_trace_step ⟨[], [1, 0]⟩ (fuel := 13) hs0
    lm22PairWrap_phase rfl rfl (.storageLive _ 3 1 lm22PairWrapDecl _ rfl) rfl rfl
  have ⟨hs2, ha1, hm1⟩ := lm22_trace_step ⟨[], [2, 1, 0]⟩ (fuel := 12) hs1
    lm22PairWrap_phase rfl rfl (.storageLive _ 3 2 lm22InnerU32Decl _ rfl) rfl rfl
  have ⟨hs3, ha2, hm2⟩ := lm22_trace_step ⟨[], [3, 2, 1, 0]⟩ (fuel := 11) hs2
    lm22PairWrap_phase rfl rfl (.storageLive _ 3 3 lm22PairWrapDecl _ rfl) rfl rfl
  have ⟨hs4, ha3, hm3⟩ := lm22_trace_step ⟨[], [4, 3, 2, 1, 0]⟩ (fuel := 10) hs3
    lm22PairWrap_phase rfl rfl (.storageLive _ 3 4 lm22InnerU32Decl _ rfl) rfl rfl
  have hwt4 : WellTypedLM2_2Stmt lm22PairWrapBody lm22PairWrapEnv ⟨[], [4, 3, 2, 1, 0]⟩ 3
      (mkStmt22 (.assign ⟨2, []⟩
        (.aggregate (.adt "lm22::InnerU32" 0 .none) [.constant (lm22ConstU32 0x13579BDF)])))
      (aggPostStaticEnv ⟨[], [4, 3, 2, 1, 0]⟩ 2 [.constant (lm22ConstU32 0x13579BDF)]) 2 :=
    .assignAggregate _ 2 2 _ _ _
      (.mk lm22InnerU32Decl [lm22InnerU32Field0] [[.field 0 lm22U32Ty]] _ [] rfl
        (Or.inr ⟨"lm22::InnerU32", rfl⟩) rfl rfl lm22PairWrap_inner_validStructLayout
        (by decide) rfl rfl (by decide)
        (.cons _ 0 0 1 _ [] trivial
          (.primLeaf (by decide) _ (lm22_constU32_wt 0x13579BDF (by decide) rfl)
            rfl lm22_u32_prim rfl rfl rfl rfl rfl rfl)
          (.nil _ 1)))
  have ⟨hs5, ha4, hm4⟩ := lm22_trace_step ⟨[2], [4, 3, 1, 0]⟩ (fuel := 9) hs4
    lm22PairWrap_phase rfl rfl hwt4 rfl rfl
  have hwt5 : WellTypedLM2_2Stmt lm22PairWrapBody lm22PairWrapEnv ⟨[2], [4, 3, 1, 0]⟩ 2
      (mkStmt22 (.assign ⟨1, []⟩
        (.aggregate (.adt "lm22::PairWithWrap" 0 .none)
          [.constant (lm22ConstU32 0x11223344), .move ⟨2, []⟩])))
      (aggPostStaticEnv ⟨[2], [4, 3, 1, 0]⟩ 1
        [.constant (lm22ConstU32 0x11223344), .move ⟨2, []⟩]) 1 :=
    .assignAggregate _ 1 1 _ _ _
      (.mk lm22PairWrapDecl lm22PairWrapFields lm22PairWrapPaths _ _ rfl
        (Or.inr ⟨"lm22::PairWithWrap", rfl⟩) rfl rfl lm22PairWrap_validStructLayout
        (by decide) rfl rfl (by decide)
        (.cons _ 0 0 1 _ _ trivial
          (.primLeaf (by decide) _ (lm22_constU32_wt 0x11223344 (by decide) rfl)
            rfl lm22_u32_prim rfl rfl rfl rfl rfl rfl)
          (.cons _ 1 1 2 (.move ⟨2, []⟩) [] (by decide : (2 : Nat) ≠ 1)
            (.scalarWrapSub (by decide) lm22InnerU32Ty lm22InnerU32Field0
              [.field 0 lm22U32Ty] _
              (.immStructLocal true 2 lm22InnerU32Decl [lm22InnerU32Field0]
                [[.field 0 lm22U32Ty]] rfl lm22PairWrap_inner_isImmediateStructTy)
              lm22PairWrap_inner_isImmediateStructTy rfl rfl rfl rfl rfl rfl rfl)
            (.nil _ 2))))
  have ⟨hs6, ha5, hm5⟩ := lm22_trace_step ⟨[1], [2, 4, 3, 0]⟩ (fuel := 8) hs5
    lm22PairWrap_phase rfl rfl hwt5 rfl rfl
  have hwt6 : WellTypedLM2_2Stmt lm22PairWrapBody lm22PairWrapEnv ⟨[1], [2, 4, 3, 0]⟩ 1
      (mkStmt22 (.assign ⟨3, []⟩ (.use (.copy ⟨1, []⟩))))
      (usePostStaticEnv ⟨[1], [2, 4, 3, 0]⟩ 3 (.copy ⟨1, []⟩)) 1 :=
    .assignUse _ 1 3 (.copy ⟨1, []⟩) _
      (.mk lm22PairWrapDecl rfl (by decide)
        (.immStructLocal false 1 lm22PairWrapDecl lm22PairWrapFields lm22PairWrapPaths
          rfl lm22PairWrap_isImmediateStructTy))
  have ⟨hs7, ha6, hm6⟩ := lm22_trace_step ⟨[3, 1], [3, 2, 4, 3, 0]⟩ (fuel := 7) hs6
    lm22PairWrap_phase rfl rfl hwt6 rfl rfl
  have hwt7 : WellTypedLM2_2Stmt lm22PairWrapBody lm22PairWrapEnv ⟨[3, 1], [3, 2, 4, 3, 0]⟩ 1
      (mkStmt22 (.assign ⟨4, []⟩ (.use (.copy ⟨3, [.field 1 lm22InnerU32Ty]⟩))))
      (usePostStaticEnv ⟨[3, 1], [3, 2, 4, 3, 0]⟩ 4 (.copy ⟨3, [.field 1 lm22InnerU32Ty]⟩)) 1 :=
    .assignUse _ 1 4 (.copy ⟨3, [.field 1 lm22InnerU32Ty]⟩) _
      (.mk lm22InnerU32Decl rfl (by decide)
        (.projectedScalarWrap false 3 [.field 1 lm22InnerU32Ty] lm22InnerU32Ty
          lm22InnerU32Field0 lm22U32Ty
          lm22PairWrap_inner_isImmediateStructTy lm22PairWrap_read_wt))
  have ⟨hs8, ha7, hm7⟩ := lm22_trace_step ⟨[4, 3, 1], [4, 3, 2, 4, 3, 0]⟩ (fuel := 6) hs7
    lm22PairWrap_phase rfl rfl hwt7 rfl rfl
  have hwt8 : WellTypedLM2_2Stmt lm22PairWrapBody lm22PairWrapEnv ⟨[4, 3, 1], [4, 3, 2, 4, 3, 0]⟩ 1
      (mkStmt22 (.assign ⟨0, []⟩ (.use (.copy ⟨4, [.field 0 lm22U32Ty]⟩))))
      (usePostStaticEnv ⟨[4, 3, 1], [4, 3, 2, 4, 3, 0]⟩ 0 (.copy ⟨4, [.field 0 lm22U32Ty]⟩)) 1 :=
    .assignUse _ 1 0 (.copy ⟨4, [.field 0 lm22U32Ty]⟩) _
      (.mk lm22U32Decl rfl (by decide)
        (.projectedScalar false 4 [.field 0 lm22U32Ty] lm22U32Ty rfl
          (.mk lm22InnerU32Decl [lm22InnerU32Field0] [[.field 0 lm22U32Ty]] 0
            (by decide) (by decide) rfl rfl rfl rfl lm22_u32_prim
            (.single (translateTy lm22InnerU32Ty lm22PairWrapLayoutTable) 0 lm22U32Ty
              Miri.ABI.Size.ZERO (Or.inl lm22_u32_prim) rfl rfl (by decide)))))
  have ⟨hs9, ha8, hm8⟩ := lm22_trace_step ⟨[0, 4, 3, 1], [0, 4, 3, 2, 4, 3, 0]⟩ (fuel := 5) hs8
    lm22PairWrap_phase rfl rfl hwt8 rfl rfl
  have ⟨hs10, ha9, hm9⟩ := lm22_trace_step ⟨[4, 0, 4, 3, 1], [4, 0, 4, 3, 2, 4, 3, 0]⟩ (fuel := 4) hs9
    lm22PairWrap_phase rfl rfl (.storageDead _ 1 4 lm22InnerU32Decl _ rfl (by decide)) rfl rfl
  have ⟨hs11, ha10, hm10⟩ := lm22_trace_step ⟨[3, 4, 0, 4, 3, 1], [3, 4, 0, 4, 3, 2, 4, 3, 0]⟩ (fuel := 3) hs10
    lm22PairWrap_phase rfl rfl (.storageDead _ 1 3 lm22PairWrapDecl _ rfl (by decide)) rfl rfl
  have ⟨hs12, ha11, hm11⟩ := lm22_trace_step ⟨[2, 3, 4, 0, 4, 3, 1], [2, 3, 4, 0, 4, 3, 2, 4, 3, 0]⟩ (fuel := 2) hs11
    lm22PairWrap_phase rfl rfl (.storageDead _ 1 2 lm22InnerU32Decl _ rfl (by decide)) rfl rfl
  have ⟨hs13, ha12, hm12⟩ := lm22_trace_step ⟨[1, 2, 3, 4, 0, 4, 3, 1], [1, 2, 3, 4, 0, 4, 3, 2, 4, 3, 0]⟩ (fuel := 1) hs12
    lm22PairWrap_phase rfl rfl (.storageDead _ 1 1 lm22PairWrapDecl _ rfl (by decide)) rfl rfl
  have himm3 :
      ∃ imm3,
        ImmediateStructRel lm22PairWrapTy lm22PairWrapLayoutTable
          lm22PairWrapFields lm22PairWrapPaths
          (.aggregate 0 [.scalar ⟨0x11223344, 4⟩, .aggregate 0 [.scalar ⟨0x13579BDF, 4⟩]]) imm3 := by
    rcases hs7 with ⟨tf7, _, _, _, hfr7, _, himm7, _, _, _, _, _, _, _⟩
    obtain ⟨_, mls7, _, _, hslot7, hmls7, _, hloc7⟩ :=
      hfr7.lookup_local (idx := 3) (decl := lm22PairWrapDecl) rfl
    have hsl7 : get? (lm22StepAnnealN lm22PairWrapBody 7
        (initMachineState lm22PairWrapBody [])).frame.locals 3 =
        some (.init (.aggregate 0 [.scalar ⟨0x11223344, 4⟩, .aggregate 0 [.scalar ⟨0x13579BDF, 4⟩]])) := rfl
    rw [hsl7] at hslot7; cases Option.some.inj hslot7
    cases hloc7 with
    | base _ _ he _ => cases he
    | structImm _ _ _ imm _ henv' _ himm =>
      rcases Prod.mk.inj (Option.some.inj henv') with ⟨rfl, rfl⟩
      exact ⟨imm, himm⟩
    | structInd _ _ _ mp lay _ _ _ =>
      exact False.elim (himm7 3 (by decide) mp lay hmls7)
  have himm4 :
      ∃ imm4,
        ImmediateStructRel lm22InnerU32Ty lm22PairWrapLayoutTable
          [lm22InnerU32Field0] [[.field 0 lm22U32Ty]]
          (.aggregate 0 [.scalar ⟨0x13579BDF, 4⟩]) imm4 := by
    rcases hs8 with ⟨tf8, _, _, _, hfr8, _, himm8, _, _, _, _, _, _, _⟩
    obtain ⟨_, mls8, _, _, hslot8, hmls8, _, hloc8⟩ :=
      hfr8.lookup_local (idx := 4) (decl := lm22InnerU32Decl) rfl
    have hsl8 : get? (lm22StepAnnealN lm22PairWrapBody 8
        (initMachineState lm22PairWrapBody [])).frame.locals 4 =
        some (.init (.aggregate 0 [.scalar ⟨0x13579BDF, 4⟩])) := rfl
    rw [hsl8] at hslot8; cases Option.some.inj hslot8
    cases hloc8 with
    | base _ _ he _ => cases he
    | structImm _ _ _ imm _ henv' _ himm =>
      rcases Prod.mk.inj (Option.some.inj henv') with ⟨rfl, rfl⟩
      exact ⟨imm, himm⟩
    | structInd _ _ _ mp lay _ _ _ =>
      exact False.elim (himm8 4 (by decide) mp lay hmls8)
  obtain ⟨ha_ret, hm_ret⟩ := lm22_return_agree_of_stateRelLM2_2 hs13 lm22PairWrap_phase
    rfl rfl rfl rfl rfl rfl rfl lm22_u32_prim (by decide) rfl
  have ha_tot :
      runAnnealBounded lm22PairWrapBody 14 (initMachineState lm22PairWrapBody []) =
        runAnnealBounded lm22PairWrapBody 1
          (lm22StepAnnealN lm22PairWrapBody 13 (initMachineState lm22PairWrapBody [])) :=
    ha0.trans (ha1.trans (ha2.trans (ha3.trans (ha4.trans (ha5.trans (ha6.trans
      (ha7.trans (ha8.trans (ha9.trans (ha10.trans (ha11.trans ha12)))))))))))
  have hm_tot :
      runMiriBoundedLM2_2 lm22PairWrapBody 14 lm22PairWrapMiriInit =
        runMiriBoundedLM2_2 lm22PairWrapBody 1 (lm22StepMiriN lm22PairWrapBody 13 lm22PairWrapMiriInit) :=
    hm0.trans (hm1.trans (hm2.trans (hm3.trans (hm4.trans (hm5.trans (hm6.trans
      (hm7.trans (hm8.trans (hm9.trans (hm10.trans (hm11.trans hm12)))))))))))
  rw [ha_tot, hm_tot]
  exact ⟨himm3, himm4, ha_ret, hm_ret⟩


/-! ## 13. `.Memory` Struct Move-Then-Use UB Parity & Read-Only Copy UB Parity

Witnesses two UB parity paths for `annealStructMemCopyOp`:
1. **`lm22MemMoveUbBody`**: after `_3 = move _2` deinitializes `.Memory` struct
   `_2` into `.uninit` / `.live (.immediate .uninit)` (`2 ∈ stEnv.immLocals`),
   reading `_4 = copy _2` is syntactically well-typed via
   `WellTypedLM2_2UseAssignMemStruct` (`Or.inr (2 ∈ stEnv.immLocals)`) and
   faults with UB on both Anneal and `lean-miri` via
   `step_assign_use_memory_struct_lm2_2_simulation`.
2. **`lm22ReadOnlyCopy_ub`**: when both source and destination allocations have
   `Mutability.Not` (`destAlloc.mutability == .Mut` is `false`),
   `annealStructMemCopyOp` bypasses `isWholeStructAllocationCopy`, delegates to
   `Miri.Memory.Allocation.copy` (which returns `.error .readOnlyAllocation`),
   and raises `.undefinedBehavior "write to read-only allocation"`. -/

def lm22MemMoveUbBody : CapturedMir where
  defPath := "lm_2_2_witness::nested_memory_move_then_use_ub"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls :=
    [u16Decl, lm22InnerPairDecl, lm22NestedDecl, lm22NestedDecl, lm22NestedDecl]
  basicBlocks := [
    { statements := [
        mkStmt22 (.storageLive 1),
        mkStmt22 (.storageLive 2),
        mkStmt22 (.storageLive 3),
        mkStmt22 (.storageLive 4),
        mkStmt22 (.assign ⟨1, []⟩
          (.aggregate (.adt "lm22::InnerPair" 0 .none)
            [.constant (lm22ConstU32 0x11112222), .constant (constU16 0x3344)])),
        mkStmt22 (.assign ⟨2, []⟩
          (.aggregate (.adt "lm22::NestedOuter" 0 .none)
            [.constant (constU8 7), .move ⟨1, []⟩])),
        mkStmt22 (.assign ⟨3, []⟩ (.use (.move ⟨2, []⟩))),
        mkStmt22 (.assign ⟨4, []⟩ (.use (.copy ⟨2, []⟩)))],
      terminator := mkTerm22 .return_,
      isCleanup := false }]
  fnAbi := lm22FnAbiU16
  layouts := lm22NestedLayoutTable
  allocations := []

def lm22MemMoveUbMiriInit : AnnealStepState :=
  { stack := ⟨#[{
      body := translateBody lm22MemMoveUbBody
      bodyIdentity := .ofCanonicalIndex 0
      functionInstance := { kind := .Item 0, args := #[] }
      extra := ()
      returnContinuation := .stop false
      returnPlace :=
        .frameLocal 0 0 none (translateTy u16Ty lm22NestedLayoutTable) (.ofAllocationToken 0)
      localsIdentity := .ofAllocationToken 0
      locals := #[
        { value := .live (.immediate .uninit), layout := none },
        { value := .dead, layout := none },
        { value := .dead, layout := none },
        { value := .dead, layout := none },
        { value := .dead, layout := none }]
      vaList := #[]
      trackCallerArg := none
      location := .mir ⟨0, 0⟩ }]⟩
    machine := AnnealMachine.empty }

theorem lm22MemMoveUb_phase : ∀ p, lm22MemMoveUbBody.phase ≠ .other p := by
  intro p h; cases h

theorem lm22MemMoveUb_stateRelLM2_2_init :
    StateRelLM2_2 lm22MemMoveUbBody lm22NestedEnv { initLocals := [], immLocals := [0] } 5
      (initMachineState lm22MemMoveUbBody []) lm22MemMoveUbMiriInit := by
  refine .mk _ rfl rfl ⟨translateTy u16Ty lm22NestedLayoutTable, rfl⟩ ?_
    (fun _ h => nomatch h)
    (fun j hj mp l => by simp at hj; subst hj; dsimp [lm22MemMoveUbMiriInit]; nofun)
    (Or.inr (AllocIdWatermark.empty 5 (by decide))) rfl rfl rfl rfl rfl
    (by intro i _ _ _ _ _ _ hi _; revert hi
        match i with | 0 | 1 | 2 | 3 | 4 | _ + 5 => rintro ⟨⟩)
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro i decl slot mls hdecl hslot hmls
  match i with
  | 0 =>
    cases Option.some.inj hdecl
    cases Option.some.inj hslot
    cases Option.some.inj hmls
    exact .base .uninit _ rfl
      (.immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩))
  | 1 =>
    cases Option.some.inj hdecl
    cases Option.some.inj hslot
    cases Option.some.inj hmls
    exact .structDead lm22InnerPairFields lm22InnerPairPaths none rfl (fun _ h => nomatch h)
  | 2 | 3 | 4 =>
    cases Option.some.inj hdecl
    cases Option.some.inj hslot
    cases Option.some.inj hmls
    exact .structDead lm22NestedFields lm22NestedPaths none rfl (fun _ h => nomatch h)
  | _ + 5 => simp [lm22MemMoveUbBody, get?] at hdecl

theorem lm22MemMoveUb_faults_with_ub_on_both :
    runAnnealBounded lm22MemMoveUbBody 8 (initMachineState lm22MemMoveUbBody []) =
      .faulted .ub ∧
    ∃ m_err msg,
      runMiriBoundedLM2_2 lm22MemMoveUbBody 8 lm22MemMoveUbMiriInit =
        .error m_err (.undefinedBehavior msg) := by
  have hs0 :
      StateRelLM2_2 lm22MemMoveUbBody lm22NestedEnv { initLocals := [], immLocals := [0] } 5
        (lm22StepAnnealN lm22MemMoveUbBody 0 (initMachineState lm22MemMoveUbBody []))
        (lm22StepMiriN lm22MemMoveUbBody 0 lm22MemMoveUbMiriInit) :=
    lm22MemMoveUb_stateRelLM2_2_init
  have ⟨hs1, ha0, hm0⟩ := lm22_trace_step ⟨[], [1, 0]⟩ (fuel := 7) hs0
    lm22MemMoveUb_phase rfl rfl (.storageLive _ 5 1 lm22InnerPairDecl _ rfl) rfl rfl
  have ⟨hs2, ha1, hm1⟩ := lm22_trace_step ⟨[], [2, 1, 0]⟩ (fuel := 6) hs1
    lm22MemMoveUb_phase rfl rfl (.storageLive _ 5 2 lm22NestedDecl _ rfl) rfl rfl
  have ⟨hs3, ha2, hm2⟩ := lm22_trace_step ⟨[], [3, 2, 1, 0]⟩ (fuel := 5) hs2
    lm22MemMoveUb_phase rfl rfl (.storageLive _ 5 3 lm22NestedDecl _ rfl) rfl rfl
  have ⟨hs4, ha3, hm3⟩ := lm22_trace_step ⟨[], [4, 3, 2, 1, 0]⟩ (fuel := 4) hs3
    lm22MemMoveUb_phase rfl rfl (.storageLive _ 5 4 lm22NestedDecl _ rfl) rfl rfl
  have hwt4 : WellTypedLM2_2Stmt lm22MemMoveUbBody lm22NestedEnv ⟨[], [4, 3, 2, 1, 0]⟩ 5
      (mkStmt22 (.assign ⟨1, []⟩
        (.aggregate (.adt "lm22::InnerPair" 0 .none)
          [.constant (lm22ConstU32 0x11112222), .constant (constU16 0x3344)])))
      (aggPostStaticEnv ⟨[], [4, 3, 2, 1, 0]⟩ 1
        [.constant (lm22ConstU32 0x11112222), .constant (constU16 0x3344)]) 4 :=
    .assignAggregate _ 4 1 _ _ _
      (.mk lm22InnerPairDecl lm22InnerPairFields lm22InnerPairPaths _ _ rfl
        (Or.inr ⟨"lm22::InnerPair", rfl⟩) rfl rfl lm22InnerPair_validStructLayout
        (by decide) rfl rfl (by decide)
        (.cons _ 0 0 1 _ _ trivial
          (.primLeaf (by decide) _ (lm22_constU32_wt 0x11112222 (by decide) rfl)
            rfl lm22_u32_prim rfl rfl rfl rfl rfl rfl)
          (.cons _ 1 1 2 _ [] trivial
            (.primLeaf (by decide) _ (lm22_constU16_wt 0x3344 (by decide) rfl)
              rfl lm22_u16_prim rfl rfl rfl rfl rfl rfl)
            (.nil _ 2))))
  have ⟨hs5, ha4, hm4⟩ := lm22_trace_step ⟨[1], [4, 3, 2, 0]⟩ (fuel := 3) hs4
    lm22MemMoveUb_phase rfl rfl hwt4 rfl rfl
  have hwt5 : WellTypedLM2_2Stmt lm22MemMoveUbBody lm22NestedEnv ⟨[1], [4, 3, 2, 0]⟩ 4
      (mkStmt22 (.assign ⟨2, []⟩
        (.aggregate (.adt "lm22::NestedOuter" 0 .none)
          [.constant (constU8 7), .move ⟨1, []⟩])))
      (aggPostStaticEnv ⟨[1], [4, 3, 2, 0]⟩ 2
        [.constant (constU8 7), .move ⟨1, []⟩]) 3 :=
    .assignAggregate _ 3 2 _ _ _
      (.mk lm22NestedDecl lm22NestedFields lm22NestedPaths _ _ rfl
        (Or.inr ⟨"lm22::NestedOuter", rfl⟩) rfl rfl lm22Nested_validStructLayout
        (by decide) rfl rfl (by decide)
        (.cons _ 0 0 1 _ _ trivial
          (.primLeaf (by decide) _ (lm22_constU8_wt 7 (by decide) rfl)
            rfl lm22_u8_prim rfl rfl rfl rfl rfl rfl)
          (.cons _ 1 1 3 (.move ⟨1, []⟩) [] (by decide : (1 : Nat) ≠ 2)
            (.scalarPairSub (by decide) lm22InnerPairTy lm22InnerPairField0 lm22InnerPairField1
              lm22U32Ty u16Ty [] [] _ _ _ (Miri.ABI.Size.ofBytes 4)
              (.immStructLocal true 1 lm22InnerPairDecl lm22InnerPairFields
                lm22InnerPairPaths rfl lm22InnerPair_isImmediateStructTy)
              lm22InnerPair_isImmediateStructTy
              rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide))
            (.nil _ 2))))
  have ⟨hs6, ha5, hm5⟩ := lm22_trace_step ⟨[2], [1, 4, 3, 0]⟩ (fuel := 2) hs5
    lm22MemMoveUb_phase rfl rfl hwt5 rfl rfl
  have hwt6 : WellTypedLM2_2Stmt lm22MemMoveUbBody lm22NestedEnv ⟨[2], [1, 4, 3, 0]⟩ 3
      (mkStmt22 (.assign ⟨3, []⟩ (.use (.move ⟨2, []⟩))))
      (useStructPostStaticEnv ⟨[2], [1, 4, 3, 0]⟩ 3 (.move ⟨2, []⟩)) 2 :=
    .assignUseMemStruct _ 2 3 true 2 _
      (.mk lm22NestedDecl lm22NestedDecl lm22NestedFields lm22NestedPaths _ _
        (by decide) rfl rfl rfl rfl (Or.inl (by decide)) rfl rfl
        (by decide) (by decide) rfl (by decide))
  have ⟨hs7, ha6, hm6⟩ := lm22_trace_step ⟨[3], [2, 1, 4, 0]⟩ (fuel := 1) hs6
    lm22MemMoveUb_phase rfl rfl hwt6 rfl rfl
  have hwt7 : WellTypedLM2_2Stmt lm22MemMoveUbBody lm22NestedEnv ⟨[3], [2, 1, 4, 0]⟩ 2
      (mkStmt22 (.assign ⟨4, []⟩ (.use (.copy ⟨2, []⟩))))
      (useStructPostStaticEnv ⟨[3], [2, 1, 4, 0]⟩ 4 (.copy ⟨2, []⟩)) 1 :=
    .assignUseMemStruct _ 1 4 false 2 _
      (.mk lm22NestedDecl lm22NestedDecl lm22NestedFields lm22NestedPaths _ _
        (by decide) rfl rfl rfl rfl (Or.inr (by decide)) rfl rfl
        (by decide) (by decide) rfl (by decide))
  have hsim7 := step_stmt_lm2_2_simulation hs7 lm22MemMoveUb_phase rfl rfl hwt7
  have ha7 :
      stepMirFn lm22MemMoveUbBody
        (lm22StepAnnealN lm22MemMoveUbBody 7 (initMachineState lm22MemMoveUbBody [])) =
      MirStepNode.fail .ub := rfl
  rw [ha7] at hsim7
  have ha_tot :
      runAnnealBounded lm22MemMoveUbBody 8 (initMachineState lm22MemMoveUbBody []) =
        runAnnealBounded lm22MemMoveUbBody 1
          (lm22StepAnnealN lm22MemMoveUbBody 7 (initMachineState lm22MemMoveUbBody [])) :=
    ha0.trans (ha1.trans (ha2.trans (ha3.trans (ha4.trans (ha5.trans ha6)))))
  have hm_tot :
      runMiriBoundedLM2_2 lm22MemMoveUbBody 8 lm22MemMoveUbMiriInit =
        runMiriBoundedLM2_2 lm22MemMoveUbBody 1 (lm22StepMiriN lm22MemMoveUbBody 7 lm22MemMoveUbMiriInit) :=
    hm0.trans (hm1.trans (hm2.trans (hm3.trans (hm4.trans (hm5.trans hm6)))))
  rw [ha_tot, hm_tot]
  refine ⟨by unfold runAnnealBounded; rw [ha7]; rfl, ?_⟩
  generalize hm_step :
    Miri.Interpreter.Step.step
      (annealStepHooksLM2_2 lm22MemMoveUbBody.localDecls lm22MemMoveUbBody.layouts) ()
      (lm22StepMiriN lm22MemMoveUbBody 7 lm22MemMoveUbMiriInit) = r at hsim7
  cases hsim7 with
  | ub m_err msg =>
    refine ⟨m_err, msg, ?_⟩
    unfold runMiriBoundedLM2_2
    rw [hm_step]

def lm22AllocId1 : Miri.Memory.AllocId := ⟨1, by decide⟩
def lm22AllocId2 : Miri.Memory.AllocId := ⟨2, by decide⟩

def lm22ReadOnlyAlloc :
    Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree) :=
  ((Miri.Memory.Allocation.fromBytes (Prov := AnnealProv)
      (Array.replicate 12 0) (translateAlignBytes 4) .Not).toOption.get
      (by decide)).withExtra none

def lm22ReadOnlyCopyState : AnnealStepState :=
  { stack := ⟨#[{
      body := translateBody lm22MemMoveUbBody
      bodyIdentity := .ofCanonicalIndex 0
      functionInstance := { kind := .Item 0, args := #[] }
      extra := ()
      returnContinuation := .stop false
      returnPlace :=
        .frameLocal 0 0 none (translateTy u16Ty lm22NestedLayoutTable) (.ofAllocationToken 0)
      localsIdentity := .ofAllocationToken 0
      locals := #[
        { value := .live (.immediate .uninit), layout := none },
        { value := .live (.indirect (stackAllocPlace lm22AllocId1)),
          layout := some (translateTy lm22NestedTy lm22NestedLayoutTable) },
        { value := .live (.indirect (stackAllocPlace lm22AllocId2)),
          layout := some (translateTy lm22NestedTy lm22NestedLayoutTable) }]
      vaList := #[]
      trackCallerArg := none
      location := .mir ⟨0, 0⟩ }]⟩
    machine :=
      { AnnealMachine.empty with
        memory :=
          { AnnealMachine.empty.memory with
            nextAllocId := 3
            live := #[
              (lm22AllocId1, ⟨.stack, lm22ReadOnlyAlloc⟩),
              (lm22AllocId2, ⟨.stack, lm22ReadOnlyAlloc⟩)] }
        addresses :=
          { AnnealMachine.empty.addresses with
            baseAddr := #[
              ⟨lm22AllocId1, annealStackBaseAddr lm22AllocId1⟩,
              ⟨lm22AllocId2, annealStackBaseAddr lm22AllocId2⟩] } } }

theorem lm22Lazy12_prepareCopy :
    (Miri.Memory.InitMask.new (Miri.ABI.Size.ofBytes 12) true).prepareCopy
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 12)) =
    .ok ⟨true, #[12]⟩ := by
  have hiter :
      (Miri.Memory.InitMask.new (Miri.ABI.Size.ofBytes 12) true).rangeAsInitChunks
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 12)) =
      .ok ⟨Miri.Memory.InitMask.new (Miri.ABI.Size.ofBytes 12) true,
        true, Miri.ABI.Size.ZERO, Miri.ABI.Size.ofBytes 12⟩ := rfl
  have hch :
      Miri.Memory.InitMask.collectChunks
        ⟨Miri.Memory.InitMask.new (Miri.ABI.Size.ofBytes 12) true,
          true, Miri.ABI.Size.ZERO, Miri.ABI.Size.ofBytes 12⟩ =
      .ok #[.Init Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 12)] := by
    with_unfolding_all rfl
  unfold Miri.Memory.InitMask.prepareCopy
  rw [hiter]
  dsimp [Bind.bind, Except.bind]
  rw [hch]
  simp
  rfl

theorem lm22EmptyProv12_prepareCopy (bytes : Array UInt8) :
    (Miri.Memory.ProvenanceMap.new (Prov := AnnealProv)).prepareCopy
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 12))
      bytes (Miri.ABI.Size.ofBytes 8) =
    .ok ⟨#[], #[]⟩ := by
  simp [Miri.Memory.ProvenanceMap.prepareCopy]
  rfl

theorem lm22ReadOnlyAlloc_copy_err :
    lm22ReadOnlyAlloc.copy
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO
        (translateTy lm22NestedTy lm22NestedLayoutTable).layout.size)
      Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8) false true lm22ReadOnlyAlloc =
    .error .readOnlyAllocation lm22ReadOnlyAlloc := by
  dsimp [Miri.Memory.Allocation.copy, Miri.Memory.Allocation.copyRepeatedly]
  erw [lm22EmptyProv12_prepareCopy (Array.replicate 12 0), lm22Lazy12_prepareCopy]
  rfl

theorem lm22ReadOnlyCopy_ub :
    annealStructMemCopyOp lm22MemMoveUbBody.localDecls lm22NestedLayoutTable
      ⟨.indirect (stackAllocPlace lm22AllocId1),
        translateTy lm22NestedTy lm22NestedLayoutTable⟩
      ⟨.local 0 2 none (.ofAllocationToken 0),
        translateTy lm22NestedTy lm22NestedLayoutTable⟩
      lm22ReadOnlyCopyState =
    .error (.undefinedBehavior "write to read-only allocation") lm22ReadOnlyCopyState :=
  annealStructMemCopyOp_readOnly_ub
    (u := 1) (destAlloc' := lm22ReadOnlyAlloc)
    rfl (by decide) rfl rfl rfl rfl
    ⟨rfl, 0, by decide, by rw [List.findIdx?_toArray]; rfl, rfl⟩
    rfl rfl rfl (by decide : 1 < 2)
    (by rw [List.findIdx?_toArray]; rfl) rfl rfl lm22ReadOnlyAlloc_copy_err


/-! ## 14. 2-Level `.Memory` Sub-Struct (`SuperOuter`, `sf.length = 3`)

Witnesses both:
1. **`annealAggregateHooksLM2_2` `.Memory` sub-struct dispatch**: Step 0 executes
   `_1 = SuperOuter(7_u8, move _2)` via `annealAggregateHooksLM2_2` ->
   `annealStructMemCopyOp` -> `Miri.Memory.Allocation.copy` at `destOff = 4`,
   copying 12-byte 3-field `.Memory` sub-struct `UnpaddedTriple(10, 20, 30)`
   into `_1`, deinitializing `_2`, keeping inter-field alignment padding bytes
   `1, 2, 3` `.uninit`, and establishing `StateRelLM2_2` (`StructMemPlaceRel`
   with `ValidAggregateFieldPath.cons` across a 3-field `.Memory` sub-struct,
   `sf.length = 3 > 2`)!
2. **2-level nested field write, whole-struct move, and 2-level nested field
   read** through the 3-field `.Memory` sub-struct:
   `_1.1.2 = const 0x778899AA_u32; _3 = move _1; _0 = copy _3.1.2; return`,
   preserving padding bytes `1, 2, 3` `.uninit` in `_3` and returning
   `some 0x778899AA` on both Anneal and `lean-miri`. -/

def lm22SuperTripleTy : Ty :=
  { kind := .adt "lm22::UnpaddedTriple" [], layoutIdx := 1 }

def lm22SuperTripleDecl : LocalDecl :=
  { mutability := .mut, ty := lm22SuperTripleTy, debugName := none }

def lm22SuperOuterTy : Ty :=
  { kind := .adt "lm22::SuperOuter" [], layoutIdx := 0 }

def lm22SuperOuterDecl : LocalDecl :=
  { mutability := .mut, ty := lm22SuperOuterTy, debugName := none }

def lm22SuperTripleTypeLayout : TypeLayout :=
  { size := { bytes := 12 }
    align := { bytes := 4 }
    backendRepr := .memory
    fields := .arbitrary [{ bytes := 0 }, { bytes := 4 }, { bytes := 8 }] [0, 1, 2]
    variants := .single 0
    isUninhabited := false
    fieldLayouts := [2, 2, 2] }

def lm22SuperOuterTypeLayout : TypeLayout :=
  { size := { bytes := 16 }
    align := { bytes := 4 }
    backendRepr := .memory
    fields := .arbitrary [{ bytes := 0 }, { bytes := 4 }] [0, 1]
    variants := .single 0
    isUninhabited := false
    fieldLayouts := [3, 1] }

def lm22SuperLayoutTable : LayoutTable :=
  { pointerBits := 64
    isLittleEndian := true
    entries :=
      [lm22SuperOuterTypeLayout, lm22SuperTripleTypeLayout,
       lm22U32TypeLayout, lm22U8TypeLayout] }

def lm22SuperTripleFields : List StructFieldDesc :=
  [ { offset := Miri.ABI.Size.ZERO
      ty := lm22U32Ty
      fieldLayout := (translateTy lm22U32Ty lm22SuperLayoutTable).layout }
  , { offset := Miri.ABI.Size.ofBytes 4
      ty := lm22U32Ty
      fieldLayout := (translateTy lm22U32Ty lm22SuperLayoutTable).layout }
  , { offset := Miri.ABI.Size.ofBytes 8
      ty := lm22U32Ty
      fieldLayout := (translateTy lm22U32Ty lm22SuperLayoutTable).layout } ]

def lm22SuperOuterFields : List StructFieldDesc :=
  [ { offset := Miri.ABI.Size.ZERO
      ty := u8Ty
      fieldLayout := (translateTy u8Ty lm22SuperLayoutTable).layout }
  , { offset := Miri.ABI.Size.ofBytes 4
      ty := lm22U32Ty
      fieldLayout := (translateTy lm22U32Ty lm22SuperLayoutTable).layout }
  , { offset := Miri.ABI.Size.ofBytes 8
      ty := lm22U32Ty
      fieldLayout := (translateTy lm22U32Ty lm22SuperLayoutTable).layout }
  , { offset := Miri.ABI.Size.ofBytes 12
      ty := lm22U32Ty
      fieldLayout := (translateTy lm22U32Ty lm22SuperLayoutTable).layout } ]

def lm22SuperOuterPaths : List (List ProjectionElem) :=
  [ [.field 0 u8Ty]
  , [.field 1 lm22SuperTripleTy, .field 0 lm22U32Ty]
  , [.field 1 lm22SuperTripleTy, .field 1 lm22U32Ty]
  , [.field 1 lm22SuperTripleTy, .field 2 lm22U32Ty] ]

def lm22SuperEnv : StructTypeEnv := fun ty =>
  match ty.kind with
  | .adt "lm22::UnpaddedTriple" [] => some (lm22SuperTripleFields, lm22UnpaddedPaths)
  | .adt "lm22::SuperOuter" [] => some (lm22SuperOuterFields, lm22SuperOuterPaths)
  | _ => none

theorem lm22SuperOuter_validStructLayout :
    ValidStructLayout (translateTy lm22SuperOuterTy lm22SuperLayoutTable).layout
      lm22SuperOuterFields := by
  refine
    { fields_in_bounds := fun i hi => by
        match i with
        | 0 | 1 | 2 | 3 => decide +revert
        | _ + 4 => simp [lm22SuperOuterFields] at hi; omega
      fields_disjoint := fun i j hi hj hne => by
        match i, j with
        | 0, 0 | 1, 1 | 2, 2 | 3, 3 => exact False.elim (hne rfl)
        | 0, 1 | 0, 2 | 0, 3 | 1, 2 | 1, 3 | 2, 3 => left; decide +revert
        | 1, 0 | 2, 0 | 3, 0 | 2, 1 | 3, 1 | 3, 2 => right; decide +revert
        | _ + 4, _ => simp [lm22SuperOuterFields] at hi; omega
        | _, _ + 4 => simp [lm22SuperOuterFields] at hj; omega
      fields_aligned := fun i hi => by
        match i with
        | 0 | 1 | 2 | 3 => decide +revert
        | _ + 4 => simp [lm22SuperOuterFields] at hi; omega
      fields_shape_valid := Or.inr ⟨#[Miri.ABI.Size.ZERO, Miri.ABI.Size.ofBytes 4], #[0, 1],
        rfl, by decide,
        (by
          intro off hoff
          change off ∈ [Miri.ABI.Size.ZERO, Miri.ABI.Size.ofBytes 4] at hoff
          cases hoff with
          | head => exact .head _
          | tail _ h2 =>
            cases h2 with
            | head => exact .tail _ (.head _)
            | tail _ hnil => cases hnil),
        (by
          intro f hf
          cases hf with
          | head => exact ⟨Miri.ABI.Size.ZERO, .head _, by decide⟩
          | tail _ hf2 =>
            cases hf2 with
            | head => exact ⟨Miri.ABI.Size.ofBytes 4, .tail _ (.head _), by decide⟩
            | tail _ hf3 =>
              cases hf3 with
              | head => exact ⟨Miri.ABI.Size.ofBytes 4, .tail _ (.head _), by decide⟩
              | tail _ hf4 =>
                cases hf4 with
                | head => exact ⟨Miri.ABI.Size.ofBytes 4, .tail _ (.head _), by decide⟩
                | tail _ hnil => cases hnil)⟩ }

theorem lm22SuperOuter_padding_bytes :
    isStructPaddingByte lm22SuperOuterFields (Miri.ABI.Size.ofBytes 16) 1 ∧
    isStructPaddingByte lm22SuperOuterFields (Miri.ABI.Size.ofBytes 16) 2 ∧
    isStructPaddingByte lm22SuperOuterFields (Miri.ABI.Size.ofBytes 16) 3 := by
  have hp : ∀ b : Nat, b < 16 → (b = 1 ∨ b = 2 ∨ b = 3) →
      isStructPaddingByte lm22SuperOuterFields (Miri.ABI.Size.ofBytes 16) b := by
    intro b hb hcases
    refine ⟨by change b < 16; exact hb, fun f hf => ?_⟩
    rcases hcases with rfl | rfl | rfl <;>
      (cases hf with
       | head => right; decide
       | tail _ hf2 =>
         cases hf2 with
         | head => left; decide
         | tail _ hf3 =>
           cases hf3 with
           | head => left; decide
           | tail _ hf4 =>
             cases hf4 with
             | head => left; decide
             | tail _ hnil => cases hnil)
  exact ⟨hp 1 (by decide) (Or.inl rfl),
    hp 2 (by decide) (Or.inr (Or.inl rfl)),
    hp 3 (by decide) (Or.inr (Or.inr rfl))⟩

theorem lm22SuperOuter_projChain_triple2 :
    ValidFieldProjChain lm22SuperLayoutTable
      (translateTy lm22SuperOuterTy lm22SuperLayoutTable)
      [.field 1 lm22SuperTripleTy, .field 2 lm22U32Ty] lm22U32Ty
      (Miri.ABI.Size.ofBytes 12) := by
  have h : Miri.ABI.Size.ofBytes ((Miri.ABI.Size.ofBytes 4).bytes + (Miri.ABI.Size.ofBytes 8).bytes) =
      Miri.ABI.Size.ofBytes 12 := rfl
  rw [← h]
  exact .cons (translateTy lm22SuperOuterTy lm22SuperLayoutTable) 1 lm22SuperTripleTy
    [.field 2 lm22U32Ty] lm22U32Ty (Miri.ABI.Size.ofBytes 4) (Miri.ABI.Size.ofBytes 8)
    (Or.inr (Or.inr ⟨"lm22::UnpaddedTriple", [], rfl⟩)) rfl rfl (by decide)
    (.single (translateTy lm22SuperTripleTy lm22SuperLayoutTable) 2 lm22U32Ty
      (Miri.ABI.Size.ofBytes 8) (Or.inl lm22_u32_prim) rfl rfl (by decide))

def lm22SuperOuterBody : CapturedMir where
  defPath := "lm_2_2_witness::super_outer_3field_memory_substruct"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls :=
    [lm22U32Decl, lm22SuperOuterDecl, lm22SuperTripleDecl, lm22SuperOuterDecl]
  basicBlocks := [
    { statements := [
        mkStmt22 (.assign ⟨1, []⟩
          (.aggregate (.adt "lm22::SuperOuter" 0 .none)
            [.constant (constU8 7), .move ⟨2, []⟩])),
        mkStmt22 (.storageLive 3),
        mkStmt22 (.assign ⟨1, [.field 1 lm22SuperTripleTy, .field 2 lm22U32Ty]⟩
          (.use (.constant (lm22ConstU32 0x778899AA)))),
        mkStmt22 (.assign ⟨3, []⟩ (.use (.move ⟨1, []⟩))),
        mkStmt22 (.assign ⟨0, []⟩
          (.use (.copy ⟨3, [.field 1 lm22SuperTripleTy, .field 2 lm22U32Ty]⟩))),
        mkStmt22 (.storageDead 3),
        mkStmt22 (.storageDead 2),
        mkStmt22 (.storageDead 1)],
      terminator := mkTerm22 .return_,
      isCleanup := false }]
  fnAbi := lm22FnAbiU32
  layouts := lm22SuperLayoutTable
  allocations := []

def lm22SuperOuterAnnealInit : MachineState :=
  { (initMachineState lm22SuperOuterBody []) with
    frame :=
      { (initMachineState lm22SuperOuterBody []).frame with
        locals :=
          [ .uninit
          , .uninit
          , .init (.aggregate 0 [.scalar ⟨10, 4⟩, .scalar ⟨20, 4⟩, .scalar ⟨30, 4⟩])
          , .dead ] } }

def lm22SuperTripleInitAlloc :
    Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree) :=
  ((Miri.Memory.Allocation.fromBytes (Prov := AnnealProv)
      #[10, 0, 0, 0, 20, 0, 0, 0, 30, 0, 0, 0]
      (translateAlignBytes 4) .Mut).toOption.get (by decide)).withExtra none

def lm22SuperOuterUninitAlloc :
    Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree) :=
  match Miri.Memory.Allocation.tryNew (Prov := AnnealProv) (Miri.ABI.Size.ofBytes 16)
      (translateAlignBytes 4) .Uninit annealZeroedStorage with
  | .ok a => a.withExtra none
  | .error _ => lm22SuperTripleInitAlloc

private theorem lm22SuperOuterUninitAlloc_props :
    lm22SuperOuterUninitAlloc.byteSize = Miri.ABI.Size.ofBytes 16 ∧
    lm22SuperOuterUninitAlloc.len = 16 ∧
    lm22SuperOuterUninitAlloc.mutability = .Mut ∧
    lm22SuperOuterUninitAlloc.provenanceMap = Miri.Memory.ProvenanceMap.new ∧
    lm22SuperOuterUninitAlloc.initializationMask =
      Miri.Memory.InitMask.new (Miri.ABI.Size.ofBytes 16) false := by
  obtain ⟨rawAlloc, htry, hbs, hlen, hmut, hprov, hmask⟩ :=
    tryNew_uninit_of_pow2_le_29 (Miri.ABI.Size.ofBytes 16) (translateAlignBytes 4) (by decide)
  unfold lm22SuperOuterUninitAlloc
  rw [htry]
  exact ⟨hbs, hlen, hmut, hprov, hmask⟩

def lm22SuperOuterMiriInit : AnnealStepState :=
  { stack := ⟨#[{
      body := translateBody lm22SuperOuterBody
      bodyIdentity := .ofCanonicalIndex 0
      functionInstance := { kind := .Item 0, args := #[] }
      extra := ()
      returnContinuation := .stop false
      returnPlace :=
        .frameLocal 0 0 none (translateTy lm22U32Ty lm22SuperLayoutTable) (.ofAllocationToken 0)
      localsIdentity := .ofAllocationToken 0
      locals := #[
        { value := .live (.immediate .uninit), layout := none },
        { value := .live (.indirect (stackAllocPlace lm22AllocId1)),
          layout := some (translateTy lm22SuperOuterTy lm22SuperLayoutTable) },
        { value := .live (.indirect (stackAllocPlace lm22AllocId2)),
          layout := some (translateTy lm22SuperTripleTy lm22SuperLayoutTable) },
        { value := .dead, layout := none }]
      vaList := #[]
      trackCallerArg := none
      location := .mir ⟨0, 0⟩ }]⟩
    machine :=
      { AnnealMachine.empty with
        memory :=
          { AnnealMachine.empty.memory with
            nextAllocId := 3
            live := #[
              (lm22AllocId1, ⟨.stack, lm22SuperOuterUninitAlloc⟩),
              (lm22AllocId2, ⟨.stack, lm22SuperTripleInitAlloc⟩)] }
        addresses :=
          { AnnealMachine.empty.addresses with
            baseAddr := #[
              ⟨lm22AllocId1, annealStackBaseAddr lm22AllocId1⟩,
              ⟨lm22AllocId2, annealStackBaseAddr lm22AllocId2⟩] } } }

theorem lm22SuperOuter_phase : ∀ p, lm22SuperOuterBody.phase ≠ .other p := by
  intro p h; cases h

def lm22SuperOuterMiriStateAt
    (loc : Miri.Interpreter.FrameLocation)
    (local2 : Miri.Interpreter.LocalValue AnnealProv)
    (a1 : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)) :
    AnnealStepState :=
  { stack := ⟨#[{
      body := translateBody lm22SuperOuterBody
      bodyIdentity := .ofCanonicalIndex 0
      functionInstance := { kind := .Item 0, args := #[] }
      extra := ()
      returnContinuation := .stop false
      returnPlace :=
        .frameLocal 0 0 none (translateTy lm22U32Ty lm22SuperLayoutTable) (.ofAllocationToken 0)
      localsIdentity := .ofAllocationToken 0
      locals := #[
        { value := .live (.immediate .uninit), layout := none },
        { value := .live (.indirect (stackAllocPlace lm22AllocId1)),
          layout := some (translateTy lm22SuperOuterTy lm22SuperLayoutTable) },
        { value := local2,
          layout := some (translateTy lm22SuperTripleTy lm22SuperLayoutTable) },
        { value := .dead, layout := none }]
      vaList := #[]
      trackCallerArg := none
      location := loc }]⟩
    machine :=
      { AnnealMachine.empty with
        memory :=
          { AnnealMachine.empty.memory with
            nextAllocId := 3
            live := #[
              (lm22AllocId1, ⟨.stack, a1⟩),
              (lm22AllocId2, ⟨.stack, lm22SuperTripleInitAlloc⟩)] }
        addresses :=
          { AnnealMachine.empty.addresses with
            baseAddr := #[
              ⟨lm22AllocId1, annealStackBaseAddr lm22AllocId1⟩,
              ⟨lm22AllocId2, annealStackBaseAddr lm22AllocId2⟩] } } }

private def lm22SuperOuterAfter0 :
    Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree) :=
  match Miri.Memory.Allocation.writeScalar annealTargetDataLayout
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.Memory.ScalarInt.ofUInt8 7).size)
      (Miri.Memory.Scalar.fromScalarInt (Miri.Memory.ScalarInt.ofUInt8 7))
      lm22SuperOuterUninitAlloc with
  | .ok () a => a
  | .error _ a => a

private def lm22SuperOuterAfter1 :
    Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree) :=
  match Miri.Memory.Allocation.copy lm22SuperTripleInitAlloc
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 12))
      (Miri.ABI.Size.ofBytes 4) (Miri.ABI.Size.ofBytes 8) false true
      lm22SuperOuterAfter0 with
  | .ok () a => a
  | .error _ a => a

private theorem lm22SuperOuterAfter0_copy :
    Miri.Memory.Allocation.copy lm22SuperTripleInitAlloc
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 12))
      (Miri.ABI.Size.ofBytes 4) (Miri.ABI.Size.ofBytes 8) false true
      lm22SuperOuterAfter0 = .ok () lm22SuperOuterAfter1 := by
  have hok :
      (match Miri.Memory.Allocation.copy lm22SuperTripleInitAlloc
          (Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 12))
          (Miri.ABI.Size.ofBytes 4) (Miri.ABI.Size.ofBytes 8) false true
          lm22SuperOuterAfter0 with
        | .ok () _ => true
        | .error _ _ => false) = true := by
    dsimp [Miri.Memory.Allocation.copy, Miri.Memory.Allocation.copyRepeatedly]
    erw [lm22EmptyProv12_prepareCopy #[10, 0, 0, 0, 20, 0, 0, 0, 30, 0, 0, 0],
      lm22Lazy12_prepareCopy]
    with_unfolding_all rfl
  unfold lm22SuperOuterAfter1
  cases hc : Miri.Memory.Allocation.copy lm22SuperTripleInitAlloc
    (Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 12))
    (Miri.ABI.Size.ofBytes 4) (Miri.ABI.Size.ofBytes 8) false true
    lm22SuperOuterAfter0 with
  | ok u a => cases u; rfl
  | error _ _ => rw [hc] at hok; cases hok

private theorem lm22SuperOuter_step0_spec :
    ∃ step1Alloc words1,
      Miri.Interpreter.Step.step
        (annealStepHooksLM2_2 lm22SuperOuterBody.localDecls lm22SuperOuterBody.layouts) ()
        lm22SuperOuterMiriInit =
        (lm22SuperOuterMiriStateAt (.mir ⟨0, 1⟩) (.live (.immediate .uninit)) step1Alloc,
          .ok true) ∧
      step1Alloc.byteSize = Miri.ABI.Size.ofBytes 16 ∧
      step1Alloc.len = 16 ∧
      step1Alloc.mutability = .Mut ∧
      step1Alloc.provenanceMap = Miri.Memory.ProvenanceMap.new ∧
      InitMaskWordRel step1Alloc.initializationMask (Miri.ABI.Size.ofBytes 16) words1 ∧
      (∀ b < 16, maskBlocksGetBit words1 b = decide (b < 1 ∨ 4 ≤ b)) ∧
      (lm22AllocRaw step1Alloc).extract 0 1 = lm22LeBytes 7 1 ∧
      (lm22AllocRaw step1Alloc).extract 4 16 =
        #[10, 0, 0, 0, 20, 0, 0, 0, 30, 0, 0, 0] := by
  obtain ⟨hbs_u, hlen_u, hmut_u, hprov_u, hmask_u⟩ := lm22SuperOuterUninitAlloc_props
  have hmask_rel_u :
      InitMaskWordRel lm22SuperOuterUninitAlloc.initializationMask
        lm22SuperOuterUninitAlloc.byteSize (initWordsFalse (Miri.ABI.Size.ofBytes 16)) := by
    rw [hmask_u, hbs_u]
    exact initMaskWordRel_new_false
  have hsr7 : ScalarRel ⟨7, 1⟩ (Miri.Memory.ScalarInt.ofUInt8 7) :=
    ⟨Or.inl rfl, by rw [scalarModulus_eq_two_pow]; decide, rfl, rfl⟩
  obtain ⟨after0, _, hw0, _, _, _, _, _, _, _, _, _⟩ :=
    alloc_writeScalar_at_offset_mask hsr7 (A := lm22SuperOuterUninitAlloc)
      (start := Miri.ABI.Size.ZERO)
      (by rw [hlen_u, hbs_u]; rfl) hmut_u hprov_u hmask_rel_u
      (by rw [hbs_u]; decide)
  have hw0_eq : after0 = lm22SuperOuterAfter0 := by
    unfold lm22SuperOuterAfter0; rw [hw0]
  subst hw0_eq
  obtain ⟨mask0, words0, hset0, hrel0, hbits0⟩ :=
    initMaskWordRel_setRange_true
      (initMaskWordRel_new_false (len := Miri.ABI.Size.ofBytes 16))
      (start := Miri.ABI.Size.ZERO) (sz := Miri.ABI.Size.ofBytes 1)
      (by decide) (by decide)
  obtain ⟨mask1, words1a, hset1, hrel1, hbits1⟩ :=
    initMaskWordRel_setRange_true hrel0
      (start := Miri.ABI.Size.ofBytes 4) (sz := Miri.ABI.Size.ofBytes 12)
      (by decide) (by decide)
  obtain ⟨mask2, words2, hset2, hrel2, hbits2⟩ :=
    initMaskWordRel_setRange_true hrel1
      (start := Miri.ABI.Size.ofBytes 4) (sz := Miri.ABI.Size.ofBytes 12)
      (by decide) (by decide)
  have hmask_chain :
      ((Miri.Memory.InitMask.new (Miri.ABI.Size.ofBytes 16) false).setRange
          (Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 1)) true >>= fun m0 =>
        m0.setRange
          (Miri.Memory.allocRange (Miri.ABI.Size.ofBytes 4) (Miri.ABI.Size.ofBytes 12)) true >>= fun m1 =>
        m1.setRange
          (Miri.Memory.allocRange (Miri.ABI.Size.ofBytes 4) (Miri.ABI.Size.ofBytes 12)) true) =
      .ok lm22SuperOuterAfter1.initializationMask := by
    with_unfolding_all rfl
  rw [hset0] at hmask_chain
  dsimp only [bind, Except.bind] at hmask_chain
  rw [hset1] at hmask_chain
  dsimp only [bind, Except.bind] at hmask_chain
  rw [hset2] at hmask_chain
  have hmask1 : InitMaskWordRel lm22SuperOuterAfter1.initializationMask
      (Miri.ABI.Size.ofBytes 16) words2 := by
    rw [← Except.ok.inj hmask_chain]
    exact hrel2
  have hfalse : ∀ k < 16,
      maskBlocksGetBit (initWordsFalse (Miri.ABI.Size.ofBytes 16)) k = false := by decide
  have hbits_all : ∀ b < 16, maskBlocksGetBit words2 b = decide (b < 1 ∨ 4 ≤ b) := by
    intro b hb
    rw [hbits2 b hb, hbits1 b hb, hbits0 b hb, hfalse b hb]
    by_cases h0 : b < 1 <;> by_cases h4 : 4 ≤ b <;>
      simp [h0, h4, Miri.ABI.Size.ZERO, Miri.ABI.Size.ofBytes] <;> omega
  have hcopy1 := lm22SuperOuterAfter0_copy
  let step1Alloc := lm22SuperOuterAfter1
  refine ⟨step1Alloc, words2, ?_,
    by with_unfolding_all rfl, by with_unfolding_all rfl,
    by with_unfolding_all rfl, by with_unfolding_all rfl,
    hmask1, hbits_all, by with_unfolding_all rfl, by with_unfolding_all rfl⟩
  let after0 := lm22SuperOuterAfter0
  let h := annealAggregateHooksLM2_2 lm22SuperOuterBody.localDecls lm22SuperOuterBody.layouts
  let dst : Miri.Interpreter.RuntimePlace AnnealProv :=
    ⟨.local 0 1 none (.ofAllocationToken 0),
      translateTy lm22SuperOuterTy lm22SuperOuterBody.layouts⟩
  let f0 : Miri.Interpreter.RuntimePlace AnnealProv :=
    ⟨.local 0 1 (some Miri.ABI.Size.ZERO) (.ofAllocationToken 0),
      layoutOfEncodedTyId 103 lm22SuperOuterBody.layouts⟩
  let v0_lay := translateTy u8Ty lm22SuperOuterBody.layouts
  let f1 : Miri.Interpreter.RuntimePlace AnnealProv :=
    ⟨.local 0 1 (some (Miri.ABI.Size.ofBytes 4)) (.ofAllocationToken 0),
      translateTy lm22SuperTripleTy lm22SuperOuterBody.layouts⟩
  let m_after0 := lm22SuperOuterMiriStateAt (.mir ⟨0, 0⟩)
    (.live (.indirect (stackAllocPlace lm22AllocId2))) after0
  let m_moved2 := lm22SuperOuterMiriStateAt (.mir ⟨0, 0⟩)
    (.live (.immediate .uninit)) after0
  let m_done := lm22SuperOuterMiriStateAt (.mir ⟨0, 0⟩)
    (.live (.immediate .uninit)) step1Alloc
  have heval :
      Miri.Interpreter.Step.evalStatement
        (annealStepHooksLM2_2 lm22SuperOuterBody.localDecls lm22SuperOuterBody.layouts) ()
        (translateStmt (mkStmt22 (.assign ⟨1, []⟩
          (.aggregate (.adt "lm22::SuperOuter" 0 .none)
            [.constant (constU8 7), .move ⟨2, []⟩]))))
        lm22SuperOuterMiriInit =
      (m_done, .ok ()) := by
    dsimp only [Miri.Interpreter.Step.evalStatement, annealStepHooksLM2_2,
      translateStmt, translateStmtKind, mkStmt22, translateRvalue, Miri.Interpreter.runRvalue,
      Miri.Interpreter.evalRvalueIntoPlace, annealRvalueHooksLM2_2]
    have hp_dst :
        annealEvalPlace lm22SuperOuterBody.localDecls lm22SuperOuterBody.layouts
          (translatePlace ⟨1, []⟩) lm22SuperOuterMiriInit =
        .ok dst lm22SuperOuterMiriInit := rfl
    have hwa := congrFun (writeAggregate_list_eq h (Or.inr rfl)
      [translateOperand (.constant (constU8 7)), translateOperand (.move ⟨2, []⟩)]
      dst rfl rfl rfl rfl) lm22SuperOuterMiriInit
    rw [EStateM.bind_eq_ok hp_dst]
    erw [hwa]
    dsimp only [writeAggregateFieldsAux]
    have hp0 : h.projectField () dst 0 lm22SuperOuterMiriInit =
        .ok f0 lm22SuperOuterMiriInit := rfl
    rw [EStateM.bind_eq_ok hp0]
    have hv0 : h.evalOperandAt () (.aggregate 0) (translateOperand (.constant (constU8 7)))
        (some (h.placeLayout f0)) lm22SuperOuterMiriInit =
        .ok ⟨.immediate (.scalar (.fromScalarInt (.ofUInt8 7))), v0_lay⟩
          lm22SuperOuterMiriInit := rfl
    rw [EStateM.bind_eq_ok hv0]
    have hc0 : h.copyOpNoValidate ()
        ⟨.immediate (.scalar (.fromScalarInt (.ofUInt8 7))), v0_lay⟩ f0 false
        lm22SuperOuterMiriInit = .ok () m_after0 := by
      have hfidx1 : lm22SuperOuterMiriInit.machine.memory.live.findIdx?
          (fun (k, _) => k == lm22AllocId1) = some 0 := by
        dsimp [lm22SuperOuterMiriInit, lm22SuperOuterMiriStateAt]
        rw [List.findIdx?_toArray]; rfl
      have hw_proj := annealWriteProjectedLocalImmediate_indirect_scalar_ok
        (localDecls := .nil) (layouts := emptyLayoutTable)
        (s := .fromScalarInt (.ofUInt8 7)) (m := lm22SuperOuterMiriInit)
        (localId := 1) (relOff := Miri.ABI.Size.ZERO) (iden := .ofAllocationToken 0)
        (fieldLay := layoutOfEncodedTyId 103 lm22SuperOuterBody.layouts)
        (mp := stackAllocPlace lm22AllocId1) (allocId := lm22AllocId1)
        (baseAddr := annealStackBaseAddr lm22AllocId1)
        (localAlloc := ⟨.stack, lm22SuperOuterUninitAlloc⟩)
        (alloc' := after0) (u := 0)
        rfl rfl (by decide) rfl rfl rfl rfl (by decide) (by decide) hfidx1 rfl hw0
      change annealWriteProjectedLocalImmediate (.scalar (.fromScalarInt (.ofUInt8 7)))
        f0 .nil emptyLayoutTable lm22SuperOuterMiriInit = .ok () m_after0
      exact hw_proj
    rw [EStateM.bind_eq_ok hc0]
    have hp1 : h.projectField () dst 1 m_after0 = .ok f1 m_after0 := rfl
    rw [EStateM.bind_eq_ok hp1]
    have hv1 : h.evalOperandAt () (.aggregate 1) (translateOperand (.move ⟨2, []⟩))
        (some (h.placeLayout f1)) m_after0 =
        .ok ⟨.indirect (stackAllocPlace lm22AllocId2), f1.layout⟩ m_moved2 := rfl
    rw [EStateM.bind_eq_ok hv1]
    have hc1 : h.copyOpNoValidate ()
        ⟨.indirect (stackAllocPlace lm22AllocId2), f1.layout⟩ f1 false m_moved2 =
        .ok () m_done := by
      have hfa1 := forceAllocation_indirect_some_ok
        (ld := lm22SuperOuterBody.localDecls) (ly := lm22SuperOuterBody.layouts)
        (m := m_moved2) (localId := 1) (relOff := Miri.ABI.Size.ofBytes 4)
        (iden := .ofAllocationToken 0) (lay := f1.layout)
        (mp := stackAllocPlace lm22AllocId1)
        rfl (by decide) rfl (by decide)
      have hfind2 :
          m_moved2.machine.memory.live.find? (fun (k, _) => k == lm22AllocId2) =
            some (lm22AllocId2, ⟨.stack, lm22SuperTripleInitAlloc⟩) := rfl
      have hbase2 :
          m_moved2.machine.lookupBaseAddr lm22AllocId2 =
            some (annealStackBaseAddr lm22AllocId2) := rfl
      have hbase1 :
          m_moved2.machine.lookupBaseAddr lm22AllocId1 =
            some (annealStackBaseAddr lm22AllocId1) := rfl
      have hfidx1 :
          m_moved2.machine.memory.live.findIdx? (fun (k, _) => k == lm22AllocId1) =
            some 0 := by
        dsimp [m_moved2, lm22SuperOuterMiriStateAt]
        rw [List.findIdx?_toArray]; rfl
      have hget1 :
          m_moved2.machine.memory.live[0]? = some (lm22AllocId1, ⟨.stack, after0⟩) := rfl
      have hwhole_false' (sOff dOff sz : Miri.ABI.Size) (same : Bool)
          (hd : dOff = Miri.ABI.Size.ofBytes 4) :
          isWholeStructAllocationCopy lm22SuperTripleInitAlloc after0 sOff dOff sz same = false := by
        subst hd
        simp [isWholeStructAllocationCopy, Miri.ABI.Size.ofBytes]
      change annealStructMemCopyOp lm22SuperOuterBody.localDecls lm22SuperOuterBody.layouts
        ⟨.indirect (stackAllocPlace lm22AllocId2), f1.layout⟩ f1 m_moved2 = .ok () m_done
      dsimp only [f1] at hfa1 ⊢
      unfold annealStructMemCopyOp
      dsimp only [bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get]
      rw [hfa1]
      dsimp only [stackAllocPlace, Option.bind, Miri.Memory.Provenance.getAllocId]
      rw [hbase2, hfind2, hbase1, hfidx1]
      dsimp only
      rw [hget1]
      dsimp only
      erw [hwhole_false' _ _ _ _ rfl]
      simp only [Bool.false_eq_true, ↓reduceIte]
      erw [hcopy1]
      rfl
    rw [EStateM.bind_eq_ok hc1]
    rfl
  exact miri_step_at_statement_ok
    (annealStepHooksLM2_2 lm22SuperOuterBody.localDecls lm22SuperOuterBody.layouts)
    rfl rfl rfl rfl rfl heval rfl rfl

/-- Kernel-checked `annealAggregateHooksLM2_2` execution of
`_1 = SuperOuter(7_u8, move _2)`: `annealStructMemCopyOp` copies the 12-byte
3-field `.Memory` sub-struct `_2` into `[4, 16)`, writes `7_u8` at `[0, 1)`,
deinitializes `_2`, and preserves inter-field alignment padding bytes `1, 2, 3`
as `.uninit` (`InitMask.get = .ok false`). -/
theorem lm22SuperOuter_agg_hooks_ok :
    let m1 := lm22StepMiriN lm22SuperOuterBody 1 lm22SuperOuterMiriInit
    (Miri.Interpreter.Step.step
      (annealStepHooksLM2_2 lm22SuperOuterBody.localDecls lm22SuperOuterBody.layouts) ()
      lm22SuperOuterMiriInit).2 = .ok true ∧
    (∃ la1,
      m1.machine.memory.live[0]? = some (lm22AllocId1, la1) ∧
      la1.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 0) = .ok true ∧
      la1.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 1) = .ok false ∧
      la1.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 2) = .ok false ∧
      la1.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 3) = .ok false ∧
      la1.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 4) = .ok true) := by
  obtain ⟨step1Alloc, words1, hstep, hbs1, _, _, _, hmask1, hbits1, _, _⟩ :=
    lm22SuperOuter_step0_spec
  have hm1 : lm22StepMiriN lm22SuperOuterBody 1 lm22SuperOuterMiriInit =
      lm22SuperOuterMiriStateAt (.mir ⟨0, 1⟩) (.live (.immediate .uninit)) step1Alloc :=
    congrArg Prod.fst hstep
  dsimp only
  rw [hstep, hm1]
  have hget : ∀ p : Nat, (hp : p < 16) →
      step1Alloc.initializationMask.get (Miri.ABI.Size.ofBytes (UInt64.ofNat p)) =
        .ok (decide (p < 1 ∨ 4 ≤ p)) := by
    intro p hp
    rw [initMaskWordRel_get hmask1 (show p < (Miri.ABI.Size.ofBytes 16).bytes.toNat from hp),
      hbits1 p hp]
  exact ⟨rfl, ⟨⟨.stack, step1Alloc⟩, rfl,
    hget 0 (by decide), hget 1 (by decide), hget 2 (by decide),
    hget 3 (by decide), hget 4 (by decide)⟩⟩

private theorem lm22SuperOuter_hwm
    (a1 : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)) :
    AllocIdWatermark 2
      (lm22SuperOuterMiriStateAt (.mir ⟨0, 1⟩) (.live (.immediate .uninit)) a1).machine.memory := by
  refine ⟨by change 1 ≤ 3; decide, by change 3 + 2 < 2 ^ 32; decide, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · intro q hq
    have hemp := (AllocIdWatermark.empty 1 (by decide)).issued_lt q hq
    change q.value.toNat < 1 at hemp
    change q.value.toNat < 3
    omega
  · intro e he
    cases he with
    | head => change (1 : Nat) < 3; decide
    | tail _ h2 =>
      cases h2 with
      | head => change (2 : Nat) < 3; decide
      | tail _ hnil => cases hnil
  · intro _ hd; cases hd
  · intro q hq
    have hemp := (AllocIdWatermark.empty 1 (by decide)).global_lt q hq
    change q.value.toNat < 1 at hemp
    change q.value.toNat < 3
    omega

private theorem lm22SuperOuter_fields_rel1
    {step1Alloc : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    {words1 : Array UInt64}
    (hbs1 : step1Alloc.byteSize = Miri.ABI.Size.ofBytes 16)
    (hlen1 : step1Alloc.len = 16)
    (hmask1 : InitMaskWordRel step1Alloc.initializationMask (Miri.ABI.Size.ofBytes 16) words1)
    (hbits1 : ∀ b < 16, maskBlocksGetBit words1 b = decide (b < 1 ∨ 4 ≤ b))
    (hex1_0 : (lm22AllocRaw step1Alloc).extract 0 1 = lm22LeBytes 7 1)
    (hex1_4 : (lm22AllocRaw step1Alloc).extract 4 16 =
      #[10, 0, 0, 0, 20, 0, 0, 0, 30, 0, 0, 0])
    (i : Nat) (hi : i < lm22SuperOuterFields.length) :
    let f := lm22SuperOuterFields[i]'hi
    let path := lm22SuperOuterPaths[i]'(by exact hi)
    path ≠ [] ∧
    f.fieldLayout = (translateTy f.ty lm22SuperLayoutTable).layout ∧
    IsPrimScalarTy f.ty ∧
    ValidAggregateFieldPath lm22SuperLayoutTable
      (.aggregate 0 [.scalar ⟨7, 1⟩,
        .aggregate 0 [.scalar ⟨10, 4⟩, .scalar ⟨20, 4⟩, .scalar ⟨30, 4⟩]]) path ∧
    ∃ sc msc,
      readProjectedValue []
        (.aggregate 0 [.scalar ⟨7, 1⟩,
          .aggregate 0 [.scalar ⟨10, 4⟩, .scalar ⟨20, 4⟩, .scalar ⟨30, 4⟩]]) path = .ok (.scalar sc) ∧
      ScalarRel sc msc ∧
      f.fieldLayout.size = translateSizeBytes sc.sizeBytes ∧
      (f.ty.kind = .bool → sc.sizeBytes = 1 ∧ (sc.bits = 0 ∨ sc.bits = 1)) ∧
      (f.ty.kind = .char → sc.sizeBytes = 4 ∧ isValidCharCode sc.bits = true) ∧
      step1Alloc.initializationMask.isRangeInitialized
        (Miri.Memory.allocRange f.offset f.fieldLayout.size) = .ok (.ok ()) ∧
      step1Alloc.readScalar annealTargetDataLayout
        (Miri.Memory.allocRange f.offset f.fieldLayout.size) false =
        .ok (.fromScalarInt msc) := by
  have htriple_len :
      ∀ sf : List Value,
        Value.aggregate 0 [.scalar ⟨10, 4⟩, .scalar ⟨20, 4⟩, .scalar ⟨30, 4⟩] =
          .aggregate 0 sf →
        (∀ a b bOff,
          (translateTy lm22SuperTripleTy lm22SuperLayoutTable).layout.backendRepr =
            .ScalarPair (a := a) (b := b) (bOffset := bOff) → sf.length ≤ 2) ∧
        (∀ a,
          (translateTy lm22SuperTripleTy lm22SuperLayoutTable).layout.backendRepr =
            .Scalar a → sf.length = 1) := by
    intro _ _
    exact ⟨(fun _ _ _ h => nomatch h), (fun _ h => nomatch h)⟩
  have hlenA : (lm22AllocRaw step1Alloc).size = step1Alloc.byteSize.bytes.toNat := by
    change step1Alloc.len = step1Alloc.byteSize.bytes.toNat
    rw [hlen1, hbs1]; rfl
  match i with
  | 0 =>
    simp only [lm22SuperOuterFields, lm22SuperOuterPaths, List.getElem_cons_zero]
    have hsr : ScalarRel ⟨7, 1⟩ (Miri.Memory.ScalarInt.ofUInt8 7) :=
      ⟨Or.inl rfl, by rw [scalarModulus_eq_two_pow]; decide, rfl, rfl⟩
    have hinit :
        step1Alloc.initializationMask.isRangeInitialized
          (Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 1)) = .ok (.ok ()) :=
      initMaskWordRel_isRangeInitialized hmask1 (by decide) (by decide)
        (fun b _ hhi => by
          have hb1 : b < 1 := hhi
          rw [hbits1 b (by omega)]; simp [hb1])
    have hbnd : Miri.ABI.Size.ZERO.bytes.toNat + (translateSizeBytes 1).bytes.toNat ≤
        step1Alloc.byteSize.bytes.toNat := by rw [hbs1]; decide
    exact ⟨nofun, trivial, lm22_u8_prim,
      .single _ 0 u8Ty (.scalar ⟨7, 1⟩) rfl,
      ⟨7, 1⟩, Miri.Memory.ScalarInt.ofUInt8 7, rfl,
      hsr, rfl, nofun, nofun, hinit,
      alloc_readScalar_at_offset hsr hlenA hbnd hinit hex1_0⟩
  | 1 =>
    simp only [lm22SuperOuterFields, lm22SuperOuterPaths, List.getElem_cons_succ,
      List.getElem_cons_zero]
    have hsr : ScalarRel ⟨10, 4⟩ (Miri.Memory.ScalarInt.ofUInt32 10) :=
      ⟨Or.inr (Or.inr (Or.inl rfl)), by rw [scalarModulus_eq_two_pow]; decide, rfl, rfl⟩
    have hinit :
        step1Alloc.initializationMask.isRangeInitialized
          (Miri.Memory.allocRange (Miri.ABI.Size.ofBytes 4) (Miri.ABI.Size.ofBytes 4)) =
          .ok (.ok ()) :=
      initMaskWordRel_isRangeInitialized hmask1 (by decide) (by decide)
        (fun b hlo hhi => by
          have hb4 : 4 ≤ b := hlo
          have hb8 : b < 4 + 4 := hhi
          rw [hbits1 b (by omega)]; simp [hb4])
    have hbnd : (Miri.ABI.Size.ofBytes 4).bytes.toNat + (translateSizeBytes 4).bytes.toNat ≤
        step1Alloc.byteSize.bytes.toNat := by rw [hbs1]; decide
    have hex : (lm22AllocRaw step1Alloc).extract (Miri.ABI.Size.ofBytes 4).bytes.toNat
        ((Miri.ABI.Size.ofBytes 4).bytes.toNat + (translateSizeBytes 4).bytes.toNat) =
        lm22LeBytes 10 (translateSizeBytes 4).bytes.toNat := by
      have hsub := congrArg (fun a => a.extract 0 4) hex1_4
      rw [Array.extract_extract] at hsub
      exact hsub.trans (by decide)
    exact ⟨nofun, trivial, lm22_u32_prim,
      .cons _ 1 lm22SuperTripleTy [.field 0 lm22U32Ty] _ rfl htriple_len
        (.single _ 0 lm22U32Ty (.scalar ⟨10, 4⟩) rfl),
      ⟨10, 4⟩, Miri.Memory.ScalarInt.ofUInt32 10, rfl,
      hsr, rfl, nofun, nofun, hinit,
      alloc_readScalar_at_offset hsr hlenA hbnd hinit hex⟩
  | 2 =>
    simp only [lm22SuperOuterFields, lm22SuperOuterPaths, List.getElem_cons_succ,
      List.getElem_cons_zero]
    have hsr : ScalarRel ⟨20, 4⟩ (Miri.Memory.ScalarInt.ofUInt32 20) :=
      ⟨Or.inr (Or.inr (Or.inl rfl)), by rw [scalarModulus_eq_two_pow]; decide, rfl, rfl⟩
    have hinit :
        step1Alloc.initializationMask.isRangeInitialized
          (Miri.Memory.allocRange (Miri.ABI.Size.ofBytes 8) (Miri.ABI.Size.ofBytes 4)) =
          .ok (.ok ()) :=
      initMaskWordRel_isRangeInitialized hmask1 (by decide) (by decide)
        (fun b hlo hhi => by
          have hb8 : 8 ≤ b := hlo
          have hb12 : b < 8 + 4 := hhi
          rw [hbits1 b (by omega)]; simp [show 4 ≤ b by omega])
    have hbnd : (Miri.ABI.Size.ofBytes 8).bytes.toNat + (translateSizeBytes 4).bytes.toNat ≤
        step1Alloc.byteSize.bytes.toNat := by rw [hbs1]; decide
    have hex : (lm22AllocRaw step1Alloc).extract (Miri.ABI.Size.ofBytes 8).bytes.toNat
        ((Miri.ABI.Size.ofBytes 8).bytes.toNat + (translateSizeBytes 4).bytes.toNat) =
        lm22LeBytes 20 (translateSizeBytes 4).bytes.toNat := by
      have hsub := congrArg (fun a => a.extract 4 8) hex1_4
      rw [Array.extract_extract] at hsub
      exact hsub.trans (by decide)
    exact ⟨nofun, trivial, lm22_u32_prim,
      .cons _ 1 lm22SuperTripleTy [.field 1 lm22U32Ty] _ rfl htriple_len
        (.single _ 1 lm22U32Ty (.scalar ⟨20, 4⟩) rfl),
      ⟨20, 4⟩, Miri.Memory.ScalarInt.ofUInt32 20, rfl,
      hsr, rfl, nofun, nofun, hinit,
      alloc_readScalar_at_offset hsr hlenA hbnd hinit hex⟩
  | 3 =>
    simp only [lm22SuperOuterFields, lm22SuperOuterPaths, List.getElem_cons_succ,
      List.getElem_cons_zero]
    have hsr : ScalarRel ⟨30, 4⟩ (Miri.Memory.ScalarInt.ofUInt32 30) :=
      ⟨Or.inr (Or.inr (Or.inl rfl)), by rw [scalarModulus_eq_two_pow]; decide, rfl, rfl⟩
    have hinit :
        step1Alloc.initializationMask.isRangeInitialized
          (Miri.Memory.allocRange (Miri.ABI.Size.ofBytes 12) (Miri.ABI.Size.ofBytes 4)) =
          .ok (.ok ()) :=
      initMaskWordRel_isRangeInitialized hmask1 (by decide) (by decide)
        (fun b hlo hhi => by
          have hb12 : 12 ≤ b := hlo
          have hb16 : b < 12 + 4 := hhi
          rw [hbits1 b (by omega)]; simp [show 4 ≤ b by omega])
    have hbnd : (Miri.ABI.Size.ofBytes 12).bytes.toNat + (translateSizeBytes 4).bytes.toNat ≤
        step1Alloc.byteSize.bytes.toNat := by rw [hbs1]; decide
    have hex : (lm22AllocRaw step1Alloc).extract (Miri.ABI.Size.ofBytes 12).bytes.toNat
        ((Miri.ABI.Size.ofBytes 12).bytes.toNat + (translateSizeBytes 4).bytes.toNat) =
        lm22LeBytes 30 (translateSizeBytes 4).bytes.toNat := by
      have hsub := congrArg (fun a => a.extract 8 12) hex1_4
      rw [Array.extract_extract] at hsub
      exact hsub.trans (by decide)
    exact ⟨nofun, trivial, lm22_u32_prim,
      .cons _ 1 lm22SuperTripleTy [.field 2 lm22U32Ty] _ rfl htriple_len
        (.single _ 2 lm22U32Ty (.scalar ⟨30, 4⟩) rfl),
      ⟨30, 4⟩, Miri.Memory.ScalarInt.ofUInt32 30, rfl,
      hsr, rfl, nofun, nofun, hinit,
      alloc_readScalar_at_offset hsr hlenA hbnd hinit hex⟩
  | _ + 4 =>
    simp [lm22SuperOuterFields] at hi
    omega

private theorem lm22SuperOuter_hsmpr1
    {step1Alloc : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    {words1 : Array UInt64}
    (hbs1 : step1Alloc.byteSize = Miri.ABI.Size.ofBytes 16)
    (hlen1 : step1Alloc.len = 16)
    (hmut1 : step1Alloc.mutability = .Mut)
    (hprov1 : step1Alloc.provenanceMap = Miri.Memory.ProvenanceMap.new)
    (hmask1 : InitMaskWordRel step1Alloc.initializationMask (Miri.ABI.Size.ofBytes 16) words1)
    (hbits1 : ∀ b < 16, maskBlocksGetBit words1 b = decide (b < 1 ∨ 4 ≤ b))
    (hex1_0 : (lm22AllocRaw step1Alloc).extract 0 1 = lm22LeBytes 7 1)
    (hex1_4 : (lm22AllocRaw step1Alloc).extract 4 16 =
      #[10, 0, 0, 0, 20, 0, 0, 0, 30, 0, 0, 0]) :
    StructMemPlaceRel
      (lm22SuperOuterMiriStateAt (.mir ⟨0, 1⟩) (.live (.immediate .uninit)) step1Alloc).machine
      lm22SuperOuterTy lm22SuperLayoutTable
      lm22SuperOuterFields lm22SuperOuterPaths
      (.aggregate 0 [.scalar ⟨7, 1⟩,
        .aggregate 0 [.scalar ⟨10, 4⟩, .scalar ⟨20, 4⟩, .scalar ⟨30, 4⟩]])
      (stackAllocPlace lm22AllocId1) := by
  have hnz1 :
      NoZeroByteLeaves (.aggregate 0 [.scalar ⟨7, 1⟩,
        .aggregate 0 [.scalar ⟨10, 4⟩, .scalar ⟨20, 4⟩, .scalar ⟨30, 4⟩]]) := by
    change 0 < 1 ∧ ((0 < 4 ∧ (0 < 4 ∧ (0 < 4 ∧ True))) ∧ True)
    decide
  refine .mk lm22AllocId1 Miri.Memory.BorTag.one (annealStackBaseAddr lm22AllocId1)
    ⟨.stack, step1Alloc⟩ words1
    lm22SuperOuter_validStructLayout rfl
    ⟨⟨_, _, rfl⟩, hnz1⟩
    rfl rfl rfl rfl
    ⟨rfl, 0, Nat.zero_lt_succ 1,
      by rw [List.findIdx?_toArray]; rfl, rfl⟩
    rfl rfl (by decide) hmut1 (by decide) hbs1
    (by rw [hlen1, hbs1]; rfl) hprov1
    (by rw [hbs1]; exact hmask1)
    ?_
    (lm22SuperOuter_fields_rel1 hbs1 hlen1 hmask1 hbits1 hex1_0 hex1_4)
    ?_
  · intro i hi b hlo hhi
    match i with
    | 0 =>
      have hb1 : b < 1 := hhi
      rw [hbits1 b (by omega)]; simp [hb1]
    | 1 =>
      have hb4 : 4 ≤ b := hlo
      have hb8 : b < 4 + 4 := hhi
      rw [hbits1 b (by omega)]; simp [hb4]
    | 2 =>
      have hb8 : 8 ≤ b := hlo
      have hb12 : b < 8 + 4 := hhi
      rw [hbits1 b (by omega)]; simp [show 4 ≤ b by omega]
    | 3 =>
      have hb12 : 12 ≤ b := hlo
      have hb16 : b < 12 + 4 := hhi
      rw [hbits1 b (by omega)]; simp [show 4 ≤ b by omega]
    | _ + 4 =>
      simp [lm22SuperOuterFields] at hi
      omega
  · intro p hp
    have hp16 : p < 16 := hp.1
    have hp123 : p = 1 ∨ p = 2 ∨ p = 3 := by
      have h0 : p < 0 ∨ 0 + 1 ≤ p := hp.2 (lm22SuperOuterFields[0]'(by decide)) (.head _)
      have h1 : p < 4 ∨ 4 + 4 ≤ p := hp.2 (lm22SuperOuterFields[1]'(by decide)) (.tail _ (.head _))
      have h2 : p < 8 ∨ 8 + 4 ≤ p :=
        hp.2 (lm22SuperOuterFields[2]'(by decide)) (.tail _ (.tail _ (.head _)))
      have h3 : p < 12 ∨ 12 + 4 ≤ p :=
        hp.2 (lm22SuperOuterFields[3]'(by decide)) (.tail _ (.tail _ (.tail _ (.head _))))
      omega
    dsimp only
    rw [initMaskWordRel_get hmask1 hp16, hbits1 p hp16]
    rcases hp123 with rfl | rfl | rfl <;> rfl

theorem lm22SuperOuter_step1_stateRel :
    StateRelLM2_2 lm22SuperOuterBody lm22SuperEnv { initLocals := [1], immLocals := [2, 0] } 2
      (lm22StepAnnealN lm22SuperOuterBody 1 lm22SuperOuterAnnealInit)
      (lm22StepMiriN lm22SuperOuterBody 1 lm22SuperOuterMiriInit) := by
  obtain ⟨step1Alloc, words1, hstep, hbs1, hlen1, hmut1, hprov1, hmask1, hbits1, hex1_0, hex1_4⟩ :=
    lm22SuperOuter_step0_spec
  have hm1 : lm22StepMiriN lm22SuperOuterBody 1 lm22SuperOuterMiriInit =
      lm22SuperOuterMiriStateAt (.mir ⟨0, 1⟩) (.live (.immediate .uninit)) step1Alloc :=
    congrArg Prod.fst hstep
  rw [hm1]
  refine .mk _ rfl rfl ⟨translateTy lm22U32Ty lm22SuperLayoutTable, rfl⟩ ?_
    (fun j hj => by
      simp at hj; subst hj; nofun)
    (fun j hj mp l h => by
      simp at hj
      rcases hj with rfl | rfl <;> cases h)
    (Or.inr (lm22SuperOuter_hwm step1Alloc)) rfl rfl rfl rfl rfl
    (by
      intro i j mp1 mp2 _ _ hne hi hj
      match i, j with
      | 1, 1 => exact False.elim (hne rfl)
      | 0, _ | 2, _ | 3, _ | _ + 4, _ => cases hi
      | _, 0 | _, 2 | _, 3 | _, _ + 4 => cases hj)
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro i decl slot mls hdecl hslot hmls
  match i with
  | 0 =>
    cases Option.some.inj hdecl
    cases Option.some.inj hslot
    cases Option.some.inj hmls
    exact .base .uninit _ rfl
      (.immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩))
  | 1 =>
    cases Option.some.inj hdecl
    cases Option.some.inj hslot
    cases Option.some.inj hmls
    exact .structInd lm22SuperOuterFields lm22SuperOuterPaths _
      (stackAllocPlace lm22AllocId1)
      _ rfl (fun l hl => by cases Option.mem_def.mp hl; rfl)
      (lm22SuperOuter_hsmpr1 hbs1 hlen1 hmut1 hprov1 hmask1 hbits1 hex1_0 hex1_4)
  | 2 =>
    cases Option.some.inj hdecl
    cases Option.some.inj hslot
    cases Option.some.inj hmls
    exact .structUninitImm lm22SuperTripleFields lm22UnpaddedPaths _ rfl
      (fun l hl => by cases Option.mem_def.mp hl; rfl)
  | 3 =>
    cases Option.some.inj hdecl
    cases Option.some.inj hslot
    cases Option.some.inj hmls
    exact .structDead lm22SuperOuterFields lm22SuperOuterPaths none rfl
      (fun _ h => nomatch h)
  | _ + 4 => simp [lm22SuperOuterBody, get?] at hdecl

theorem lm22SuperOuter_full_trace_and_returns_agree :
    (∃ mp3 alloc3,
      StructMemPlaceRel
        (lm22StepMiriN lm22SuperOuterBody 4 lm22SuperOuterMiriInit).machine
        lm22SuperOuterTy lm22SuperLayoutTable lm22SuperOuterFields lm22SuperOuterPaths
        (.aggregate 0 [.scalar ⟨7, 1⟩,
          .aggregate 0 [.scalar ⟨10, 4⟩, .scalar ⟨20, 4⟩, .scalar ⟨0x778899AA, 4⟩]]) mp3 ∧
      (∃ allocId3,
        (∃ tag, mp3.ptr.provenance = some (.concrete allocId3 tag)) ∧
        (lm22StepMiriN lm22SuperOuterBody 4 lm22SuperOuterMiriInit).machine.memory.live.find?
          (fun (k, _) => k == allocId3) = some (allocId3, alloc3)) ∧
      alloc3.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 1) = .ok false ∧
      alloc3.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 2) = .ok false ∧
      alloc3.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 3) = .ok false) ∧
    annealOutcomeScalarBits 4
      (runAnnealBounded lm22SuperOuterBody 9 lm22SuperOuterAnnealInit) = some 0x778899AA ∧
    miriOutcomeScalarBits 4
      (runMiriBoundedLM2_2 lm22SuperOuterBody 9 lm22SuperOuterMiriInit) = some 0x778899AA := by
  have ha0 :
      runAnnealBounded lm22SuperOuterBody 9 lm22SuperOuterAnnealInit =
        runAnnealBounded lm22SuperOuterBody 8
          (lm22StepAnnealN lm22SuperOuterBody 1 lm22SuperOuterAnnealInit) := rfl
  have hm0 :
      runMiriBoundedLM2_2 lm22SuperOuterBody 9 lm22SuperOuterMiriInit =
        runMiriBoundedLM2_2 lm22SuperOuterBody 8
          (lm22StepMiriN lm22SuperOuterBody 1 lm22SuperOuterMiriInit) := by
    obtain ⟨step1Alloc, _, hstep, _⟩ := lm22SuperOuter_step0_spec
    have hm1 : lm22StepMiriN lm22SuperOuterBody 1 lm22SuperOuterMiriInit =
        lm22SuperOuterMiriStateAt (.mir ⟨0, 1⟩) (.live (.immediate .uninit)) step1Alloc :=
      congrArg Prod.fst hstep
    rw [hm1]
    conv => lhs; unfold runMiriBoundedLM2_2
    rw [hstep]
    rfl
  have hs1 := lm22SuperOuter_step1_stateRel
  have ⟨hs2, ha1, hm1⟩ := lm22_trace_step ⟨[1], [3, 2, 0]⟩ (fuel := 7) hs1
    lm22SuperOuter_phase rfl rfl (.storageLive _ 2 3 lm22SuperOuterDecl _ rfl) rfl rfl
  have hwt2 : WellTypedLM2_2Stmt lm22SuperOuterBody lm22SuperEnv ⟨[1], [3, 2, 0]⟩ 2
      (mkStmt22 (.assign ⟨1, [.field 1 lm22SuperTripleTy, .field 2 lm22U32Ty]⟩
        (.use (.constant (lm22ConstU32 0x778899AA)))))
      (fieldWritePostStaticEnv ⟨[1], [3, 2, 0]⟩ 1 (.constant (lm22ConstU32 0x778899AA))) 1 :=
    .assignFieldWrite _ 1 1 [.field 1 lm22SuperTripleTy, .field 2 lm22U32Ty]
      (.constant (lm22ConstU32 0x778899AA)) _
      (.mk lm22SuperOuterDecl lm22SuperOuterFields lm22SuperOuterPaths 3
        rfl rfl (by decide) rfl (by decide) (by decide) rfl
        (fun j hj hne => by
          match j with
          | 0 => exact .diff_head (by decide)
          | 1 => exact .same_head (.diff_head (by decide))
          | 2 => exact .same_head (.diff_head (by decide))
          | 3 => exact False.elim (hne rfl)
          | _ + 4 => simp [lm22SuperOuterPaths] at hj; omega)
        lm22SuperOuter_projChain_triple2
        rfl rfl lm22_u32_prim trivial (lm22_constU32_wt 0x778899AA (by decide) rfl))
  have ⟨hs3, ha2, hm2⟩ := lm22_trace_step ⟨[1], [3, 2, 0]⟩ (fuel := 6) hs2
    lm22SuperOuter_phase rfl rfl hwt2 rfl rfl
  have hwt3 : WellTypedLM2_2Stmt lm22SuperOuterBody lm22SuperEnv ⟨[1], [3, 2, 0]⟩ 1
      (mkStmt22 (.assign ⟨3, []⟩ (.use (.move ⟨1, []⟩))))
      (useStructPostStaticEnv ⟨[1], [3, 2, 0]⟩ 3 (.move ⟨1, []⟩)) 0 :=
    .assignUseMemStruct _ 0 3 true 1 _
      (.mk lm22SuperOuterDecl lm22SuperOuterDecl lm22SuperOuterFields lm22SuperOuterPaths _ _
        (by decide) rfl rfl rfl rfl (Or.inl (by decide)) rfl rfl
        (by decide) (by decide) rfl (by decide))
  have ⟨hs4, ha3, hm3⟩ := lm22_trace_step ⟨[3], [1, 2, 0]⟩ (fuel := 5) hs3
    lm22SuperOuter_phase rfl rfl hwt3 rfl rfl
  have hwt4 : WellTypedLM2_2Stmt lm22SuperOuterBody lm22SuperEnv ⟨[3], [1, 2, 0]⟩ 0
      (mkStmt22 (.assign ⟨0, []⟩
        (.use (.copy ⟨3, [.field 1 lm22SuperTripleTy, .field 2 lm22U32Ty]⟩))))
      (usePostStaticEnv ⟨[3], [1, 2, 0]⟩ 0
        (.copy ⟨3, [.field 1 lm22SuperTripleTy, .field 2 lm22U32Ty]⟩)) 0 :=
    .assignUse _ 0 0 _ _
      (.mk lm22U32Decl rfl (by decide)
        (.projectedScalar false 3 [.field 1 lm22SuperTripleTy, .field 2 lm22U32Ty]
          lm22U32Ty rfl
          (.mk lm22SuperOuterDecl lm22SuperOuterFields lm22SuperOuterPaths 3
            (by decide) (by decide) rfl rfl rfl rfl lm22_u32_prim
            lm22SuperOuter_projChain_triple2)))
  have ⟨hs5, ha4, hm4⟩ := lm22_trace_step ⟨[0, 3], [0, 1, 2, 0]⟩ (fuel := 4) hs4
    lm22SuperOuter_phase rfl rfl hwt4 rfl rfl
  have ⟨hs6, ha5, hm5⟩ := lm22_trace_step ⟨[3, 0, 3], [3, 0, 1, 2, 0]⟩ (fuel := 3) hs5
    lm22SuperOuter_phase rfl rfl (.storageDead _ 0 3 lm22SuperOuterDecl _ rfl (by decide)) rfl rfl
  have ⟨hs7, ha6, hm6⟩ := lm22_trace_step ⟨[2, 3, 0, 3], [2, 3, 0, 1, 2, 0]⟩ (fuel := 2) hs6
    lm22SuperOuter_phase rfl rfl (.storageDead _ 0 2 lm22SuperTripleDecl _ rfl (by decide)) rfl rfl
  have ⟨hs8, ha7, hm7⟩ := lm22_trace_step ⟨[1, 2, 3, 0, 3], [1, 2, 3, 0, 1, 2, 0]⟩ (fuel := 1) hs7
    lm22SuperOuter_phase rfl rfl (.storageDead _ 0 1 lm22SuperOuterDecl _ rfl (by decide)) rfl rfl
  obtain ⟨p1, p2, p3⟩ := lm22SuperOuter_padding_bytes
  have hpad4 :
      ∃ mp3 alloc3,
        StructMemPlaceRel
          (lm22StepMiriN lm22SuperOuterBody 4 lm22SuperOuterMiriInit).machine
          lm22SuperOuterTy lm22SuperLayoutTable lm22SuperOuterFields lm22SuperOuterPaths
          (.aggregate 0 [.scalar ⟨7, 1⟩,
            .aggregate 0 [.scalar ⟨10, 4⟩, .scalar ⟨20, 4⟩, .scalar ⟨0x778899AA, 4⟩]]) mp3 ∧
        (∃ allocId3,
          (∃ tag, mp3.ptr.provenance = some (.concrete allocId3 tag)) ∧
          (lm22StepMiriN lm22SuperOuterBody 4 lm22SuperOuterMiriInit).machine.memory.live.find?
            (fun (k, _) => k == allocId3) = some (allocId3, alloc3)) ∧
        alloc3.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 1) = .ok false ∧
        alloc3.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 2) = .ok false ∧
        alloc3.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 3) = .ok false := by
    obtain ⟨mp3, _, _, _, _, hsmpr3⟩ :=
      hs4.extract_structMemPlaceRel (idx := 3) (decl := lm22SuperOuterDecl) rfl rfl rfl rfl
    obtain ⟨allocId3, alloc3, hprov3, hfind3, hpad_fn3, _⟩ :=
      hsmpr3.has_uninit_of_padding_byte p1
    exact ⟨mp3, alloc3, hsmpr3, ⟨allocId3, hprov3, hfind3⟩,
      hpad_fn3 1 p1, hpad_fn3 2 p2, hpad_fn3 3 p3⟩
  obtain ⟨ha_ret, hm_ret⟩ := lm22_return_agree_of_stateRelLM2_2 hs8 lm22SuperOuter_phase
    rfl rfl rfl rfl rfl rfl rfl lm22_u32_prim (by decide) rfl
  have ha_tot :
      runAnnealBounded lm22SuperOuterBody 9 lm22SuperOuterAnnealInit =
        runAnnealBounded lm22SuperOuterBody 1
          (lm22StepAnnealN lm22SuperOuterBody 8 lm22SuperOuterAnnealInit) :=
    ha0.trans (ha1.trans (ha2.trans (ha3.trans (ha4.trans (ha5.trans (ha6.trans ha7))))))
  have hm_tot :
      runMiriBoundedLM2_2 lm22SuperOuterBody 9 lm22SuperOuterMiriInit =
        runMiriBoundedLM2_2 lm22SuperOuterBody 1 (lm22StepMiriN lm22SuperOuterBody 8 lm22SuperOuterMiriInit) :=
    hm0.trans (hm1.trans (hm2.trans (hm3.trans (hm4.trans (hm5.trans (hm6.trans hm7))))))
  rw [ha_tot, hm_tot]
  exact ⟨hpad4, ha_ret, hm_ret⟩

/-! ## 15. Freed/Dangling Allocation UB in `annealStructMemCopyOp` -/

def lm22DanglingSrcCopyState : AnnealStepState :=
  { lm22ReadOnlyCopyState with
    machine :=
      { lm22ReadOnlyCopyState.machine with
        memory :=
          { lm22ReadOnlyCopyState.machine.memory with
            live := #[(lm22AllocId2, ⟨.stack, lm22ReadOnlyAlloc⟩)] } } }

def lm22DanglingDestCopyState : AnnealStepState :=
  { lm22ReadOnlyCopyState with
    machine :=
      { lm22ReadOnlyCopyState.machine with
        memory :=
          { lm22ReadOnlyCopyState.machine.memory with
            live := #[(lm22AllocId1, ⟨.stack, lm22ReadOnlyAlloc⟩)] } } }

theorem lm22DanglingSrcCopy_ub :
    annealStructMemCopyOp lm22MemMoveUbBody.localDecls lm22NestedLayoutTable
      ⟨.indirect (stackAllocPlace lm22AllocId1),
        translateTy lm22NestedTy lm22NestedLayoutTable⟩
      ⟨.local 0 2 none (.ofAllocationToken 0),
        translateTy lm22NestedTy lm22NestedLayoutTable⟩
      lm22DanglingSrcCopyState =
    .error (.undefinedBehavior "dangling allocation in memory copy")
      lm22DanglingSrcCopyState :=
  annealStructMemCopyOp_dangling_src_ub
    rfl (by decide) rfl rfl rfl rfl

theorem lm22DanglingDestCopy_ub :
    annealStructMemCopyOp lm22MemMoveUbBody.localDecls lm22NestedLayoutTable
      ⟨.indirect (stackAllocPlace lm22AllocId1),
        translateTy lm22NestedTy lm22NestedLayoutTable⟩
      ⟨.local 0 2 none (.ofAllocationToken 0),
        translateTy lm22NestedTy lm22NestedLayoutTable⟩
      lm22DanglingDestCopyState =
    .error (.undefinedBehavior "dangling allocation in memory copy")
      lm22DanglingDestCopyState :=
  annealStructMemCopyOp_dangling_dest_ub
    rfl (by decide) rfl rfl rfl
    ⟨rfl, 0, by decide, by rw [List.findIdx?_toArray]; rfl, rfl⟩
    rfl rfl (by rw [List.findIdx?_toArray]; rfl)

/-! ## 16. Struct-Returning Root Function (`step_terminator_return_struct_lm2_2_simulation`) -/

def lm22FnAbiPadded : FnAbi :=
  { args := []
    ret := { layout := lm22PaddedTypeLayout, mode := .indirect }
    conv := .rust
    canUnwind := false }

def lm22StructRetBody : CapturedMir where
  defPath := "lm_2_2_witness::return_padded_outer"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [lm22PaddedDecl, lm22InnerU32Decl]
  basicBlocks := [
    { statements := [
        mkStmt22 (.storageLive 1),
        mkStmt22 (.assign ⟨1, []⟩
          (.aggregate (.adt "lm22::InnerU32" 0 .none) [.constant (lm22ConstU32 42)])),
        mkStmt22 (.assign ⟨0, []⟩
          (.aggregate (.adt "lm22::PaddedOuter" 0 .none)
            [.constant (constU8 7), .move ⟨1, []⟩])),
        mkStmt22 (.assign ⟨0, [.field 1 lm22InnerU32Ty, .field 0 lm22U32Ty]⟩
          (.use (.constant (lm22ConstU32 0xDEADBEEF)))),
        mkStmt22 (.storageDead 1)],
      terminator := mkTerm22 .return_,
      isCleanup := false }]
  fnAbi := lm22FnAbiPadded
  layouts := lm22PaddedLayoutTable
  allocations := []

def lm22StructRetMiriInit : AnnealStepState :=
  { stack := ⟨#[{
      body := translateBody lm22StructRetBody
      bodyIdentity := .ofCanonicalIndex 0
      functionInstance := { kind := .Item 0, args := #[] }
      extra := ()
      returnContinuation := .stop false
      returnPlace :=
        .frameLocal 0 0 none (translateTy lm22PaddedTy lm22PaddedLayoutTable) (.ofAllocationToken 0)
      localsIdentity := .ofAllocationToken 0
      locals := #[
        { value := .live (.immediate .uninit), layout := none },
        { value := .dead, layout := none }]
      vaList := #[]
      trackCallerArg := none
      location := .mir ⟨0, 0⟩ }]⟩
    machine := AnnealMachine.empty }

theorem lm22StructRet_phase : ∀ p, lm22StructRetBody.phase ≠ .other p := by
  intro p h; cases h

theorem lm22StructRet_stateRelLM2_2_init :
    StateRelLM2_2 lm22StructRetBody lm22PaddedEnv { initLocals := [], immLocals := [0] } 3
      (initMachineState lm22StructRetBody []) lm22StructRetMiriInit := by
  refine .mk _ rfl rfl ⟨translateTy lm22PaddedTy lm22PaddedLayoutTable, rfl⟩ ?_
    (fun _ h => nomatch h)
    (fun j hj _ _ => by simp at hj; subst hj; dsimp [lm22StructRetMiriInit]; nofun)
    (Or.inr (AllocIdWatermark.empty 3 (by decide))) rfl rfl rfl rfl rfl
    (by intro i _ _ _ _ _ _ hi _; revert hi; match i with | 0 | 1 | _ + 2 => rintro ⟨⟩)
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro i decl slot mls hdecl hslot hmls
  match i with
  | 0 =>
    cases Option.some.inj hdecl
    cases Option.some.inj hslot
    cases Option.some.inj hmls
    exact .structUninitImm lm22PaddedFields lm22PaddedPaths none rfl (fun _ h => nomatch h)
  | 1 =>
    cases Option.some.inj hdecl
    cases Option.some.inj hslot
    cases Option.some.inj hmls
    exact .structDead [lm22InnerU32Field0] [[.field 0 lm22U32Ty]] none rfl (fun _ h => nomatch h)
  | _ + 2 => simp [lm22StructRetBody, get?] at hdecl

theorem lm22StructRet_full_trace_and_struct_return :
    runAnnealBounded lm22StructRetBody 6 (initMachineState lm22StructRetBody []) =
      .returned (.aggregate 0 [.scalar ⟨7, 1⟩, .aggregate 0 [.scalar ⟨0xDEADBEEF, 4⟩]])
        (initMachineState lm22StructRetBody []).memory ∧
    ∃ m_ret mp0 alloc0,
      runMiriBoundedLM2_2 lm22StructRetBody 6 lm22StructRetMiriInit =
        .returned m_ret (.ok (.indirect mp0)) ∧
      StructMemPlaceRel m_ret.machine lm22PaddedTy lm22PaddedLayoutTable
        lm22PaddedFields lm22PaddedPaths
        (.aggregate 0 [.scalar ⟨7, 1⟩, .aggregate 0 [.scalar ⟨0xDEADBEEF, 4⟩]]) mp0 ∧
      (∃ allocId0,
        (∃ tag, mp0.ptr.provenance = some (.concrete allocId0 tag)) ∧
        m_ret.machine.memory.live.find? (fun (k, _) => k == allocId0) = some (allocId0, alloc0)) ∧
      alloc0.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 1) = .ok false ∧
      alloc0.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 2) = .ok false ∧
      alloc0.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 3) = .ok false := by
  have hs0 : StateRelLM2_2 lm22StructRetBody lm22PaddedEnv { initLocals := [], immLocals := [0] } 3
      (lm22StepAnnealN lm22StructRetBody 0 (initMachineState lm22StructRetBody []))
      (lm22StepMiriN lm22StructRetBody 0 lm22StructRetMiriInit) :=
    lm22StructRet_stateRelLM2_2_init
  have ⟨hs1, ha0, hm0⟩ := lm22_trace_step ⟨[], [1, 0]⟩ (fuel := 5) hs0
    lm22StructRet_phase rfl rfl (.storageLive _ 3 1 lm22InnerU32Decl _ rfl) rfl rfl
  have hwt1 : WellTypedLM2_2Stmt lm22StructRetBody lm22PaddedEnv ⟨[], [1, 0]⟩ 3
      (mkStmt22 (.assign ⟨1, []⟩
        (.aggregate (.adt "lm22::InnerU32" 0 .none) [.constant (lm22ConstU32 42)])))
      (aggPostStaticEnv ⟨[], [1, 0]⟩ 1 [.constant (lm22ConstU32 42)]) 2 :=
    .assignAggregate _ 2 1 _ _ _
      (.mk lm22InnerU32Decl [lm22InnerU32Field0] [[.field 0 lm22U32Ty]] _ [] rfl
        (Or.inr ⟨"lm22::InnerU32", rfl⟩) rfl rfl lm22InnerU32_validStructLayout
        (by decide) rfl rfl (by decide)
        (.cons _ 0 0 1 _ [] trivial
          (.primLeaf (by decide) _ (lm22_constU32_wt 42 (by decide) rfl)
            rfl lm22_u32_prim rfl rfl rfl rfl rfl rfl)
          (.nil _ 1)))
  have ⟨hs2, ha1, hm1⟩ := lm22_trace_step ⟨[1], [0]⟩ (fuel := 4) hs1
    lm22StructRet_phase rfl rfl hwt1 rfl rfl
  have hwt2 : WellTypedLM2_2Stmt lm22StructRetBody lm22PaddedEnv ⟨[1], [0]⟩ 2
      (mkStmt22 (.assign ⟨0, []⟩
        (.aggregate (.adt "lm22::PaddedOuter" 0 .none)
          [.constant (constU8 7), .move ⟨1, []⟩])))
      (aggPostStaticEnv ⟨[1], [0]⟩ 0 [.constant (constU8 7), .move ⟨1, []⟩]) 1 :=
    .assignAggregate _ 1 0 _ _ _
      (.mk lm22PaddedDecl lm22PaddedFields lm22PaddedPaths _ _ rfl
        (Or.inr ⟨"lm22::PaddedOuter", rfl⟩) rfl rfl lm22Padded_validStructLayout
        (by decide) rfl rfl (by decide)
        (.cons _ 0 0 1 _ _ trivial
          (.primLeaf (by decide) _ (lm22_constU8_wt 7 (by decide) rfl)
            rfl lm22_u8_prim rfl rfl rfl rfl rfl rfl)
          (.cons _ 1 1 2 (.move ⟨1, []⟩) [] (by decide : (1 : Nat) ≠ 0)
            (.scalarWrapSub (by decide) lm22InnerU32Ty lm22InnerU32Field0
              [.field 0 lm22U32Ty] _
              (.immStructLocal true 1 lm22InnerU32Decl [lm22InnerU32Field0]
                [[.field 0 lm22U32Ty]] rfl lm22InnerU32_isImmediateStructTy)
              lm22InnerU32_isImmediateStructTy rfl rfl rfl rfl rfl rfl rfl)
            (.nil _ 2))))
  have ⟨hs3, ha2, hm2⟩ := lm22_trace_step ⟨[0], [1]⟩ (fuel := 3) hs2
    lm22StructRet_phase rfl rfl hwt2 rfl rfl
  have hwt3 : WellTypedLM2_2Stmt lm22StructRetBody lm22PaddedEnv ⟨[0], [1]⟩ 1
      (mkStmt22 (.assign ⟨0, [.field 1 lm22InnerU32Ty, .field 0 lm22U32Ty]⟩
        (.use (.constant (lm22ConstU32 0xDEADBEEF)))))
      (fieldWritePostStaticEnv ⟨[0], [1]⟩ 0 (.constant (lm22ConstU32 0xDEADBEEF))) 0 :=
    .assignFieldWrite _ 0 0 [.field 1 lm22InnerU32Ty, .field 0 lm22U32Ty]
      (.constant (lm22ConstU32 0xDEADBEEF)) _
      (.mk lm22PaddedDecl lm22PaddedFields lm22PaddedPaths 1 rfl rfl (by decide)
        rfl (by decide) (by decide) rfl
        (fun j hj hne => by
          match j with
          | 0 => exact .diff_head (by decide)
          | 1 => exact False.elim (hne rfl)
          | _ + 2 => simp [lm22PaddedPaths] at hj; omega)
        lm22Padded_projChain_inner0
        rfl rfl lm22_u32_prim trivial (lm22_constU32_wt 0xDEADBEEF (by decide) rfl))
  have ⟨hs4, ha3, hm3⟩ := lm22_trace_step ⟨[0], [1]⟩ (fuel := 2) hs3
    lm22StructRet_phase rfl rfl hwt3 rfl rfl
  have ⟨hs5, ha4, hm4⟩ := lm22_trace_step ⟨[1, 0], [1, 1]⟩ (fuel := 1) hs4
    lm22StructRet_phase rfl rfl (.storageDead _ 0 1 lm22InnerU32Decl _ rfl (by decide)) rfl rfl
  have ha_tot :
      runAnnealBounded lm22StructRetBody 6 (initMachineState lm22StructRetBody []) =
        runAnnealBounded lm22StructRetBody 1
          (lm22StepAnnealN lm22StructRetBody 5 (initMachineState lm22StructRetBody [])) :=
    ha0.trans (ha1.trans (ha2.trans (ha3.trans ha4)))
  have hm_tot :
      runMiriBoundedLM2_2 lm22StructRetBody 6 lm22StructRetMiriInit =
        runMiriBoundedLM2_2 lm22StructRetBody 1 (lm22StepMiriN lm22StructRetBody 5 lm22StructRetMiriInit) :=
    hm0.trans (hm1.trans (hm2.trans (hm3.trans hm4)))
  have ha5 :
      stepMirFn lm22StructRetBody
          (lm22StepAnnealN lm22StructRetBody 5 (initMachineState lm22StructRetBody [])) =
        .retNormal (.aggregate 0 [.scalar ⟨7, 1⟩, .aggregate 0 [.scalar ⟨0xDEADBEEF, 4⟩]])
          (initMachineState lm22StructRetBody []).memory := rfl
  have hsim := step_terminator_return_struct_lm2_2_simulation hs5 lm22StructRet_phase
    rfl rfl rfl rfl rfl (decl0 := lm22PaddedDecl) rfl rfl (Or.inl (by decide))
  rw [ha5] at hsim
  generalize hm5 :
    Miri.Interpreter.Step.step
        (annealStepHooksLM2_2 lm22StructRetBody.localDecls lm22StructRetBody.layouts) ()
        (lm22StepMiriN lm22StructRetBody 5 lm22StructRetMiriInit) = r5 at hsim
  refine ⟨by rw [ha_tot]; rfl, ?_⟩
  cases hsim with
  | retRootImm decl0' _ imm0 _ _ hdecl0' _ himmRel _ =>
    cases Option.some.inj hdecl0'
    exact False.elim (lm22_not_immediateStructRel_of_memory rfl himmRel)
  | retRootMem decl0' _ mp0 _ m_ret hdecl0' hretOp hsmpr hm_ret_eq =>
    cases Option.some.inj hdecl0'
    have hemp : m_ret.stack.frames.isEmpty = true := by rw [hm_ret_eq]; rfl
    have hm_out :
        runMiriBoundedLM2_2 lm22StructRetBody 1
            (lm22StepMiriN lm22StructRetBody 5 lm22StructRetMiriInit) =
          .returned m_ret (.ok (.indirect mp0)) := by
      unfold runMiriBoundedLM2_2
      rw [hm5]; dsimp only; rw [hemp, hretOp]; rfl
    obtain ⟨allocId0, alloc0, hprov0, hfind0, hpad_fn0, _⟩ :=
      hsmpr.has_uninit_of_padding_byte lm22Padded_interfield_padding_bytes.1
    exact ⟨m_ret, mp0, alloc0, hm_tot.trans hm_out, hsmpr, ⟨allocId0, hprov0, hfind0⟩,
      hpad_fn0 1 lm22Padded_interfield_padding_bytes.1,
      hpad_fn0 2 lm22Padded_interfield_padding_bytes.2.1,
      hpad_fn0 3 lm22Padded_interfield_padding_bytes.2.2⟩

/-! ## 17. Self-Move Lockstep vs. Self-Copy `copyRangesOverlap` Divergence -/

def lm22SelfMoveBody : CapturedMir where
  defPath := "lm_2_2_witness::self_move_padded_outer"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [lm22U32Decl, lm22PaddedDecl, lm22InnerU32Decl]
  basicBlocks := [
    { statements := [
        mkStmt22 (.storageLive 1),
        mkStmt22 (.storageLive 2),
        mkStmt22 (.assign ⟨2, []⟩
          (.aggregate (.adt "lm22::InnerU32" 0 .none) [.constant (lm22ConstU32 0xCAFE1234)])),
        mkStmt22 (.assign ⟨1, []⟩
          (.aggregate (.adt "lm22::PaddedOuter" 0 .none)
            [.constant (constU8 7), .move ⟨2, []⟩])),
        mkStmt22 (.assign ⟨1, []⟩ (.use (.move ⟨1, []⟩))),
        mkStmt22 (.assign ⟨0, []⟩
          (.use (.copy ⟨1, [.field 1 lm22InnerU32Ty, .field 0 lm22U32Ty]⟩))),
        mkStmt22 (.storageDead 2),
        mkStmt22 (.storageDead 1)],
      terminator := mkTerm22 .return_,
      isCleanup := false }]
  fnAbi := lm22FnAbiU32
  layouts := lm22PaddedLayoutTable
  allocations := []

def lm22SelfMoveMiriInit : AnnealStepState :=
  { stack := ⟨#[{
      body := translateBody lm22SelfMoveBody
      bodyIdentity := .ofCanonicalIndex 0
      functionInstance := { kind := .Item 0, args := #[] }
      extra := ()
      returnContinuation := .stop false
      returnPlace :=
        .frameLocal 0 0 none (translateTy lm22U32Ty lm22PaddedLayoutTable) (.ofAllocationToken 0)
      localsIdentity := .ofAllocationToken 0
      locals := #[
        { value := .live (.immediate .uninit), layout := none },
        { value := .dead, layout := none },
        { value := .dead, layout := none }]
      vaList := #[]
      trackCallerArg := none
      location := .mir ⟨0, 0⟩ }]⟩
    machine := AnnealMachine.empty }

theorem lm22SelfMove_phase : ∀ p, lm22SelfMoveBody.phase ≠ .other p := by
  intro p h; cases h

theorem lm22SelfMove_stateRelLM2_2_init :
    StateRelLM2_2 lm22SelfMoveBody lm22PaddedEnv { initLocals := [], immLocals := [0] } 3
      (initMachineState lm22SelfMoveBody []) lm22SelfMoveMiriInit := by
  refine .mk _ rfl rfl ⟨translateTy lm22U32Ty lm22PaddedLayoutTable, rfl⟩ ?_
    (fun _ h => nomatch h)
    (fun j hj _ _ => by simp at hj; subst hj; dsimp [lm22SelfMoveMiriInit]; nofun)
    (Or.inr (AllocIdWatermark.empty 3 (by decide))) rfl rfl rfl rfl rfl
    (by intro i _ _ _ _ _ _ hi _; revert hi; match i with | 0 | 1 | 2 | _ + 3 => rintro ⟨⟩)
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro i decl slot mls hdecl hslot hmls
  match i with
  | 0 =>
    cases Option.some.inj hdecl; cases Option.some.inj hslot; cases Option.some.inj hmls
    exact .base .uninit _ rfl (.immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩))
  | 1 =>
    cases Option.some.inj hdecl; cases Option.some.inj hslot; cases Option.some.inj hmls
    exact .structDead lm22PaddedFields lm22PaddedPaths none rfl (fun _ h => nomatch h)
  | 2 =>
    cases Option.some.inj hdecl; cases Option.some.inj hslot; cases Option.some.inj hmls
    exact .structDead [lm22InnerU32Field0] [[.field 0 lm22U32Ty]] none rfl (fun _ h => nomatch h)
  | _ + 3 => simp [lm22SelfMoveBody, get?] at hdecl

theorem lm22SelfMove_full_trace_and_returns_agree :
    (∃ mp localAlloc,
      StructMemPlaceRel
        (lm22StepMiriN lm22SelfMoveBody 5 lm22SelfMoveMiriInit).machine
        lm22PaddedTy lm22PaddedLayoutTable lm22PaddedFields lm22PaddedPaths
        (.aggregate 0 [.scalar ⟨7, 1⟩, .aggregate 0 [.scalar ⟨0xCAFE1234, 4⟩]]) mp ∧
      (∃ allocId,
        (∃ tag, mp.ptr.provenance = some (.concrete allocId tag)) ∧
        (lm22StepMiriN lm22SelfMoveBody 5 lm22SelfMoveMiriInit).machine.memory.live.find?
          (fun (k, _) => k == allocId) = some (allocId, localAlloc)) ∧
      localAlloc.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 1) = .ok false ∧
      localAlloc.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 2) = .ok false ∧
      localAlloc.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 3) = .ok false) ∧
    annealOutcomeScalarBits 4
      (runAnnealBounded lm22SelfMoveBody 9 (initMachineState lm22SelfMoveBody [])) = some 0xCAFE1234 ∧
    miriOutcomeScalarBits 4
      (runMiriBoundedLM2_2 lm22SelfMoveBody 9 lm22SelfMoveMiriInit) = some 0xCAFE1234 := by
  have hs0 : StateRelLM2_2 lm22SelfMoveBody lm22PaddedEnv { initLocals := [], immLocals := [0] } 3
      (lm22StepAnnealN lm22SelfMoveBody 0 (initMachineState lm22SelfMoveBody []))
      (lm22StepMiriN lm22SelfMoveBody 0 lm22SelfMoveMiriInit) :=
    lm22SelfMove_stateRelLM2_2_init
  have ⟨hs1, ha0, hm0⟩ := lm22_trace_step ⟨[], [1, 0]⟩ (fuel := 8) hs0
    lm22SelfMove_phase rfl rfl (.storageLive _ 3 1 lm22PaddedDecl _ rfl) rfl rfl
  have ⟨hs2, ha1, hm1⟩ := lm22_trace_step ⟨[], [2, 1, 0]⟩ (fuel := 7) hs1
    lm22SelfMove_phase rfl rfl (.storageLive _ 3 2 lm22InnerU32Decl _ rfl) rfl rfl
  have hwt2 : WellTypedLM2_2Stmt lm22SelfMoveBody lm22PaddedEnv ⟨[], [2, 1, 0]⟩ 3
      (mkStmt22 (.assign ⟨2, []⟩
        (.aggregate (.adt "lm22::InnerU32" 0 .none) [.constant (lm22ConstU32 0xCAFE1234)])))
      (aggPostStaticEnv ⟨[], [2, 1, 0]⟩ 2 [.constant (lm22ConstU32 0xCAFE1234)]) 2 :=
    .assignAggregate _ 2 2 _ _ _
      (.mk lm22InnerU32Decl [lm22InnerU32Field0] [[.field 0 lm22U32Ty]] _ [] rfl
        (Or.inr ⟨"lm22::InnerU32", rfl⟩) rfl rfl lm22InnerU32_validStructLayout
        (by decide) rfl rfl (by decide)
        (.cons _ 0 0 1 _ [] trivial
          (.primLeaf (by decide) _ (lm22_constU32_wt 0xCAFE1234 (by decide) rfl)
            rfl lm22_u32_prim rfl rfl rfl rfl rfl rfl)
          (.nil _ 1)))
  have ⟨hs3, ha2, hm2⟩ := lm22_trace_step ⟨[2], [1, 0]⟩ (fuel := 6) hs2
    lm22SelfMove_phase rfl rfl hwt2 rfl rfl
  have hwt3 : WellTypedLM2_2Stmt lm22SelfMoveBody lm22PaddedEnv ⟨[2], [1, 0]⟩ 2
      (mkStmt22 (.assign ⟨1, []⟩
        (.aggregate (.adt "lm22::PaddedOuter" 0 .none)
          [.constant (constU8 7), .move ⟨2, []⟩])))
      (aggPostStaticEnv ⟨[2], [1, 0]⟩ 1 [.constant (constU8 7), .move ⟨2, []⟩]) 1 :=
    .assignAggregate _ 1 1 _ _ _
      (.mk lm22PaddedDecl lm22PaddedFields lm22PaddedPaths _ _ rfl
        (Or.inr ⟨"lm22::PaddedOuter", rfl⟩) rfl rfl lm22Padded_validStructLayout
        (by decide) rfl rfl (by decide)
        (.cons _ 0 0 1 _ _ trivial
          (.primLeaf (by decide) _ (lm22_constU8_wt 7 (by decide) rfl)
            rfl lm22_u8_prim rfl rfl rfl rfl rfl rfl)
          (.cons _ 1 1 2 (.move ⟨2, []⟩) [] (by decide : (2 : Nat) ≠ 1)
            (.scalarWrapSub (by decide) lm22InnerU32Ty lm22InnerU32Field0
              [.field 0 lm22U32Ty] _
              (.immStructLocal true 2 lm22InnerU32Decl [lm22InnerU32Field0]
                [[.field 0 lm22U32Ty]] rfl lm22InnerU32_isImmediateStructTy)
              lm22InnerU32_isImmediateStructTy rfl rfl rfl rfl rfl rfl rfl)
            (.nil _ 2))))
  have ⟨hs4, ha3, hm3⟩ := lm22_trace_step ⟨[1], [2, 0]⟩ (fuel := 5) hs3
    lm22SelfMove_phase rfl rfl hwt3 rfl rfl
  have hwt4 : WellTypedLM2_2Stmt lm22SelfMoveBody lm22PaddedEnv ⟨[1], [2, 0]⟩ 1
      (mkStmt22 (.assign ⟨1, []⟩ (.use (.move ⟨1, []⟩))))
      (useStructPostStaticEnv ⟨[1], [2, 0]⟩ 1 (.move ⟨1, []⟩)) 0 :=
    .assignSelfMoveMemStruct _ 0 1 _
      (.mk lm22PaddedDecl lm22PaddedFields lm22PaddedPaths _ _ rfl rfl
        (Or.inl (by decide)) rfl rfl (by decide) (by decide) rfl (by decide))
  have ⟨hs5, ha4, hm4⟩ := lm22_trace_step ⟨[1], [2, 0]⟩ (fuel := 4) hs4
    lm22SelfMove_phase rfl rfl hwt4 rfl rfl
  have hwt5 : WellTypedLM2_2Stmt lm22SelfMoveBody lm22PaddedEnv ⟨[1], [2, 0]⟩ 0
      (mkStmt22 (.assign ⟨0, []⟩
        (.use (.copy ⟨1, [.field 1 lm22InnerU32Ty, .field 0 lm22U32Ty]⟩))))
      (usePostStaticEnv ⟨[1], [2, 0]⟩ 0
        (.copy ⟨1, [.field 1 lm22InnerU32Ty, .field 0 lm22U32Ty]⟩)) 0 :=
    .assignUse _ 0 0 _ _
      (.mk lm22U32Decl rfl (by decide)
        (.projectedScalar false 1 [.field 1 lm22InnerU32Ty, .field 0 lm22U32Ty]
          lm22U32Ty rfl
          (.mk lm22PaddedDecl lm22PaddedFields lm22PaddedPaths 1 (by decide) (by decide)
            rfl rfl rfl rfl lm22_u32_prim lm22Padded_projChain_inner0)))
  have ⟨hs6, ha5, hm5⟩ := lm22_trace_step ⟨[0, 1], [0, 2, 0]⟩ (fuel := 3) hs5
    lm22SelfMove_phase rfl rfl hwt5 rfl rfl
  have ⟨hs7, ha6, hm6⟩ := lm22_trace_step ⟨[2, 0, 1], [2, 0, 2, 0]⟩ (fuel := 2) hs6
    lm22SelfMove_phase rfl rfl (.storageDead _ 0 2 lm22InnerU32Decl _ rfl (by decide)) rfl rfl
  have ⟨hs8, ha7, hm7⟩ := lm22_trace_step ⟨[1, 2, 0, 1], [1, 2, 0, 2, 0]⟩ (fuel := 1) hs7
    lm22SelfMove_phase rfl rfl (.storageDead _ 0 1 lm22PaddedDecl _ rfl (by decide)) rfl rfl
  have hpad5 :
      ∃ mp localAlloc,
        StructMemPlaceRel
          (lm22StepMiriN lm22SelfMoveBody 5 lm22SelfMoveMiriInit).machine
          lm22PaddedTy lm22PaddedLayoutTable lm22PaddedFields lm22PaddedPaths
          (.aggregate 0 [.scalar ⟨7, 1⟩, .aggregate 0 [.scalar ⟨0xCAFE1234, 4⟩]]) mp ∧
        (∃ allocId,
          (∃ tag, mp.ptr.provenance = some (.concrete allocId tag)) ∧
          (lm22StepMiriN lm22SelfMoveBody 5 lm22SelfMoveMiriInit).machine.memory.live.find?
            (fun (k, _) => k == allocId) = some (allocId, localAlloc)) ∧
        localAlloc.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 1) = .ok false ∧
        localAlloc.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 2) = .ok false ∧
        localAlloc.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 3) = .ok false := by
    obtain ⟨mp, _, _, _, _, hsmpr⟩ :=
      hs5.extract_structMemPlaceRel (idx := 1) (decl := lm22PaddedDecl) rfl rfl rfl rfl
    obtain ⟨allocId, localAlloc, hprov, hfind, hpad_fn, _⟩ :=
      hsmpr.has_uninit_of_padding_byte lm22Padded_interfield_padding_bytes.1
    exact ⟨mp, localAlloc, hsmpr, ⟨allocId, hprov, hfind⟩,
      hpad_fn 1 lm22Padded_interfield_padding_bytes.1,
      hpad_fn 2 lm22Padded_interfield_padding_bytes.2.1,
      hpad_fn 3 lm22Padded_interfield_padding_bytes.2.2⟩
  obtain ⟨ha_ret, hm_ret⟩ := lm22_return_agree_of_stateRelLM2_2 hs8 lm22SelfMove_phase
    rfl rfl rfl rfl rfl rfl rfl lm22_u32_prim (by decide) rfl
  have ha_tot :
      runAnnealBounded lm22SelfMoveBody 9 (initMachineState lm22SelfMoveBody []) =
        runAnnealBounded lm22SelfMoveBody 1
          (lm22StepAnnealN lm22SelfMoveBody 8 (initMachineState lm22SelfMoveBody [])) :=
    ha0.trans (ha1.trans (ha2.trans (ha3.trans (ha4.trans (ha5.trans (ha6.trans ha7))))))
  have hm_tot :
      runMiriBoundedLM2_2 lm22SelfMoveBody 9 lm22SelfMoveMiriInit =
        runMiriBoundedLM2_2 lm22SelfMoveBody 1 (lm22StepMiriN lm22SelfMoveBody 8 lm22SelfMoveMiriInit) :=
    hm0.trans (hm1.trans (hm2.trans (hm3.trans (hm4.trans (hm5.trans (hm6.trans hm7))))))
  rw [ha_tot, hm_tot]
  exact ⟨hpad5, ha_ret, hm_ret⟩

def lm22SelfCopyBody : CapturedMir where
  defPath := "lm_2_2_witness::self_copy_overlap_ub"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [lm22U32Decl, lm22UnpaddedDecl]
  basicBlocks := [
    { statements := [mkStmt22 (.assign ⟨1, []⟩ (.use (.copy ⟨1, []⟩)))],
      terminator := mkTerm22 .return_,
      isCleanup := false }]
  fnAbi := lm22FnAbiU32
  layouts := lm22UnpaddedLayoutTable
  allocations := []

def lm22SelfCopyAnnealInit : MachineState :=
  { (initMachineState lm22SelfCopyBody []) with
    frame :=
      { (initMachineState lm22SelfCopyBody []).frame with
        locals :=
          [ .uninit
          , .init (.aggregate 0 [.scalar ⟨10, 4⟩, .scalar ⟨20, 4⟩, .scalar ⟨30, 4⟩]) ] } }

def lm22SelfCopyMiriInit : AnnealStepState :=
  { stack := ⟨#[{
      body := translateBody lm22SelfCopyBody
      bodyIdentity := .ofCanonicalIndex 0
      functionInstance := { kind := .Item 0, args := #[] }
      extra := ()
      returnContinuation := .stop false
      returnPlace :=
        .frameLocal 0 0 none (translateTy lm22U32Ty lm22UnpaddedLayoutTable) (.ofAllocationToken 0)
      localsIdentity := .ofAllocationToken 0
      locals := #[
        { value := .live (.immediate .uninit), layout := none },
        { value := .live (.indirect (stackAllocPlace lm22AllocId1)),
          layout := some (translateTy lm22UnpaddedTy lm22UnpaddedLayoutTable) }]
      vaList := #[]
      trackCallerArg := none
      location := .mir ⟨0, 0⟩ }]⟩
    machine :=
      { AnnealMachine.empty with
        memory :=
          { AnnealMachine.empty.memory with
            nextAllocId := 2
            live := #[(lm22AllocId1, ⟨.stack, lm22SuperTripleInitAlloc⟩)] }
        addresses :=
          { AnnealMachine.empty.addresses with
            baseAddr := #[⟨lm22AllocId1, annealStackBaseAddr lm22AllocId1⟩] } } }

theorem lm22SuperTripleInitAlloc_selfCopy_err :
    ∃ alloc',
      lm22SuperTripleInitAlloc.copy
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO
          (translateTy lm22UnpaddedTy lm22UnpaddedLayoutTable).layout.size)
        Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8) true true
        lm22SuperTripleInitAlloc =
      .error .copyRangesOverlap alloc' := by
  have herr :
      (match lm22SuperTripleInitAlloc.copy
          (Miri.Memory.allocRange Miri.ABI.Size.ZERO
            (translateTy lm22UnpaddedTy lm22UnpaddedLayoutTable).layout.size)
          Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8) true true
          lm22SuperTripleInitAlloc with
        | .error .copyRangesOverlap _ => true
        | _ => false) = true := by
    dsimp [Miri.Memory.Allocation.copy, Miri.Memory.Allocation.copyRepeatedly]
    erw [lm22EmptyProv12_prepareCopy #[10, 0, 0, 0, 20, 0, 0, 0, 30, 0, 0, 0],
      lm22Lazy12_prepareCopy]
    with_unfolding_all rfl
  cases hc : lm22SuperTripleInitAlloc.copy
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO
        (translateTy lm22UnpaddedTy lm22UnpaddedLayoutTable).layout.size)
      Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8) true true
      lm22SuperTripleInitAlloc with
  | ok _ _ => rw [hc] at herr; cases herr
  | error e alloc' =>
    cases e <;> rw [hc] at herr <;> try cases herr
    exact ⟨alloc', rfl⟩

theorem lm22SelfCopyOverlap_ub :
    annealStructMemCopyOp lm22SelfCopyBody.localDecls lm22UnpaddedLayoutTable
      ⟨.indirect (stackAllocPlace lm22AllocId1),
        translateTy lm22UnpaddedTy lm22UnpaddedLayoutTable⟩
      ⟨.local 0 1 none (.ofAllocationToken 0),
        translateTy lm22UnpaddedTy lm22UnpaddedLayoutTable⟩
      lm22SelfCopyMiriInit =
    .error (.undefinedBehavior "whole-value copy between overlapping ranges")
      lm22SelfCopyMiriInit := by
  obtain ⟨alloc', herr⟩ := lm22SuperTripleInitAlloc_selfCopy_err
  exact annealStructMemCopyOp_overlap_ub
    (u := 0) (alloc' := alloc')
    rfl (by decide) rfl rfl rfl rfl
    ⟨rfl, 0, by decide, by rw [List.findIdx?_toArray]; rfl, rfl⟩
    (by decide) (by rw [List.findIdx?_toArray]; rfl) rfl herr

private theorem lm22SelfCopy_hsmpr :
    StructMemPlaceRel lm22SelfCopyMiriInit.machine
      lm22UnpaddedTy lm22UnpaddedLayoutTable
      lm22UnpaddedFields lm22UnpaddedPaths
      (.aggregate 0 [.scalar ⟨10, 4⟩, .scalar ⟨20, 4⟩, .scalar ⟨30, 4⟩])
      (stackAllocPlace lm22AllocId1) := by
  have hmask :
      InitMaskWordRel lm22SuperTripleInitAlloc.initializationMask
        (Miri.ABI.Size.ofBytes 12) (initWordsTrue (Miri.ABI.Size.ofBytes 12)) :=
    ⟨rfl, by simp [initWordsTrue], Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
  have hnz :
      NoZeroByteLeaves (.aggregate 0 [.scalar ⟨10, 4⟩, .scalar ⟨20, 4⟩, .scalar ⟨30, 4⟩]) := by
    change 0 < 4 ∧ (0 < 4 ∧ (0 < 4 ∧ True))
    decide
  refine .mk lm22AllocId1 Miri.Memory.BorTag.one (annealStackBaseAddr lm22AllocId1)
    ⟨.stack, lm22SuperTripleInitAlloc⟩ (initWordsTrue (Miri.ABI.Size.ofBytes 12))
    lm22Unpadded_validStructLayout rfl ⟨⟨_, _, rfl⟩, hnz⟩
    rfl rfl rfl rfl
    ⟨rfl, 0, by decide, by rw [List.findIdx?_toArray]; rfl, rfl⟩
    rfl rfl (by decide) rfl (by decide) rfl rfl rfl hmask
    (fun i hi b _ hhi => by
      have hb12 : b < (Miri.ABI.Size.ofBytes 12).bytes.toNat := by
        match i with
        | 0 => change b < 0 + 4 at hhi; change b < 12; omega
        | 1 => change b < 4 + 4 at hhi; change b < 12; omega
        | 2 => change b < 8 + 4 at hhi; change b < 12; omega
        | _ + 3 => simp [lm22UnpaddedFields] at hi; omega
      exact maskBlocksGetBit_initWordsTrue hb12)
    ?_
    (fun p hp => False.elim (lm22Unpadded_no_padding_bytes ⟨p, hp⟩))
  intro i hi
  have hlenA : (lm22AllocRaw lm22SuperTripleInitAlloc).size =
      lm22SuperTripleInitAlloc.byteSize.bytes.toNat := rfl
  match i with
  | 0 =>
    simp only [lm22UnpaddedFields, lm22UnpaddedPaths, List.getElem_cons_zero]
    have hsr : ScalarRel ⟨10, 4⟩ (Miri.Memory.ScalarInt.ofUInt32 10) :=
      ⟨Or.inr (Or.inr (Or.inl rfl)), by rw [scalarModulus_eq_two_pow]; decide, rfl, rfl⟩
    have hinit :
        lm22SuperTripleInitAlloc.initializationMask.isRangeInitialized
          (Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 4)) = .ok (.ok ()) :=
      initMaskWordRel_isRangeInitialized hmask (by decide) (by decide)
        (fun b _ hhi => maskBlocksGetBit_initWordsTrue (len := Miri.ABI.Size.ofBytes 12)
          (by change b < 0 + 4 at hhi; change b < 12; omega))
    exact ⟨nofun, trivial, lm22_u32_prim, .single _ 0 lm22U32Ty (.scalar ⟨10, 4⟩) rfl,
      ⟨10, 4⟩, Miri.Memory.ScalarInt.ofUInt32 10, rfl, hsr, rfl, nofun, nofun, hinit,
      alloc_readScalar_at_offset hsr hlenA (by decide) hinit (by decide)⟩
  | 1 =>
    simp only [lm22UnpaddedFields, lm22UnpaddedPaths, List.getElem_cons_succ, List.getElem_cons_zero]
    have hsr : ScalarRel ⟨20, 4⟩ (Miri.Memory.ScalarInt.ofUInt32 20) :=
      ⟨Or.inr (Or.inr (Or.inl rfl)), by rw [scalarModulus_eq_two_pow]; decide, rfl, rfl⟩
    have hinit :
        lm22SuperTripleInitAlloc.initializationMask.isRangeInitialized
          (Miri.Memory.allocRange (Miri.ABI.Size.ofBytes 4) (Miri.ABI.Size.ofBytes 4)) = .ok (.ok ()) :=
      initMaskWordRel_isRangeInitialized hmask (by decide) (by decide)
        (fun b _ hhi => maskBlocksGetBit_initWordsTrue (len := Miri.ABI.Size.ofBytes 12)
          (by change b < 4 + 4 at hhi; change b < 12; omega))
    exact ⟨nofun, trivial, lm22_u32_prim, .single _ 1 lm22U32Ty (.scalar ⟨20, 4⟩) rfl,
      ⟨20, 4⟩, Miri.Memory.ScalarInt.ofUInt32 20, rfl, hsr, rfl, nofun, nofun, hinit,
      alloc_readScalar_at_offset hsr hlenA (by decide) hinit (by decide)⟩
  | 2 =>
    simp only [lm22UnpaddedFields, lm22UnpaddedPaths, List.getElem_cons_succ, List.getElem_cons_zero]
    have hsr : ScalarRel ⟨30, 4⟩ (Miri.Memory.ScalarInt.ofUInt32 30) :=
      ⟨Or.inr (Or.inr (Or.inl rfl)), by rw [scalarModulus_eq_two_pow]; decide, rfl, rfl⟩
    have hinit :
        lm22SuperTripleInitAlloc.initializationMask.isRangeInitialized
          (Miri.Memory.allocRange (Miri.ABI.Size.ofBytes 8) (Miri.ABI.Size.ofBytes 4)) = .ok (.ok ()) :=
      initMaskWordRel_isRangeInitialized hmask (by decide) (by decide)
        (fun b _ hhi => maskBlocksGetBit_initWordsTrue (len := Miri.ABI.Size.ofBytes 12)
          (by change b < 8 + 4 at hhi; change b < 12; omega))
    exact ⟨nofun, trivial, lm22_u32_prim, .single _ 2 lm22U32Ty (.scalar ⟨30, 4⟩) rfl,
      ⟨30, 4⟩, Miri.Memory.ScalarInt.ofUInt32 30, rfl, hsr, rfl, nofun, nofun, hinit,
      alloc_readScalar_at_offset hsr hlenA (by decide) hinit (by decide)⟩
  | _ + 3 => simp [lm22UnpaddedFields] at hi; omega

theorem lm22SelfCopy_stateRel :
    StateRelLM2_2 lm22SelfCopyBody lm22UnpaddedEnv { initLocals := [1], immLocals := [0] } 0
      lm22SelfCopyAnnealInit lm22SelfCopyMiriInit := by
  refine .mk _ rfl rfl ⟨translateTy lm22U32Ty lm22UnpaddedLayoutTable, rfl⟩ ?_
    (fun j hj => by simp at hj; subst hj; nofun)
    (fun j hj _ _ h => by simp at hj; subst hj; cases h)
    (Or.inl rfl) rfl rfl rfl rfl rfl
    (by intro i j _ _ _ _ hne hi hj
        match i, j with
        | 1, 1 => exact False.elim (hne rfl)
        | 0, _ | _ + 2, _ => cases hi
        | _, 0 | _, _ + 2 => cases hj)
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro i decl slot mls hdecl hslot hmls
  match i with
  | 0 =>
    cases Option.some.inj hdecl; cases Option.some.inj hslot; cases Option.some.inj hmls
    exact .base .uninit _ rfl (.immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩))
  | 1 =>
    cases Option.some.inj hdecl; cases Option.some.inj hslot; cases Option.some.inj hmls
    exact .structInd lm22UnpaddedFields lm22UnpaddedPaths _
      (stackAllocPlace lm22AllocId1) _ rfl
      (fun l hl => by cases Option.mem_def.mp hl; rfl) lm22SelfCopy_hsmpr
  | _ + 2 => simp [lm22SelfCopyBody, get?] at hdecl

theorem lm22SelfCopy_divergence :
    stepMirFn lm22SelfCopyBody lm22SelfCopyAnnealInit =
      MirStepNode.step (advanceStmt lm22SelfCopyAnnealInit
        (lm22SelfCopyAnnealInit.frame.locals.set 1
          (.init (.aggregate 0 [.scalar ⟨10, 4⟩, .scalar ⟨20, 4⟩, .scalar ⟨30, 4⟩])))
        lm22SelfCopyAnnealInit.memory) ∧
    ∃ m_err,
      Miri.Interpreter.Step.step
          (annealStepHooksLM2_2 lm22SelfCopyBody.localDecls lm22SelfCopyBody.layouts) ()
          lm22SelfCopyMiriInit =
        (m_err, .error (.undefinedBehavior "whole-value copy between overlapping ranges")) :=
  step_assign_self_copy_memory_struct_divergence
    lm22SelfCopy_stateRel (fun _ h => by cases h)
    rfl rfl rfl rfl rfl rfl (by decide) rfl
    (fun allocId localAlloc hlive _ => by
      obtain ⟨_, u, hu_lt, _, hget⟩ := hlive
      have hu0 : u = 0 := Nat.lt_one_iff.mp hu_lt
      subst hu0
      injection hget with _ hla
      subst hla
      exact lm22SuperTripleInitAlloc_selfCopy_err)


end LeanMiriSpec.Correspondence.Witness
