/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import LeanMiriSpec.Correspondence.SimLM2_3
import LeanMiriSpec.Correspondence.Witness

/-!
# Non-Vacuity Witnesses for the `LM-2.3` Multi-Variant Enum Correspondence

The `LM-2.3` theorems would hold vacuously if `ValidEnumLayout`,
`StateRelLM2_3`, `EnumLocalByteUninit`, or `IsImmediateStepLocal` could not be
satisfied together across multi-step execution. This module constructs a
genuine 3-variant direct-tagged enum `enum Lm23Enum { V0, V1(u32),
V2(u32, u64) }` (16 bytes, 8-byte aligned, `u32` direct tag at `[0, 4)`, `V0`
fieldless, `V1` with `u32` at `[4, 8)`, and `V2` with `u32` at `[4, 8)` and
`u64` at `[8, 16)`) and proves concrete `rfl`-verified execution witnesses
exercising all five `LM-2.3` simulation theorems plus control-flow helpers and
`StateRel.toLM2_3`:

1. `wit_lm2_3_full_pipeline_trace`: an 8-step end-to-end execution starting
   from `StateRel.toLM2_3`:
   - `_1 = Lm23Enum::V1(42_u32)` (`evalRvalue_aggregate_enum_simulation` on
     `.uninit` `_1`, establishing `EnumLocalByteUninit` on `[8, 16)`);
   - `_2 = discriminant(_1)` (`evalRvalue_discriminant_simulation`, yielding
     `1_isize`);
   - `SwitchInt(copy _2, [0 => bb2, 1 => bb1, otherwise => bb2])`
     (`enum_match_switchInt_simulation`, taking arm `1 => bb1`);
   - `_3 = copy ((_1 as Some("V1") 1).0 : u32)`
     (`evalProjection_downcast_field_simulation` with `isMove = false`, reading
     `42_u32` while preserving `EnumLocalByteUninit` on `[8, 16)`);
   - `SetDiscriminant(_1, 0)` (`step_setDiscriminant_simulation`, mutating the
     tag in place to `0` while preserving `EnumLocalByteUninit` on `[4, 16)`);
   - `_1 = Lm23Enum::V2(copy _3, 99_u64)`
     (`evalRvalue_aggregate_enum_simulation` in-place overwrite on `.init` `_1`
     using both `copyLocal` and `constScalar`);
   - `_0 = move ((_1 as Some("V2") 2).1 : u64)`
     (`evalProjection_downcast_field_simulation` with `isMove = true`, reading
     `99_u64` at offset `8`);
   - `return` (`step_return_scalar_lm2_3_simulation`, returning `99_u64` in
     lockstep in both Anneal and `lean-miri`).
2. `wit_lm2_3_inactive_variant_downcast_ub`: after `_1 = Lm23Enum::V1(42_u32)`,
   reading inactive variant `V2`'s `u64` field `((_1 as 2).1)` at `[8, 16)`
   traps with undefined behavior in lockstep in both Anneal and `lean-miri`.
3. `wit_lm2_3_setDiscriminant_then_inactive_ub`: after
   `_1 = Lm23Enum::V1(42_u32); SetDiscriminant(_1, 0)`, reading `((_1 as 2).1)`
   at `[8, 16)` likewise traps with undefined behavior in lockstep in both
   machines.
4. `wit_lm2_3_switch_otherwise_and_goto_trace`: a 6-step trace constructing
   `Lm23Enum::V2(7_u32, 88_u64)`, reading `discriminant(_1) = 2_isize`,
   dispatching via `SwitchInt`'s `otherwise` fallback arm, stepping across
   `Goto`, projecting `V2.1 = 88_u64`, and returning `88_u64` in lockstep.
5. `wit_lm2_3_uninit_and_dead_ub`: lockstep undefined-behavior witnesses for
   `discriminant(_1)` on `.uninit`, `Lm23Enum::V0` aggregate assignment to
   `.dead` `_4`, `Downcast` + `Field` projection from `.dead` `_4`, and
   `SetDiscriminant(_4, 1)` on `.dead` `_4`.
6. `wit_lm2_3_setDiscriminant_uninit_divergence`: `SetDiscriminant(_1, 0)` on
   `.uninit` `_1` is UB in Anneal, but lean-miri writes the tag and steps.
7. `wit_lm2_3_inactive_variant_initialized_divergence`: after
   `_1 = Lm23Enum::V1(42_u32)`, projecting inactive variant `V2`'s first field
   `((_1 as 2).0 : u32)` at `[4, 8)` (which overlaps active `V1.0` at `[4, 8)`)
   is UB in Anneal (`stepMirFn = .fail .ub`), whereas `lean-miri` reads the
   initialized bytes `[4, 8)` without checking the discriminant tag and writes
   `42_u32` into `_3` (`evalProjection_downcast_field_initialized_divergence`).
8. `wit_lm2_3_prefix_setDiscriminant_read`: after
   `_1 = Lm23Enum::V2(42_u32, 99_u64)`, `SetDiscriminant(_1, 1)` mutates the
   tag in place to `1` (`V1`'s payload `[u32 @ 4]` is a non-empty strict prefix
   of `V2`'s payload `[u32 @ 4, u64 @ 8]`), and `_3 = copy ((_1 as 1).0 : u32)`
   reads `42_u32` in lockstep in both Anneal and `lean-miri`.
9. `wit_lm2_3_upcast_setDiscriminant_read_and_trailing_ub`: after
   `_1 = Lm23Enum::V1(42_u32)`, `SetDiscriminant(_1, 2)` mutates the tag in
   place from `1` (`V1`) to `2` (`V2`, a wider variant whose trailing field
   `V2.1 : u64` at `[8, 16)` is absent from `fieldVals` and uninitialized in
   memory), `_3 = copy ((_1 as 2).0 : u32)` reads the shared prefix field
   `42_u32` in lockstep, and `_0 = copy ((_1 as 2).1 : u64)` then traps with
   undefined behavior in lockstep in both Anneal and `lean-miri` on the
   uninitialized trailing field of the active variant.
10. `wit_lm2_3_bodyFree_divBody`: `BodyFreeOfLM2_3` and
    `step_LM2_3_eq_of_bodyFree` on `LM-1.1`'s `divBody`.
11. `wit_lm2_3_upcast_field_write_move_and_storage_lifecycle`: a 9-step
    end-to-end execution exercising `SetDiscriminant(_1, 2)` upcast, downcast
    field write `((_1 as 2).1) = 99_u64` (`fieldIdx = fieldVals.length`),
    `StorageLive(_4)`, `_4 = move _1`, `StorageDead(_1)`,
    `_0 = move ((_4 as 2).1)`, `StorageDead(_4)`, and `return 99_u64`.
12. `wit_lm2_3_copy_move_and_downcast_write_ub`: lockstep undefined-behavior
    witnesses for downcast field write on `.dead` `_4`, enum `copy` on `.dead`
    `_4`, and enum `move` on `.uninit` `_1`.
13. `wit_lm2_3_downcast_write_inactive_divergence`: writing
    `((_1 as 2).1 : u64) = 99_u64` on `_1 = Lm23Enum::V1(42_u32)` without
    `SetDiscriminant` fails with `.ub` in Anneal while stepping in `lean-miri`.
14. `wit_lm2_3_downcast_write_uninit_divergence`: writing
    `((_1 as 1).0 : u32) = 42_u32` on `.uninit` `_1` fails with `.ub` in Anneal
    while allocating and writing the field in `lean-miri`
    (`step_downcast_field_write_uninit_divergence`).
15. `wit_lm2_3_field_overwrite_self_move_and_copy_overwrite`: an 8-step trace
    exercising in-place active-field overwrite `((_1 as 1).0) = 77_u32`
    (`fieldIdx < fieldVals.length`), whole-enum self-move `_1 = move _1`
    (`step_enum_self_move_simulation`), `StorageLive(_4)`, `_4 = Lm23Enum::V0`,
    in-place indirect enum copy overwrite `_4 = copy _1`,
    `_3 = copy ((_4 as 1).0 : u32)` reading `77_u32`, and `StorageDead(_4)`.
16. `wit_lm2_3_self_copy_dead_and_uninit_ub`: lockstep undefined-behavior
    simulation for whole-enum self-copy `_1 = copy _1` on immediate `.uninit`
    `_1` and on `.dead` `_1` after `StorageDead(_1)`
    (`step_enum_self_copy_dead_or_uninit_simulation`).
17. `wit_lm2_3_self_copy_overlap_divergence`: after `_1 = Lm23Enum::V1(42_u32)`,
    whole-enum self-copy `_1 = copy _1` steps in Anneal while unconditionally
    failing with `"whole-value copy between overlapping ranges"` in `lean-miri`
    (`step_enum_self_copy_overlap_divergence`).
18. `wit_lm2_3_uninitInd_copy_and_move_divergence`: constructs concrete
    `StateRelLM2_3` states with `_1` in `LocalRelLM2_3.enumUninitInd`
    (`¬ IsImmediateStepLocal m 1`) and proves all four `(self vs. distinct) ×
    (copy vs. move)` quadrants (`_1 = copy _1`, `_1 = move _1`, `_4 = copy _1`,
    and `_4 = move _1`) fail `.ub` in Anneal while stepping `.ok true` in
    `lean-miri` (`step_enum_copy_move_uninitInd_divergence`).
19. `wit_lm2_3_return_enum_and_ub`: constructs an enum-returning MIR body
    `lm23ReturnEnumBody` (`_0 : Lm23Enum`) and proves:
    - `_0 = Lm23Enum::V2(42_u32, 99_u64); return` returns
      `.aggregate 2 [.scalar ⟨42, 4⟩, .scalar ⟨99, 8⟩]` in lockstep with
      `returnOperand = .ok (.indirect mp0)` and `EnumMemRel` on `mp0`
      (`step_return_enum_lm2_3_simulation`);
    - `return` on immediate `.uninit` `_0` and on `.dead` `_0` traps with
      undefined behavior in lockstep (`step_return_enum_lm2_3_simulation`);
    - `return` on indirect `.uninit` (`enumUninitInd`) `_0` fails `.ub` in
      Anneal while returning `.indirect mp0` and stepping `.ok true` in
      `lean-miri` (`step_return_enum_uninitInd_divergence`).
-/

namespace LeanMiriSpec.Correspondence.Witness

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open LeanMiriSpec.Correspondence

/-! ## 0. Outcome Inversion Helpers for `StepRelLM2_3` -/

theorem stepRelLM2_3_inv_step {body : CapturedMir} {env : EnumTypeEnv}
    {bud : Nat} {m : AnnealStepState} {s' : MachineState}
    {mRes : Miri.Interpreter.StepResult AnnealStepState Bool}
    (h : StepRelLM2_3 body env bud m (.step s') mRes) :
    ∃ m', mRes = (m', .ok true) ∧ StateRelLM2_3 body env bud s' m' := by
  generalize ha : MirStepNode.step s' = aRes at h
  cases h with
  | step s₁ m' hst =>
    injection ha with hr
    injection hr with hs
    subst hs
    exact ⟨m', rfl, hst⟩
  | emitStep obs s₁ m' hst =>
    cases obs with
    | silent =>
      dsimp [MirStepNode.emitStep, MirStepNode.step] at ha
      injection ha with hr
      injection hr with hs
      subst hs
      exact ⟨m', rfl, hst⟩
    | event _ => cases ha
  | retRoot _ _ _ _ _ _ _ _ _ => cases ha
  | ub _ _ => cases ha

theorem stepRelLM2_3_inv_event {body : CapturedMir} {env : EnumTypeEnv}
    {bud : Nat} {m : AnnealStepState} {tag : Nat} {s' : MachineState}
    {mRes : Miri.Interpreter.StepResult AnnealStepState Bool}
    (h : StepRelLM2_3 body env bud m (.emitStep (.event tag) s') mRes) :
    ∃ m', mRes = (m', .ok true) ∧ StateRelLM2_3 body env bud s' m' := by
  generalize ha : MirStepNode.emitStep (.event tag) s' = aRes at h
  cases h with
  | step _ _ _ => cases ha
  | emitStep obs s₁ m' hst =>
    cases obs with
    | silent => cases ha
    | event t =>
      dsimp [MirStepNode.emitStep] at ha
      injection ha with _ hk
      have hs : MirExecState.running s' = MirExecState.running s₁ :=
        congrFun hk PUnit.unit
      injection hs with hs'
      subst hs'
      exact ⟨m', rfl, hst⟩
  | retRoot _ _ _ _ _ _ _ _ _ => cases ha
  | ub _ _ => cases ha

theorem stepRelLM2_3_inv_retNormal {body : CapturedMir} {env : EnumTypeEnv}
    {bud : Nat} {m : AnnealStepState} {v : Value} {mem : Memory}
    {mRes : Miri.Interpreter.StepResult AnnealStepState Bool}
    (h : StepRelLM2_3 body env bud m (.retNormal v mem) mRes) :
    ∃ d0 imm0 m',
      mRes = (m', .ok true) ∧
      get? body.localDecls 0 = some d0 ∧
      annealControlHooks.returnOperand () m = (m, .ok (.immediate imm0)) ∧
      ImmediateRel d0.ty body.layouts v imm0 ∧
      m' = { m with stack := ⟨#[]⟩ } := by
  generalize ha : MirStepNode.retNormal v mem = aRes at h
  cases h with
  | step _ _ _ => cases ha
  | emitStep obs _ _ _ => cases obs <;> cases ha
  | retRoot d0 v₁ imm0 mem₁ m' hd0 hret himm hm' =>
    dsimp [MirStepNode.retNormal] at ha
    injection ha with hr
    injection hr with hp
    injection hp with hv _
    subst hv
    exact ⟨d0, imm0, m', rfl, hd0, hret, himm, hm'⟩
  | ub _ _ => cases ha

theorem stepRelLM2_3_inv_ub {body : CapturedMir} {env : EnumTypeEnv}
    {bud : Nat} {m : AnnealStepState}
    {mRes : Miri.Interpreter.StepResult AnnealStepState Bool}
    (h : StepRelLM2_3 body env bud m (.fail .ub) mRes) :
    ∃ m' msg, mRes = (m', .error (.undefinedBehavior msg)) := by
  generalize ha : MirStepNode.fail .ub = aRes at h
  cases h with
  | step _ _ _ => cases ha
  | emitStep obs _ _ _ => cases obs <;> cases ha
  | retRoot _ _ _ _ _ _ _ _ _ => cases ha
  | ub m' msg => exact ⟨m', msg, rfl⟩

/-! ## 1. Concrete 3-Variant Direct-Tagged Enum `Lm23Enum` -/

def lm23U32Ty : Ty := { kind := .uint .u32, layoutIdx := 0 }
def lm23U64Ty : Ty := { kind := .uint .u64, layoutIdx := 0 }
def lm23IsizeTy : Ty := { kind := .int .isize, layoutIdx := 0 }
def lm23EnumTy : Ty := { kind := .adt "Lm23Enum" [], layoutIdx := 1 }

def lm23Decl (t : Ty) : LocalDecl :=
  { mutability := .mut, ty := t, debugName := none }

def lm23U64Layout : TypeLayout :=
  { size := { bytes := 8 }, align := { bytes := 8 },
    backendRepr := .scalar
      (.initialized (.int 64 false) { start := 0, end_ := 18446744073709551615 }),
    fields := .primitive, variants := .single 0, isUninhabited := false }

def lm23RawTag : ScalarLayout :=
  .initialized (.int 32 false) { start := 0, end_ := 2 }

def lm23RawShapes : List FieldsShape :=
  [ .arbitrary [] []
  , .arbitrary [{ bytes := 4 }] [0]
  , .arbitrary [{ bytes := 4 }, { bytes := 8 }] [0, 1] ]

/-- `enum Lm23Enum { V0, V1(u32), V2(u32, u64) }`: 16 bytes, 8-byte aligned,
direct `u32` tag in `[0, 4)` (`tagBytes = 4`), `V0` fieldless, `V1` payload
`u32` at `[4, 8)`, and `V2` payload `(u32 @ 4, u64 @ 8)` in `[4, 16)`. -/
def lm23EnumLayout : TypeLayout :=
  { size := { bytes := 16 }, align := { bytes := 8 }, backendRepr := .memory,
    fields := .arbitrary [{ bytes := 0 }] [0],
    variants := .multiple lm23RawTag 0 lm23RawShapes,
    isUninhabited := false }

def lm23Layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true,
    entries := [lm23U64Layout, lm23EnumLayout] }

def lm23Variants : List (List StructFieldDesc) :=
  [ []
  , [ { offset := Miri.ABI.Size.ofBytes 4
        ty := lm23U32Ty
        fieldLayout := (translateTy lm23U32Ty lm23Layouts).layout } ]
  , [ { offset := Miri.ABI.Size.ofBytes 4
        ty := lm23U32Ty
        fieldLayout := (translateTy lm23U32Ty lm23Layouts).layout }
    , { offset := Miri.ABI.Size.ofBytes 8
        ty := lm23U64Ty
        fieldLayout := (translateTy lm23U64Ty lm23Layouts).layout } ] ]

def lm23Env : EnumTypeEnv
  | { kind := .adt "Lm23Enum" [], layoutIdx := 1 } => some (4, lm23Variants)
  | _ => none

theorem lm23_isPrim_u32 : IsPrimScalarTy lm23U32Ty :=
  Or.inr (Or.inr (Or.inr ⟨.u32, rfl⟩))

theorem lm23_isPrim_u64 : IsPrimScalarTy lm23U64Ty :=
  Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))

theorem lm23_isPrim_isize : IsPrimScalarTy lm23IsizeTy :=
  Or.inr (Or.inr (Or.inl ⟨.isize, rfl⟩))

theorem lm23_isDiscrDest_isize : IsEnumDiscrDestTy lm23IsizeTy :=
  Or.inr (Or.inr (Or.inl rfl))

theorem lm23_validEnumLayout :
    ValidEnumLayout lm23EnumTy lm23Layouts 4 lm23Variants where
  is_adt := ⟨"Lm23Enum", [], rfl⟩
  layoutIdx_lt := by decide
  multi_variant := by decide
  tagBytes_valid := Or.inr (Or.inr (Or.inl rfl))
  variants_fit_tag := by decide
  size_ge_tag := by decide
  size_lt_4gib := by decide
  align_pow2_le := by decide
  backend_memory := rfl
  uninhabited_false := rfl
  outer_fields_tag0 := rfl
  table_entry := by
    refine ⟨lm23EnumLayout,
      { start := BitVec.ofNat 128 0, «end» := BitVec.ofNat 128 2 },
      lm23RawTag, lm23RawShapes, rfl, rfl, rfl, rfl, ?_,
      (lm23RawShapes.map translateVariantFieldsShape).toArray, rfl, rfl, ?_⟩
    · intro v hv
      have hv' : v < 3 := hv
      match v with
      | 0 | 1 | 2 => decide
      | _ + 3 => omega
    · intro v hv
      have hv' : v < 3 := hv
      match v with
      | 0 =>
        refine ⟨rfl, rfl, rfl, (fun _ hi => by cases hi),
          (fun _ hi => by cases hi), (fun _ hi => by cases hi),
          (fun _ _ hi _ _ => by cases hi)⟩
      | 1 =>
        refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
        · intro i hi
          have hi' : i < 1 := hi
          match i with
          | 0 => exact ⟨lm23_isPrim_u32, rfl⟩
          | _ + 1 => omega
        · intro i hi
          have hi' : i < 1 := hi
          match i with
          | 0 => decide +revert
          | _ + 1 => omega
        · intro i hi
          have hi' : i < 1 := hi
          match i with
          | 0 => decide +revert
          | _ + 1 => omega
        · intro i j hi hj hne
          have hi' : i < 1 := hi
          have hj' : j < 1 := hj
          omega
      | 2 =>
        refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
        · intro i hi
          have hi' : i < 2 := hi
          match i with
          | 0 => exact ⟨lm23_isPrim_u32, rfl⟩
          | 1 => exact ⟨lm23_isPrim_u64, rfl⟩
          | _ + 2 => omega
        · intro i hi
          have hi' : i < 2 := hi
          match i with
          | 0 | 1 => decide +revert
          | _ + 2 => omega
        · intro i hi
          have hi' : i < 2 := hi
          match i with
          | 0 | 1 => decide +revert
          | _ + 2 => omega
        · intro i j hi hj hne
          have hi' : i < 2 := hi
          have hj' : j < 2 := hj
          match i, j with
          | 0, 0 | 1, 1 => exact absurd rfl hne
          | 0, 1 => left; decide +revert
          | 1, 0 => right; decide +revert
          | _ + 2, _ => omega
          | _, _ + 2 => omega
      | _ + 3 => omega

theorem lm23_env_valid :
    ∀ ty tb vs, lm23Env ty = some (tb, vs) →
      ValidEnumLayout ty lm23Layouts tb vs := by
  intro ty tb vs h
  unfold lm23Env at h
  split at h
  · injection h with hp
    rcases hp with ⟨rfl, rfl⟩
    exact lm23_validEnumLayout
  · cases h

/-! ## 2. Concrete MIR Body and Initial States -/

def lm23ConstU32 (n : Nat) : ConstOperand :=
  { ty := lm23U32Ty, val := .scalar (.int ⟨n, 4⟩) }

def lm23ConstU64 (n : Nat) : ConstOperand :=
  { ty := lm23U64Ty, val := .scalar (.int ⟨n, 8⟩) }

def lm23Stmt (k : StatementKind) : MirAst.Statement :=
  { kind := k, span := "lm-2.3-witness" }

def lm23Term (k : TerminatorKind) : MirAst.Terminator :=
  { kind := k, span := "lm-2.3-witness" }

def lm23AggV0Stmt (dst : Local) : MirAst.Statement :=
  lm23Stmt (.assign (local_ dst) (.aggregate (.adt "Lm23Enum" 0 none) []))

def lm23AggV1Stmt (dst : Local) (n : Nat) : MirAst.Statement :=
  lm23Stmt (.assign (local_ dst)
    (.aggregate (.adt "Lm23Enum" 1 none) [.constant (lm23ConstU32 n)]))

def lm23AggV2CopyStmt (dst srcU32 : Local) (n64 : Nat) : MirAst.Statement :=
  lm23Stmt (.assign (local_ dst)
    (.aggregate (.adt "Lm23Enum" 2 none)
      [.copy (local_ srcU32), .constant (lm23ConstU64 n64)]))

def lm23AggV2ConstStmt (dst : Local) (n32 n64 : Nat) : MirAst.Statement :=
  lm23Stmt (.assign (local_ dst)
    (.aggregate (.adt "Lm23Enum" 2 none)
      [.constant (lm23ConstU32 n32), .constant (lm23ConstU64 n64)]))

def lm23DiscrStmt (dst src : Local) : MirAst.Statement :=
  lm23Stmt (.assign (local_ dst) (.discriminant (local_ src)))

def lm23SetDiscrStmt (dst : Local) (v : Nat) : MirAst.Statement :=
  lm23Stmt (.setDiscriminant (local_ dst) v)

def lm23DowncastReadStmt (isMove : Bool) (dst src : Local)
    (vName : Option String) (v f : Nat) (fty : Ty) : MirAst.Statement :=
  lm23Stmt (.assign (local_ dst)
    (.use (if isMove then
      .move ⟨src, [.downcast vName v, .field f fty]⟩
    else
      .copy ⟨src, [.downcast vName v, .field f fty]⟩)))

def lm23DowncastWriteConstU32Stmt (dst : Local) (vName : Option String)
    (v f n32 : Nat) : MirAst.Statement :=
  lm23Stmt (.assign ⟨dst, [.downcast vName v, .field f lm23U32Ty]⟩
    (.use (.constant (lm23ConstU32 n32))))

def lm23DowncastWriteConstU64Stmt (dst : Local) (vName : Option String)
    (v f n64 : Nat) : MirAst.Statement :=
  lm23Stmt (.assign ⟨dst, [.downcast vName v, .field f lm23U64Ty]⟩
    (.use (.constant (lm23ConstU64 n64))))

def lm23StorageLiveStmt (loc : Local) : MirAst.Statement :=
  lm23Stmt (.storageLive loc)

def lm23StorageDeadStmt (loc : Local) : MirAst.Statement :=
  lm23Stmt (.storageDead loc)

def lm23EnumCopyMoveStmt (isMove : Bool) (dst src : Local) : MirAst.Statement :=
  lm23Stmt (.assign (local_ dst)
    (.use (if isMove then .move (local_ src) else .copy (local_ src))))

def lm23SwitchTargets1 : SwitchTargets :=
  { branches := [(0, 2), (1, 1)], otherwise := 2 }

def lm23SwitchTargetsOtherwise : SwitchTargets :=
  { branches := [(0, 2), (1, 1)], otherwise := 5 }

def lm23FnAbi : FnAbi :=
  { args := [], ret := { layout := lm23U64Layout, mode := .direct },
    conv := .rust, canUnwind := false }

/-- Locals: `_0: u64`, `_1: Lm23Enum`, `_2: isize`, `_3: u32`, `_4: Lm23Enum`
(`_4` starts `.dead` to exercise dead-local enum UB paths).
- `bb0`..`bb1`: full 8-step `V1 -> discriminant -> SwitchInt -> Downcast ->
  SetDiscriminant(0) -> V2(copy _3, 99) -> move Downcast -> Return` pipeline;
- `bb2`: `_1 = V1(42); _0 = copy ((_1 as 2).1 : u64)` inactive-variant UB;
- `bb3`: `_1 = V1(42); SetDiscriminant(_1, 0); _0 = copy ((_1 as 2).1 : u64)`
  inactive-variant UB after `SetDiscriminant`;
- `bb4`..`bb6`: `V2(7, 88) -> discriminant -> SwitchInt(otherwise => bb5) ->
  Goto(bb6) -> copy ((_1 as 2).1) -> Return`;
- `bb7`, `bb9`..`bb11`: `.uninit` `discriminant`, `.dead` `Aggregate`, `.dead`
  `Downcast` + `Field`, and `.dead` `SetDiscriminant` lockstep UB blocks;
- `bb8`: `SetDiscriminant` on `.uninit` `_1`, where Anneal reports UB but
  lean-miri writes the tag. -/
def lm23Body : CapturedMir where
  defPath := "lm_2_3_witness::enums"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls :=
    [ lm23Decl lm23U64Ty
    , lm23Decl lm23EnumTy
    , lm23Decl lm23IsizeTy
    , lm23Decl lm23U32Ty
    , lm23Decl lm23EnumTy ]
  basicBlocks :=
    [ -- bb0: construct V1(42), read discriminant, SwitchInt to bb1
      { statements := [lm23AggV1Stmt 1 42, lm23DiscrStmt 2 1]
        terminator := lm23Term (.switchInt (.copy (local_ 2)) lm23SwitchTargets1)
        isCleanup := false }
    , -- bb1: downcast V1.0, SetDiscriminant(0), overwrite V2(copy _3, 99),
      --      move downcast V2.1 into _0, return
      { statements :=
          [ lm23DowncastReadStmt false 3 1 (some "V1") 1 0 lm23U32Ty
          , lm23SetDiscrStmt 1 0
          , lm23AggV2CopyStmt 1 3 99
          , lm23DowncastReadStmt true 0 1 (some "V2") 2 1 lm23U64Ty ]
        terminator := lm23Term .return_
        isCleanup := false }
    , -- bb2: construct V1(42), then read inactive V2.1 ([8, 16) uninit -> UB)
      { statements :=
          [ lm23AggV1Stmt 1 42
          , lm23DowncastReadStmt false 0 1 (some "V2") 2 1 lm23U64Ty ]
        terminator := lm23Term .return_
        isCleanup := false }
    , -- bb3: V1(42), SetDiscriminant(0), then read inactive V2.1 -> UB
      { statements :=
          [ lm23AggV1Stmt 1 42
          , lm23SetDiscrStmt 1 0
          , lm23DowncastReadStmt false 0 1 (some "V2") 2 1 lm23U64Ty ]
        terminator := lm23Term .return_
        isCleanup := false }
    , -- bb4: V2(7, 88), read discriminant = 2, SwitchInt otherwise -> bb5
      { statements := [lm23AggV2ConstStmt 1 7 88, lm23DiscrStmt 2 1]
        terminator :=
          lm23Term (.switchInt (.copy (local_ 2)) lm23SwitchTargetsOtherwise)
        isCleanup := false }
    , -- bb5: Goto -> bb6
      { statements := []
        terminator := lm23Term (.goto 6)
        isCleanup := false }
    , -- bb6: read V2.1 = 88 into _0 and return
      { statements :=
          [ lm23DowncastReadStmt false 0 1 (some "V2") 2 1 lm23U64Ty ]
        terminator := lm23Term .return_
        isCleanup := false }
    , -- bb7: discriminant(_1) on uninit _1 -> UB
      { statements := [lm23DiscrStmt 2 1]
        terminator := lm23Term .return_
        isCleanup := false }
    , -- bb8: SetDiscriminant(_1, 0) on uninit _1: Anneal UB, lean-miri steps
      { statements := [lm23SetDiscrStmt 1 0]
        terminator := lm23Term .return_
        isCleanup := false }
    , -- bb9: _4 = V0 on dead _4 -> UB
      { statements := [lm23AggV0Stmt 4]
        terminator := lm23Term .return_
        isCleanup := false }
    , -- bb10: _3 = copy ((_4 as 1).0) on dead _4 -> UB
      { statements :=
          [ lm23DowncastReadStmt false 3 4 (some "V1") 1 0 lm23U32Ty ]
        terminator := lm23Term .return_
        isCleanup := false }
    , -- bb11: SetDiscriminant(_4, 1) on dead _4 -> UB
      { statements := [lm23SetDiscrStmt 4 1]
        terminator := lm23Term .return_
        isCleanup := false }
    , -- bb12: _1 = V1(42), _3 = copy ((_1 as 2).0): Anneal UB, lean-miri ok
      { statements :=
          [ lm23AggV1Stmt 1 42
          , lm23DowncastReadStmt false 3 1 (some "V2") 2 0 lm23U32Ty ]
        terminator := lm23Term .return_
        isCleanup := false }
    , -- bb13: _1 = V2(42, 99), SetDiscriminant(_1, 1), _3 = copy ((_1 as 1).0)
      { statements :=
          [ lm23AggV2ConstStmt 1 42 99
          , lm23SetDiscrStmt 1 1
          , lm23DowncastReadStmt false 3 1 (some "V1") 1 0 lm23U32Ty ]
        terminator := lm23Term .return_
        isCleanup := false }
    , -- bb14: _1 = V1(42), SetDiscriminant(_1, 2) (V1 -> V2 upcast),
      --       _3 = copy ((_1 as 2).0 : u32), _0 = copy ((_1 as 2).1) -> UB
      { statements :=
          [ lm23AggV1Stmt 1 42
          , lm23SetDiscrStmt 1 2
          , lm23DowncastReadStmt false 3 1 (some "V2") 2 0 lm23U32Ty
          , lm23DowncastReadStmt false 0 1 (some "V2") 2 1 lm23U64Ty ]
        terminator := lm23Term .return_
        isCleanup := false }
    , -- bb15: V1(42) -> SetDiscriminant(2) -> ((_1 as 2).1) = 99 ->
      --       StorageLive(_4) -> _4 = move _1 -> StorageDead(_1) ->
      --       _0 = move ((_4 as 2).1) -> StorageDead(_4) -> return 99
      { statements :=
          [ lm23AggV1Stmt 1 42
          , lm23SetDiscrStmt 1 2
          , lm23DowncastWriteConstU64Stmt 1 (some "V2") 2 1 99
          , lm23StorageLiveStmt 4
          , lm23EnumCopyMoveStmt true 4 1
          , lm23StorageDeadStmt 1
          , lm23DowncastReadStmt true 0 4 (some "V2") 2 1 lm23U64Ty
          , lm23StorageDeadStmt 4 ]
        terminator := lm23Term .return_
        isCleanup := false }
    , -- bb16: ((_4 as 1).0 : u32) = 7 on dead _4 -> UB
      { statements := [lm23DowncastWriteConstU32Stmt 4 (some "V1") 1 0 7]
        terminator := lm23Term .return_
        isCleanup := false }
    , -- bb17: _1 = copy _4 on dead _4 -> UB
      { statements := [lm23EnumCopyMoveStmt false 1 4]
        terminator := lm23Term .return_
        isCleanup := false }
    , -- bb18: StorageLive(_4); _4 = move _1 on uninit _1 -> UB
      { statements :=
          [ lm23StorageLiveStmt 4
          , lm23EnumCopyMoveStmt true 4 1 ]
        terminator := lm23Term .return_
        isCleanup := false }
    , -- bb19: _1 = V1(42); ((_1 as 2).1 : u64) = 99 (inactive write divergence)
      { statements :=
          [ lm23AggV1Stmt 1 42
          , lm23DowncastWriteConstU64Stmt 1 (some "V2") 2 1 99 ]
        terminator := lm23Term .return_
        isCleanup := false }
    , -- bb20: ((_1 as 1).0 : u32) = 42 on uninit _1 (uninit write divergence)
      { statements :=
          [ lm23DowncastWriteConstU32Stmt 1 (some "V1") 1 0 42 ]
        terminator := lm23Term .return_
        isCleanup := false }
    , -- bb21: V1(42) -> overwrite ((_1 as 1).0) = 77 -> self-move _1 = move _1
      --       -> StorageLive(_4) -> _4 = V0 -> in-place _4 = copy _1 ->
      --       _3 = copy ((_4 as 1).0) -> StorageDead(_4)
      { statements :=
          [ lm23AggV1Stmt 1 42
          , lm23DowncastWriteConstU32Stmt 1 (some "V1") 1 0 77
          , lm23EnumCopyMoveStmt true 1 1
          , lm23StorageLiveStmt 4
          , lm23AggV0Stmt 4
          , lm23EnumCopyMoveStmt false 4 1
          , lm23DowncastReadStmt false 3 4 (some "V1") 1 0 lm23U32Ty
          , lm23StorageDeadStmt 4 ]
        terminator := lm23Term .return_
        isCleanup := false }
    , -- bb22: _1 = copy _1 on uninit _1 (UB if immediate; divergence if
      --       indirect enumUninitInd)
      { statements := [lm23EnumCopyMoveStmt false 1 1]
        terminator := lm23Term .return_
        isCleanup := false }
    , -- bb23: StorageDead(_1); _1 = copy _1 on dead _1 -> lockstep UB
      { statements :=
          [ lm23StorageDeadStmt 1
          , lm23EnumCopyMoveStmt false 1 1 ]
        terminator := lm23Term .return_
        isCleanup := false }
    , -- bb24: _1 = V1(42); _1 = copy _1 (overlapping self-copy divergence)
      { statements :=
          [ lm23AggV1Stmt 1 42
          , lm23EnumCopyMoveStmt false 1 1 ]
        terminator := lm23Term .return_
        isCleanup := false }
    , -- bb25: StorageLive(_4); _4 = copy _1 (distinct-local enumUninitInd copy
      --       divergence)
      { statements :=
          [ lm23StorageLiveStmt 4
          , lm23EnumCopyMoveStmt false 4 1 ]
        terminator := lm23Term .return_
        isCleanup := false }
    , -- bb26: _1 = move _1 on uninit _1 (self-move enumUninitInd divergence)
      { statements := [lm23EnumCopyMoveStmt true 1 1]
        terminator := lm23Term .return_
        isCleanup := false } ]
  fnAbi := lm23FnAbi
  layouts := lm23Layouts
  allocations := []

theorem lm23_phase : ∀ p, lm23Body.phase ≠ .other p := by
  intro p h; cases h

/-- Initial Anneal state at the start of block `b` (`_0.._3` uninitialized,
`_4` dead). -/
def lm23InitAnneal (b : Nat) : MachineState :=
  { frame := { blockIdx := b, stmtIdx := 0,
               locals := [.uninit, .uninit, .uninit, .uninit, .dead] }
    memory := (initMachineState lm23Body []).memory }

def lm23InitMiriFrame (b : Nat) :
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { body := translateBody lm23Body
    bodyIdentity := .ofCanonicalIndex 0
    functionInstance := { kind := .Item 0, args := #[] }
    extra := ()
    returnContinuation := .stop false
    returnPlace :=
      .frameLocal 0 0 none (translateTy lm23U64Ty lm23Layouts)
        (.ofAllocationToken 0)
    localsIdentity := .ofAllocationToken 0
    locals := #[
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate .uninit), layout := none },
      { value := .dead, layout := none }]
    vaList := #[]
    trackCallerArg := none
    location := .mir ⟨b, 0⟩ }

def lm23InitMiri (b : Nat) : AnnealStepState :=
  { stack := ⟨#[lm23InitMiriFrame b]⟩, machine := AnnealMachine.empty }

theorem lm23_init_stateRel (b : Nat) :
    StateRel lm23Body (lm23InitAnneal b) (lm23InitMiri b) := by
  refine StateRel.mk (lm23InitMiriFrame b) rfl rfl
    ⟨translateTy lm23U64Ty lm23Layouts, rfl⟩ ?_ rfl rfl rfl rfl rfl
    (by
      intro i _ _ _ _ _ _ hi _
      revert hi
      match i with
      | 0 | 1 | 2 | 3 | 4 => rintro ⟨⟩
      | _ + 5 => rintro ⟨⟩)
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro i decl slot mls hdecl hslot hmls
  match i with
  | 0 | 1 | 2 | 3 =>
    have hs : slot = .uninit := by simpa [lm23InitAnneal, get?] using hslot.symm
    have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
      simpa [lm23InitMiriFrame] using hmls.symm
    subst hs hm
    exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
  | 4 =>
    have hs : slot = .dead := by simpa [lm23InitAnneal, get?] using hslot.symm
    have hm : mls = { value := .dead, layout := none } := by
      simpa [lm23InitMiriFrame] using hmls.symm
    subst hs hm
    exact .dead none (fun _ h => nomatch h)
  | _ + 5 =>
    simp [lm23Body, get?] at hdecl

theorem lm23_init_stateRelLM2_3 (b budget : Nat) (hbud : 1 + budget < 2 ^ 32) :
    StateRelLM2_3 lm23Body lm23Env budget (lm23InitAnneal b) (lm23InitMiri b) := by
  refine (lm23_init_stateRel b).toLM2_3 lm23_env_valid ?_
    (Or.inr (AllocIdWatermark.empty budget hbud))
  intro idx decl slot mls hdecl _ hslot tf hframes hmls
  have htf : lm23InitMiriFrame b = tf := by simpa [lm23InitMiri] using hframes
  subst htf
  match idx with
  | 0 | 1 | 2 | 3 =>
    right
    refine ⟨by simpa [lm23InitAnneal, get?] using hslot.symm, ?_⟩
    have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
      simpa [lm23InitMiriFrame] using hmls.symm
    subst hm; rfl
  | 4 =>
    left
    simpa [lm23InitAnneal, get?] using hslot.symm
  | _ + 5 =>
    simp [lm23Body, get?] at hdecl

theorem lm23_init_imm (b j : Nat) :
    IsImmediateStepLocal (lm23InitMiri b) j := by
  intro tf hframes mls hmls mp hv
  have htf : lm23InitMiriFrame b = tf := by simpa [lm23InitMiri] using hframes
  subst htf
  match j with
  | 0 | 1 | 2 | 3 | 4 => simp [lm23InitMiriFrame] at hmls; subst hmls; cases hv
  | _ + 5 => simp [lm23InitMiriFrame] at hmls

theorem lm23_constU32_wt (n : Nat) (hn : n < 2 ^ 32)
    (tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit) :
    WellTypedEnumScalarOp lm23Body tf (.constant (lm23ConstU32 n)) lm23U32Ty :=
  .constScalar (lm23ConstU32 n) ⟨n, 4⟩ rfl lm23_isPrim_u32
    (Or.inr (Or.inr (Or.inl rfl)))
    (by rw [scalarModulus_eq_two_pow]; simpa using hn)
    rfl (fun h => nomatch h) (fun h => nomatch h)

theorem lm23_constU64_wt (n : Nat) (hn : n < 2 ^ 64)
    (tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit) :
    WellTypedEnumScalarOp lm23Body tf (.constant (lm23ConstU64 n)) lm23U64Ty :=
  .constScalar (lm23ConstU64 n) ⟨n, 8⟩ rfl lm23_isPrim_u64
    (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    (by rw [scalarModulus_eq_two_pow]; simpa using hn)
    rfl (fun h => nomatch h) (fun h => nomatch h)

theorem lm23_switchCases1_fit :
    SwitchCasesFit lm23IsizeTy lm23SwitchTargets1 := by
  intro v b hmem
  simp only [lm23SwitchTargets1, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    exact ⟨by decide, fun h => nomatch h⟩

theorem lm23_switchCasesOtherwise_fit :
    SwitchCasesFit lm23IsizeTy lm23SwitchTargetsOtherwise := by
  intro v b hmem
  simp only [lm23SwitchTargetsOtherwise, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    exact ⟨by decide, fun h => nomatch h⟩

abbrev lm23Hooks := annealStepHooksLM2_3 lm23Body.localDecls lm23Body.layouts

/-! ## 3. Witness 1: Full 8-Step Multi-Variant Enum Pipeline (`bb0 -> bb1`) -/

def lm23PipeS1 : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 1,
               locals := [.uninit, .init (.aggregate 1 [.scalar ⟨42, 4⟩]),
                          .uninit, .uninit, .dead] }
    memory := (initMachineState lm23Body []).memory }

def lm23PipeS2 : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 2,
               locals := [.uninit, .init (.aggregate 1 [.scalar ⟨42, 4⟩]),
                          .init (.scalar ⟨1, 8⟩), .uninit, .dead] }
    memory := (initMachineState lm23Body []).memory }

def lm23PipeS3 : MachineState :=
  { frame := { blockIdx := 1, stmtIdx := 0,
               locals := [.uninit, .init (.aggregate 1 [.scalar ⟨42, 4⟩]),
                          .init (.scalar ⟨1, 8⟩), .uninit, .dead] }
    memory := (initMachineState lm23Body []).memory }

def lm23PipeS4 : MachineState :=
  { frame := { blockIdx := 1, stmtIdx := 1,
               locals := [.uninit, .init (.aggregate 1 [.scalar ⟨42, 4⟩]),
                          .init (.scalar ⟨1, 8⟩), .init (.scalar ⟨42, 4⟩), .dead] }
    memory := (initMachineState lm23Body []).memory }

def lm23PipeS5 : MachineState :=
  { frame := { blockIdx := 1, stmtIdx := 2,
               locals := [.uninit, .init (.aggregate 0 [.scalar ⟨42, 4⟩]),
                          .init (.scalar ⟨1, 8⟩), .init (.scalar ⟨42, 4⟩), .dead] }
    memory := (initMachineState lm23Body []).memory }

def lm23PipeS6 : MachineState :=
  { frame := { blockIdx := 1, stmtIdx := 3,
               locals := [.uninit,
                          .init (.aggregate 2 [.scalar ⟨42, 4⟩, .scalar ⟨99, 8⟩]),
                          .init (.scalar ⟨1, 8⟩), .init (.scalar ⟨42, 4⟩), .dead] }
    memory := (initMachineState lm23Body []).memory }

def lm23PipeS7 : MachineState :=
  { frame := { blockIdx := 1, stmtIdx := 4,
               locals := [.init (.scalar ⟨99, 8⟩),
                          .init (.aggregate 2 [.scalar ⟨42, 4⟩, .scalar ⟨99, 8⟩]),
                          .init (.scalar ⟨1, 8⟩), .init (.scalar ⟨42, 4⟩), .dead] }
    memory := (initMachineState lm23Body []).memory }

theorem lm23_pipe_a1 : stepMirFn lm23Body (lm23InitAnneal 0) = .step lm23PipeS1 := rfl
theorem lm23_pipe_a2 : stepMirFn lm23Body lm23PipeS1 = .step lm23PipeS2 := rfl
theorem lm23_pipe_a3 :
    stepMirFn lm23Body lm23PipeS2 = .emitStep (.event 1) lm23PipeS3 := rfl
theorem lm23_pipe_a4 : stepMirFn lm23Body lm23PipeS3 = .step lm23PipeS4 := rfl
theorem lm23_pipe_a5 : stepMirFn lm23Body lm23PipeS4 = .step lm23PipeS5 := rfl
theorem lm23_pipe_a6 : stepMirFn lm23Body lm23PipeS5 = .step lm23PipeS6 := rfl
theorem lm23_pipe_a7 : stepMirFn lm23Body lm23PipeS6 = .step lm23PipeS7 := rfl
theorem lm23_pipe_a8 :
    stepMirFn lm23Body lm23PipeS7 =
      .retNormal (.scalar ⟨99, 8⟩) (initMachineState lm23Body []).memory := rfl

/-- Helper chaining Step 1 (`_1 = Lm23Enum::V1(42_u32)`) from `lm23InitAnneal b`
on any block whose `stmt 0` is `lm23AggV1Stmt 1 42`, establishing
`StateRelLM2_3`, `EnumLocalByteUninit m₁ 1 8` (byte `8` in inactive `V2.1`),
and immediacy of `_0`, `_2`, `_3`. -/
theorem lm23_step_agg_v1_at {b budget : Nat} (hbud : 1 + (budget + 1) < 2 ^ 32)
    {bb : BasicBlockData}
    (hbb : get? lm23Body.basicBlocks b = some bb)
    (hstmt0 : get? bb.statements 0 = some (lm23AggV1Stmt 1 42))
    {s₁ : MachineState}
    (ha₁ : stepMirFn lm23Body (lm23InitAnneal b) = .step s₁) :
    ∃ m₁ : AnnealStepState,
      Miri.Interpreter.Step.step lm23Hooks () (lm23InitMiri b) = (m₁, .ok true) ∧
      StateRelLM2_3 lm23Body lm23Env budget s₁ m₁ ∧
      EnumLocalByteUninit m₁ 1 8 ∧
      (∀ j, j ≠ 1 → IsImmediateStepLocal m₁ j) := by
  have hsim := evalRvalue_aggregate_enum_simulation
    (lm23_init_stateRelLM2_3 b (budget + 1) hbud) lm23_env_valid lm23_phase
    hbb hstmt0 rfl (dstDecl := lm23Decl lm23EnumTy) rfl
    (tagBytes := 4) (variants := lm23Variants) rfl (by decide) rfl
    (fun tf i hi _ => by
      have hi' : i < 1 := hi
      match i with
      | 0 => exact lm23_constU32_wt 42 (by decide) tf
      | _ + 1 => omega)
  dsimp only at hsim
  rcases hsim with ⟨hrel₁, hpost₁⟩
  rw [ha₁] at hrel₁
  obtain ⟨m₁, hm₁, hst₁⟩ := stepRelLM2_3_inv_step hrel₁
  have hno₁ : ∀ msg, (Miri.Interpreter.Step.step lm23Hooks () (lm23InitMiri b)).2 ≠
      .error (.undefinedBehavior msg) := by
    rw [hm₁]; intro _ h; cases h
  obtain ⟨huninit₁, _, himm₁⟩ := hpost₁ hno₁
  have hu8 : EnumLocalByteUninit m₁ 1 8 := by
    have hu := huninit₁ rfl 8 (by decide) (by decide) (fun j hj => by
      have hj' : j < 1 := hj
      match j with
      | 0 => right; decide +revert
      | _ + 1 => omega)
    simpa [hm₁] using hu
  refine ⟨m₁, hm₁, hst₁, hu8, fun j hj => ?_⟩
  have hij := himm₁ j hj (lm23_init_imm b j)
  simpa [hm₁] using hij

/-- **Witness 1 (`wit_lm2_3_full_pipeline_trace`)**:
End-to-end 8-step lockstep execution of multi-variant enum construction (`V1`),
`Rvalue.Discriminant`, `Terminator.SwitchInt` branch dispatch, `Downcast` +
`Field` active-variant read, `SetDiscriminant(0)` in-place tag mutation,
in-place multi-field `V2(copy _3, 99_u64)` overwrite, `move` `Downcast` +
`Field` read at offset `8`, and root scalar `Return` (`99_u64`). -/
theorem wit_lm2_3_full_pipeline_trace :
    ∃ (m₁ m₂ m₃ m₄ m₅ m₆ m₇ m₈ : AnnealStepState)
      (imm0 : Miri.Interpreter.Immediate AnnealProv),
      Miri.Interpreter.Step.step lm23Hooks () (lm23InitMiri 0) = (m₁, .ok true) ∧
      StateRelLM2_3 lm23Body lm23Env 1 lm23PipeS1 m₁ ∧
      EnumLocalByteUninit m₁ 1 8 ∧
      Miri.Interpreter.Step.step lm23Hooks () m₁ = (m₂, .ok true) ∧
      StateRelLM2_3 lm23Body lm23Env 1 lm23PipeS2 m₂ ∧
      Miri.Interpreter.Step.step lm23Hooks () m₂ = (m₃, .ok true) ∧
      StateRelLM2_3 lm23Body lm23Env 1 lm23PipeS3 m₃ ∧
      Miri.Interpreter.Step.step lm23Hooks () m₃ = (m₄, .ok true) ∧
      StateRelLM2_3 lm23Body lm23Env 1 lm23PipeS4 m₄ ∧
      Miri.Interpreter.Step.step lm23Hooks () m₄ = (m₅, .ok true) ∧
      StateRelLM2_3 lm23Body lm23Env 1 lm23PipeS5 m₅ ∧
      EnumLocalByteUninit m₅ 1 8 ∧
      Miri.Interpreter.Step.step lm23Hooks () m₅ = (m₆, .ok true) ∧
      StateRelLM2_3 lm23Body lm23Env 0 lm23PipeS6 m₆ ∧
      Miri.Interpreter.Step.step lm23Hooks () m₆ = (m₇, .ok true) ∧
      StateRelLM2_3 lm23Body lm23Env 0 lm23PipeS7 m₇ ∧
      Miri.Interpreter.Step.step lm23Hooks () m₇ = (m₈, .ok true) ∧
      annealControlHooks.returnOperand () m₇ = (m₇, .ok (.immediate imm0)) ∧
      ImmediateRel lm23U64Ty lm23Layouts (.scalar ⟨99, 8⟩) imm0 ∧
      m₈.stack.frames = #[] := by
  -- Step 1: _1 = Lm23Enum::V1(42_u32)
  obtain ⟨m₁, hm₁, hst₁, hu₁, himm₁⟩ :=
    lm23_step_agg_v1_at (b := 0) (budget := 1) (by decide) rfl rfl lm23_pipe_a1
  -- Step 2: _2 = discriminant(_1)
  obtain ⟨hrel₂, hu₂_fn, himm₂_fn⟩ := evalRvalue_discriminant_simulation
    hst₁ lm23_phase lm23_env_valid rfl rfl rfl
    (srcDecl := lm23Decl lm23EnumTy) (dstDecl := lm23Decl lm23IsizeTy)
    rfl rfl rfl lm23_isDiscrDest_isize (himm₁ 2 (by decide))
  rw [lm23_pipe_a2] at hrel₂
  obtain ⟨m₂, hm₂, hst₂⟩ := stepRelLM2_3_inv_step hrel₂
  have hu₂ : EnumLocalByteUninit m₂ 1 8 := by
    simpa [hm₂] using hu₂_fn 1 8 (by decide) hu₁
  have himm₂ : ∀ j, j ≠ 1 → IsImmediateStepLocal m₂ j := fun j hj => by
    simpa [hm₂] using himm₂_fn j (himm₁ j hj)
  -- Step 3: SwitchInt(copy _2, [0 => bb2, 1 => bb1, otherwise => bb2])
  have hsim₃ := enum_match_switchInt_simulation
    hst₂ lm23_env_valid lm23_phase rfl rfl rfl rfl
    (ty := lm23IsizeTy) (Or.inr (Or.inl ⟨.isize, rfl⟩))
    (fun tf htf => .copyLocal 2 (lm23Decl lm23IsizeTy) rfl lm23_isPrim_isize
      (himm₂ 2 (by decide) tf htf))
    lm23_switchCases1_fit
  dsimp only at hsim₃
  rcases hsim₃ with ⟨hrel₃, hpost₃⟩
  rw [lm23_pipe_a3] at hrel₃
  obtain ⟨m₃, hm₃, hst₃⟩ := stepRelLM2_3_inv_event hrel₃
  have hno₃ : ∀ msg, (Miri.Interpreter.Step.step lm23Hooks () m₂).2 ≠
      .error (.undefinedBehavior msg) := by
    rw [hm₃]; intro _ h; cases h
  obtain ⟨hu₃_fn, himm₃_fn⟩ := hpost₃ hno₃
  have hu₃ : EnumLocalByteUninit m₃ 1 8 := by simpa [hm₃] using hu₃_fn 1 8 hu₂
  have himm₃ : ∀ j, j ≠ 1 → IsImmediateStepLocal m₃ j := fun j hj => by
    simpa [hm₃] using himm₃_fn j (himm₂ j hj)
  -- Step 4: _3 = copy ((_1 as Some("V1") 1).0 : u32)
  obtain ⟨hrel₄, hu₄_fn, himm₄_fn⟩ := evalProjection_downcast_field_simulation
    hst₃ lm23_phase lm23_env_valid rfl rfl (isMove := false) rfl
    (srcDecl := lm23Decl lm23EnumTy) (dstDecl := lm23Decl lm23U32Ty)
    rfl rfl rfl (by decide) (by decide) rfl rfl (himm₃ 3 (by decide))
    (fun v_act _ hsl hne => by
      injection hsl with hs; injection hs with hv; injection hv with hv_eq _
      exact absurd hv_eq hne)
  rw [lm23_pipe_a4] at hrel₄
  obtain ⟨m₄, hm₄, hst₄⟩ := stepRelLM2_3_inv_step hrel₄
  have hu₄ : EnumLocalByteUninit m₄ 1 8 := by
    simpa [hm₄] using hu₄_fn 1 8 (by decide) hu₃
  have himm₄ : ∀ j, j ≠ 1 → IsImmediateStepLocal m₄ j := fun j hj => by
    simpa [hm₄] using himm₄_fn j (himm₃ j hj)
  -- Step 5: SetDiscriminant(_1, 0)
  obtain ⟨hrel₅, hu₅_fn, himm₅_fn⟩ := step_setDiscriminant_simulation
    hst₄ lm23_phase lm23_env_valid rfl rfl rfl
    (dstDecl := lm23Decl lm23EnumTy) rfl rfl (by decide)
    (by intro h; cases h) (fun _ _ _ _ _ hi => nomatch hi)
  rw [lm23_pipe_a5] at hrel₅
  obtain ⟨m₅, hm₅, hst₅⟩ := stepRelLM2_3_inv_step hrel₅
  have hu₅ : EnumLocalByteUninit m₅ 1 8 := by
    simpa [hm₅] using hu₅_fn 1 8 (Or.inr ⟨by decide, by decide⟩) hu₄
  have himm₅ : ∀ j, j ≠ 1 → IsImmediateStepLocal m₅ j := fun j hj => by
    simpa [hm₅] using himm₅_fn j (himm₄ j hj)
  -- Step 6: _1 = Lm23Enum::V2(copy _3, 99_u64) (in-place overwrite!)
  have hsim₆ := evalRvalue_aggregate_enum_simulation
    hst₅ lm23_env_valid lm23_phase rfl rfl rfl
    (dstDecl := lm23Decl lm23EnumTy) rfl
    (tagBytes := 4) (variants := lm23Variants) rfl (by decide) rfl
    (fun tf i hi htf => by
      have hi' : i < 2 := hi
      match i with
      | 0 =>
        exact .copyLocal 3 (lm23Decl lm23U32Ty) rfl lm23_isPrim_u32
          (himm₅ 3 (by decide) tf htf)
      | 1 => exact lm23_constU64_wt 99 (by decide) tf
      | _ + 2 => omega)
  dsimp only at hsim₆
  rcases hsim₆ with ⟨hrel₆, hpost₆⟩
  rw [lm23_pipe_a6] at hrel₆
  obtain ⟨m₆, hm₆, hst₆⟩ := stepRelLM2_3_inv_step hrel₆
  have hno₆ : ∀ msg, (Miri.Interpreter.Step.step lm23Hooks () m₅).2 ≠
      .error (.undefinedBehavior msg) := by
    rw [hm₆]; intro _ h; cases h
  have himm₆_0 : IsImmediateStepLocal m₆ 0 := by
    simpa [hm₆] using (hpost₆ hno₆).2.2 0 (by decide) (himm₅ 0 (by decide))
  -- Step 7: _0 = move ((_1 as Some("V2") 2).1 : u64)
  obtain ⟨hrel₇, _, himm₇_fn⟩ := evalProjection_downcast_field_simulation
    hst₆ lm23_phase lm23_env_valid rfl rfl (isMove := true) rfl
    (srcDecl := lm23Decl lm23EnumTy) (dstDecl := lm23Decl lm23U64Ty)
    rfl rfl rfl (by decide) (by decide) rfl rfl himm₆_0
    (fun v_act _ hsl hne => by
      injection hsl with hs; injection hs with hv; injection hv with hv_eq _
      exact absurd hv_eq hne)
  rw [lm23_pipe_a7] at hrel₇
  obtain ⟨m₇, hm₇, hst₇⟩ := stepRelLM2_3_inv_step hrel₇
  have himm₇_0 : IsImmediateStepLocal m₇ 0 := by
    simpa [hm₇] using himm₇_fn 0 himm₆_0
  -- Step 8: return 99_u64
  have hrel₈ := step_return_scalar_lm2_3_simulation
    hst₇ lm23_env_valid lm23_phase rfl rfl rfl rfl rfl
    (decl0 := lm23Decl lm23U64Ty) rfl lm23_isPrim_u64 himm₇_0
  rw [lm23_pipe_a8] at hrel₈
  obtain ⟨d0, imm0, m₈, hm₈, hd0, hret_op, himm_rel, hm₈_eq⟩ :=
    stepRelLM2_3_inv_retNormal hrel₈
  have hd0_eq : d0 = lm23Decl lm23U64Ty := by
    simpa [lm23Body, get?] using hd0.symm
  subst hd0_eq
  refine ⟨m₁, m₂, m₃, m₄, m₅, m₆, m₇, m₈, imm0,
    hm₁, hst₁, hu₁, hm₂, hst₂, hm₃, hst₃, hm₄, hst₄,
    hm₅, hst₅, hu₅, hm₆, hst₆, hm₇, hst₇, hm₈,
    hret_op, himm_rel, ?_⟩
  rw [hm₈_eq]

/-! ## 4. Witnesses 2 & 3: Inactive-Variant `Downcast` + `Field` Read UB -/

def lm23Bb2S1 : MachineState :=
  { frame := { blockIdx := 2, stmtIdx := 1,
               locals := [.uninit, .init (.aggregate 1 [.scalar ⟨42, 4⟩]),
                          .uninit, .uninit, .dead] }
    memory := (initMachineState lm23Body []).memory }

theorem lm23_bb2_a1 : stepMirFn lm23Body (lm23InitAnneal 2) = .step lm23Bb2S1 := rfl
theorem lm23_bb2_a2 : stepMirFn lm23Body lm23Bb2S1 = .fail .ub := rfl

/-- **Witness 2 (`wit_lm2_3_inactive_variant_downcast_ub`)**:
After `_1 = Lm23Enum::V1(42_u32)`, projecting `((_1 as 2).1 : u64)` reads
inactive variant `V2`'s `u64` payload slice `[8, 16)` where byte `8` is
uninitialized (`EnumLocalByteUninit m₁ 1 8`); both Anneal (`stepMirFn`) and
`lean-miri` (`Miri.Interpreter.Step.step`) diagnose undefined behavior in
lockstep. -/
theorem wit_lm2_3_inactive_variant_downcast_ub :
    ∃ (m₁ m₂ : AnnealStepState) (msg : String),
      stepMirFn lm23Body (lm23InitAnneal 2) = .step lm23Bb2S1 ∧
      Miri.Interpreter.Step.step lm23Hooks () (lm23InitMiri 2) = (m₁, .ok true) ∧
      StateRelLM2_3 lm23Body lm23Env 0 lm23Bb2S1 m₁ ∧
      EnumLocalByteUninit m₁ 1 8 ∧
      stepMirFn lm23Body lm23Bb2S1 = .fail .ub ∧
      Miri.Interpreter.Step.step lm23Hooks () m₁ =
        (m₂, .error (.undefinedBehavior msg)) := by
  obtain ⟨m₁, hm₁, hst₁, hu₁, himm₁⟩ :=
    lm23_step_agg_v1_at (b := 2) (budget := 0) (by decide) rfl rfl lm23_bb2_a1
  obtain ⟨hrel₂, _, _⟩ := evalProjection_downcast_field_simulation
    hst₁ lm23_phase lm23_env_valid rfl rfl (isMove := false) rfl
    (srcDecl := lm23Decl lm23EnumTy) (dstDecl := lm23Decl lm23U64Ty)
    rfl rfl rfl (by decide) (by decide) rfl rfl (himm₁ 0 (by decide))
    (fun _ _ _ _ => ⟨8, by decide, by decide, hu₁⟩)
  rw [lm23_bb2_a2] at hrel₂
  obtain ⟨m₂, msg, hm₂⟩ := stepRelLM2_3_inv_ub hrel₂
  exact ⟨m₁, m₂, msg, lm23_bb2_a1, hm₁, hst₁, hu₁, lm23_bb2_a2, hm₂⟩

def lm23Bb3S1 : MachineState :=
  { frame := { blockIdx := 3, stmtIdx := 1,
               locals := [.uninit, .init (.aggregate 1 [.scalar ⟨42, 4⟩]),
                          .uninit, .uninit, .dead] }
    memory := (initMachineState lm23Body []).memory }

def lm23Bb3S2 : MachineState :=
  { frame := { blockIdx := 3, stmtIdx := 2,
               locals := [.uninit, .init (.aggregate 0 [.scalar ⟨42, 4⟩]),
                          .uninit, .uninit, .dead] }
    memory := (initMachineState lm23Body []).memory }

theorem lm23_bb3_a1 : stepMirFn lm23Body (lm23InitAnneal 3) = .step lm23Bb3S1 := rfl
theorem lm23_bb3_a2 : stepMirFn lm23Body lm23Bb3S1 = .step lm23Bb3S2 := rfl
theorem lm23_bb3_a3 : stepMirFn lm23Body lm23Bb3S2 = .fail .ub := rfl

/-- **Witness 3 (`wit_lm2_3_setDiscriminant_then_inactive_ub`)**:
After `_1 = Lm23Enum::V1(42_u32); SetDiscriminant(_1, 0)`, byte `8` remains
uninitialized (`EnumLocalByteUninit m₂ 1 8`) and reading `((_1 as 2).1 : u64)`
traps with undefined behavior in lockstep in both machines. -/
theorem wit_lm2_3_setDiscriminant_then_inactive_ub :
    ∃ (m₁ m₂ m₃ : AnnealStepState) (msg : String),
      Miri.Interpreter.Step.step lm23Hooks () (lm23InitMiri 3) = (m₁, .ok true) ∧
      Miri.Interpreter.Step.step lm23Hooks () m₁ = (m₂, .ok true) ∧
      StateRelLM2_3 lm23Body lm23Env 0 lm23Bb3S2 m₂ ∧
      EnumLocalByteUninit m₂ 1 8 ∧
      stepMirFn lm23Body lm23Bb3S2 = .fail .ub ∧
      Miri.Interpreter.Step.step lm23Hooks () m₂ =
        (m₃, .error (.undefinedBehavior msg)) := by
  obtain ⟨m₁, hm₁, hst₁, hu₁, himm₁⟩ :=
    lm23_step_agg_v1_at (b := 3) (budget := 0) (by decide) rfl rfl lm23_bb3_a1
  obtain ⟨hrel₂, hu₂_fn, himm₂_fn⟩ := step_setDiscriminant_simulation
    hst₁ lm23_phase lm23_env_valid rfl rfl rfl
    (dstDecl := lm23Decl lm23EnumTy) rfl rfl (by decide)
    (by intro h; cases h) (fun _ _ _ _ _ hi => nomatch hi)
  rw [lm23_bb3_a2] at hrel₂
  obtain ⟨m₂, hm₂, hst₂⟩ := stepRelLM2_3_inv_step hrel₂
  have hu₂ : EnumLocalByteUninit m₂ 1 8 := by
    simpa [hm₂] using hu₂_fn 1 8 (Or.inr ⟨by decide, by decide⟩) hu₁
  have himm₂_0 : IsImmediateStepLocal m₂ 0 := by
    simpa [hm₂] using himm₂_fn 0 (himm₁ 0 (by decide))
  obtain ⟨hrel₃, _, _⟩ := evalProjection_downcast_field_simulation
    hst₂ lm23_phase lm23_env_valid rfl rfl (isMove := false) rfl
    (srcDecl := lm23Decl lm23EnumTy) (dstDecl := lm23Decl lm23U64Ty)
    rfl rfl rfl (by decide) (by decide) rfl rfl himm₂_0
    (fun _ _ _ _ => ⟨8, by decide, by decide, hu₂⟩)
  rw [lm23_bb3_a3] at hrel₃
  obtain ⟨m₃, msg, hm₃⟩ := stepRelLM2_3_inv_ub hrel₃
  exact ⟨m₁, m₂, m₃, msg, hm₁, hm₂, hst₂, hu₂, lm23_bb3_a3, hm₃⟩

/-! ## 5. Witness 4: `SwitchInt` `otherwise` + `Goto` + `Return` (`bb4..bb6`) -/

def lm23Bb4S1 : MachineState :=
  { frame := { blockIdx := 4, stmtIdx := 1,
               locals := [.uninit,
                          .init (.aggregate 2 [.scalar ⟨7, 4⟩, .scalar ⟨88, 8⟩]),
                          .uninit, .uninit, .dead] }
    memory := (initMachineState lm23Body []).memory }

def lm23Bb4S2 : MachineState :=
  { frame := { blockIdx := 4, stmtIdx := 2,
               locals := [.uninit,
                          .init (.aggregate 2 [.scalar ⟨7, 4⟩, .scalar ⟨88, 8⟩]),
                          .init (.scalar ⟨2, 8⟩), .uninit, .dead] }
    memory := (initMachineState lm23Body []).memory }

def lm23Bb5S0 : MachineState :=
  { frame := { blockIdx := 5, stmtIdx := 0,
               locals := [.uninit,
                          .init (.aggregate 2 [.scalar ⟨7, 4⟩, .scalar ⟨88, 8⟩]),
                          .init (.scalar ⟨2, 8⟩), .uninit, .dead] }
    memory := (initMachineState lm23Body []).memory }

def lm23Bb6S0 : MachineState :=
  { frame := { blockIdx := 6, stmtIdx := 0,
               locals := [.uninit,
                          .init (.aggregate 2 [.scalar ⟨7, 4⟩, .scalar ⟨88, 8⟩]),
                          .init (.scalar ⟨2, 8⟩), .uninit, .dead] }
    memory := (initMachineState lm23Body []).memory }

def lm23Bb6S1 : MachineState :=
  { frame := { blockIdx := 6, stmtIdx := 1,
               locals := [.init (.scalar ⟨88, 8⟩),
                          .init (.aggregate 2 [.scalar ⟨7, 4⟩, .scalar ⟨88, 8⟩]),
                          .init (.scalar ⟨2, 8⟩), .uninit, .dead] }
    memory := (initMachineState lm23Body []).memory }

theorem lm23_bb4_a1 : stepMirFn lm23Body (lm23InitAnneal 4) = .step lm23Bb4S1 := rfl
theorem lm23_bb4_a2 : stepMirFn lm23Body lm23Bb4S1 = .step lm23Bb4S2 := rfl
theorem lm23_bb4_a3 :
    stepMirFn lm23Body lm23Bb4S2 = .emitStep (.event 2) lm23Bb5S0 := rfl
theorem lm23_bb4_a4 : stepMirFn lm23Body lm23Bb5S0 = .step lm23Bb6S0 := rfl
theorem lm23_bb4_a5 : stepMirFn lm23Body lm23Bb6S0 = .step lm23Bb6S1 := rfl
theorem lm23_bb4_a6 :
    stepMirFn lm23Body lm23Bb6S1 =
      .retNormal (.scalar ⟨88, 8⟩) (initMachineState lm23Body []).memory := rfl

/-- **Witness 4 (`wit_lm2_3_switch_otherwise_and_goto_trace`)**:
Constructing `Lm23Enum::V2(7_u32, 88_u64)`, reading `discriminant(_1) = 2`,
branching via `SwitchInt`'s `otherwise => bb5` fallback arm, stepping across
`Goto -> bb6` (`step_goto_lm2_3_simulation`), projecting `V2.1 = 88_u64`, and
returning `88_u64` in lockstep. -/
theorem wit_lm2_3_switch_otherwise_and_goto_trace :
    ∃ (m₁ m₂ m₃ m₄ m₅ m₆ : AnnealStepState)
      (imm0 : Miri.Interpreter.Immediate AnnealProv),
      Miri.Interpreter.Step.step lm23Hooks () (lm23InitMiri 4) = (m₁, .ok true) ∧
      Miri.Interpreter.Step.step lm23Hooks () m₁ = (m₂, .ok true) ∧
      Miri.Interpreter.Step.step lm23Hooks () m₂ = (m₃, .ok true) ∧
      StateRelLM2_3 lm23Body lm23Env 0 lm23Bb5S0 m₃ ∧
      Miri.Interpreter.Step.step lm23Hooks () m₃ = (m₄, .ok true) ∧
      StateRelLM2_3 lm23Body lm23Env 0 lm23Bb6S0 m₄ ∧
      Miri.Interpreter.Step.step lm23Hooks () m₄ = (m₅, .ok true) ∧
      Miri.Interpreter.Step.step lm23Hooks () m₅ = (m₆, .ok true) ∧
      annealControlHooks.returnOperand () m₅ = (m₅, .ok (.immediate imm0)) ∧
      ImmediateRel lm23U64Ty lm23Layouts (.scalar ⟨88, 8⟩) imm0 := by
  have hsim₁ := evalRvalue_aggregate_enum_simulation
    (lm23_init_stateRelLM2_3 4 1 (by decide)) lm23_env_valid lm23_phase
    rfl rfl rfl (dstDecl := lm23Decl lm23EnumTy) rfl
    (tagBytes := 4) (variants := lm23Variants) rfl (by decide) rfl
    (fun tf i hi _ => by
      have hi' : i < 2 := hi
      match i with
      | 0 => exact lm23_constU32_wt 7 (by decide) tf
      | 1 => exact lm23_constU64_wt 88 (by decide) tf
      | _ + 2 => omega)
  dsimp only at hsim₁
  rcases hsim₁ with ⟨hrel₁, hpost₁⟩
  rw [lm23_bb4_a1] at hrel₁
  obtain ⟨m₁, hm₁, hst₁⟩ := stepRelLM2_3_inv_step hrel₁
  have hno₁ : ∀ msg, (Miri.Interpreter.Step.step lm23Hooks () (lm23InitMiri 4)).2 ≠
      .error (.undefinedBehavior msg) := by
    rw [hm₁]; intro _ h; cases h
  have himm₁ : ∀ j, j ≠ 1 → IsImmediateStepLocal m₁ j := fun j hj => by
    simpa [hm₁] using (hpost₁ hno₁).2.2 j hj (lm23_init_imm 4 j)
  obtain ⟨hrel₂, _, himm₂_fn⟩ := evalRvalue_discriminant_simulation
    hst₁ lm23_phase lm23_env_valid rfl rfl rfl
    (srcDecl := lm23Decl lm23EnumTy) (dstDecl := lm23Decl lm23IsizeTy)
    rfl rfl rfl lm23_isDiscrDest_isize (himm₁ 2 (by decide))
  rw [lm23_bb4_a2] at hrel₂
  obtain ⟨m₂, hm₂, hst₂⟩ := stepRelLM2_3_inv_step hrel₂
  have himm₂ : ∀ j, j ≠ 1 → IsImmediateStepLocal m₂ j := fun j hj => by
    simpa [hm₂] using himm₂_fn j (himm₁ j hj)
  have hsim₃ := enum_match_switchInt_simulation
    hst₂ lm23_env_valid lm23_phase rfl rfl rfl rfl
    (ty := lm23IsizeTy) (Or.inr (Or.inl ⟨.isize, rfl⟩))
    (fun tf htf => .copyLocal 2 (lm23Decl lm23IsizeTy) rfl lm23_isPrim_isize
      (himm₂ 2 (by decide) tf htf))
    lm23_switchCasesOtherwise_fit
  dsimp only at hsim₃
  rcases hsim₃ with ⟨hrel₃, hpost₃⟩
  rw [lm23_bb4_a3] at hrel₃
  obtain ⟨m₃, hm₃, hst₃⟩ := stepRelLM2_3_inv_event hrel₃
  have hno₃ : ∀ msg, (Miri.Interpreter.Step.step lm23Hooks () m₂).2 ≠
      .error (.undefinedBehavior msg) := by
    rw [hm₃]; intro _ h; cases h
  have himm₃_0 : IsImmediateStepLocal m₃ 0 := by
    simpa [hm₃] using (hpost₃ hno₃).2 0 (himm₂ 0 (by decide))
  have hsim₄ := step_goto_lm2_3_simulation hst₃ lm23_phase rfl rfl rfl rfl
  dsimp only at hsim₄
  rcases hsim₄ with ⟨hrel₄, _, himm₄_fn⟩
  rw [lm23_bb4_a4] at hrel₄
  obtain ⟨m₄, hm₄, hst₄⟩ := stepRelLM2_3_inv_step hrel₄
  have himm₄_0 : IsImmediateStepLocal m₄ 0 := by
    simpa [hm₄] using himm₄_fn 0 himm₃_0
  obtain ⟨hrel₅, _, himm₅_fn⟩ := evalProjection_downcast_field_simulation
    hst₄ lm23_phase lm23_env_valid rfl rfl (isMove := false) rfl
    (srcDecl := lm23Decl lm23EnumTy) (dstDecl := lm23Decl lm23U64Ty)
    rfl rfl rfl (by decide) (by decide) rfl rfl himm₄_0
    (fun v_act _ hsl hne => by
      injection hsl with hs; injection hs with hv; injection hv with hv_eq _
      exact absurd hv_eq hne)
  rw [lm23_bb4_a5] at hrel₅
  obtain ⟨m₅, hm₅, hst₅⟩ := stepRelLM2_3_inv_step hrel₅
  have himm₅_0 : IsImmediateStepLocal m₅ 0 := by
    simpa [hm₅] using himm₅_fn 0 himm₄_0
  have hrel₆ := step_return_scalar_lm2_3_simulation
    hst₅ lm23_env_valid lm23_phase rfl rfl rfl rfl rfl
    (decl0 := lm23Decl lm23U64Ty) rfl lm23_isPrim_u64 himm₅_0
  rw [lm23_bb4_a6] at hrel₆
  obtain ⟨d0, imm0, m₆, hm₆, hd0, hret_op, himm_rel, _⟩ :=
    stepRelLM2_3_inv_retNormal hrel₆
  have hd0_eq : d0 = lm23Decl lm23U64Ty := by
    simpa [lm23Body, get?] using hd0.symm
  subst hd0_eq
  exact ⟨m₁, m₂, m₃, m₄, m₅, m₆, imm0,
    hm₁, hm₂, hm₃, hst₃, hm₄, hst₄, hm₅, hm₆, hret_op, himm_rel⟩

/-! ## 6. Witness 5: Lockstep `.uninit`/`.dead` Enum UB (`bb7`, `bb9..bb11`) -/

/-- **Witness 5 (`wit_lm2_3_uninit_and_dead_ub`)**:
Lockstep undefined behavior on four uninitialized or dead enum error paths:
`discriminant` on `.uninit`, `Aggregate` write to `.dead`, `Downcast` + `Field`
read from `.dead`, and `SetDiscriminant` on `.dead`. -/
theorem wit_lm2_3_uninit_and_dead_ub :
    (stepMirFn lm23Body (lm23InitAnneal 7) = .fail .ub ∧
      ∃ msg, (Miri.Interpreter.Step.step lm23Hooks () (lm23InitMiri 7)).2 =
        .error (.undefinedBehavior msg)) ∧
    (stepMirFn lm23Body (lm23InitAnneal 9) = .fail .ub ∧
      ∃ msg, (Miri.Interpreter.Step.step lm23Hooks () (lm23InitMiri 9)).2 =
        .error (.undefinedBehavior msg)) ∧
    (stepMirFn lm23Body (lm23InitAnneal 10) = .fail .ub ∧
      ∃ msg, (Miri.Interpreter.Step.step lm23Hooks () (lm23InitMiri 10)).2 =
        .error (.undefinedBehavior msg)) ∧
    (stepMirFn lm23Body (lm23InitAnneal 11) = .fail .ub ∧
      ∃ msg, (Miri.Interpreter.Step.step lm23Hooks () (lm23InitMiri 11)).2 =
        .error (.undefinedBehavior msg)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have ha : stepMirFn lm23Body (lm23InitAnneal 7) = .fail .ub := rfl
    obtain ⟨hrel, _, _⟩ := evalRvalue_discriminant_simulation
      (lm23_init_stateRelLM2_3 7 0 (by decide)) lm23_phase lm23_env_valid
      rfl rfl rfl (srcDecl := lm23Decl lm23EnumTy) (dstDecl := lm23Decl lm23IsizeTy)
      rfl rfl rfl lm23_isDiscrDest_isize (lm23_init_imm 7 2)
    exact ⟨ha, hrel.ub_iff.mp ha⟩
  · have ha : stepMirFn lm23Body (lm23InitAnneal 9) = .fail .ub := rfl
    have hsim := evalRvalue_aggregate_enum_simulation
      (lm23_init_stateRelLM2_3 9 1 (by decide)) lm23_env_valid lm23_phase
      rfl rfl rfl (dstDecl := lm23Decl lm23EnumTy) rfl
      (tagBytes := 4) (variants := lm23Variants) rfl (by decide) rfl
      (fun _ _ hi _ => by cases hi)
    exact ⟨ha, hsim.1.ub_iff.mp ha⟩
  · have ha : stepMirFn lm23Body (lm23InitAnneal 10) = .fail .ub := rfl
    obtain ⟨hrel, _, _⟩ := evalProjection_downcast_field_simulation
      (lm23_init_stateRelLM2_3 10 0 (by decide)) lm23_phase lm23_env_valid
      rfl rfl (isMove := false) rfl
      (srcDecl := lm23Decl lm23EnumTy) (dstDecl := lm23Decl lm23U32Ty)
      rfl rfl rfl (by decide) (by decide) rfl rfl (lm23_init_imm 10 3)
      (fun _ _ hsl _ => by simp [lm23InitAnneal, get?] at hsl)
    exact ⟨ha, hrel.ub_iff.mp ha⟩
  · have ha : stepMirFn lm23Body (lm23InitAnneal 11) = .fail .ub := rfl
    obtain ⟨hrel, _, _⟩ := step_setDiscriminant_simulation
      (lm23_init_stateRelLM2_3 11 0 (by decide)) lm23_phase lm23_env_valid
      rfl rfl rfl (dstDecl := lm23Decl lm23EnumTy) rfl rfl (by decide)
      (by intro h; cases h)
      (fun _ _ _ hsl _ _ => by simp [lm23InitAnneal, get?] at hsl)
    exact ⟨ha, hrel.ub_iff.mp ha⟩

/-! ## 7. Witness 6: `SetDiscriminant` on `.uninit` Diverges (`bb8`) -/

/-- **Witness 6 (`wit_lm2_3_setDiscriminant_uninit_divergence`)**:
`SetDiscriminant(_1, 0)` on the fresh `.uninit` local `_1` is UB in Anneal,
but lean-miri forces `_1` into memory, writes tag `0`, and completes the step
(`step_setDiscriminant_uninit_divergence`). -/
theorem wit_lm2_3_setDiscriminant_uninit_divergence :
    stepMirFn lm23Body (lm23InitAnneal 8) = .fail .ub ∧
    ∃ m', Miri.Interpreter.Step.step lm23Hooks () (lm23InitMiri 8) = (m', .ok true) :=
  step_setDiscriminant_uninit_divergence
    (lm23_init_stateRelLM2_3 8 1 (by decide)) lm23_phase lm23_env_valid
    rfl rfl rfl (dstDecl := lm23Decl lm23EnumTy) rfl rfl (by decide) rfl

/-! ## 8. Witness 7: Inactive-Variant Read on Init Bytes Diverges (`bb12`) -/

def lm23Bb12S1 : MachineState :=
  { frame := { blockIdx := 12, stmtIdx := 1,
               locals := [.uninit, .init (.aggregate 1 [.scalar ⟨42, 4⟩]),
                          .uninit, .uninit, .dead] }
    memory := (initMachineState lm23Body []).memory }

def lm23Bb12S2 : MachineState :=
  { frame := { blockIdx := 12, stmtIdx := 2,
               locals := [.uninit, .init (.aggregate 1 [.scalar ⟨42, 4⟩]),
                          .uninit, .init (.scalar ⟨42, 4⟩), .dead] }
    memory := (initMachineState lm23Body []).memory }

theorem lm23_bb12_a1 : stepMirFn lm23Body (lm23InitAnneal 12) = .step lm23Bb12S1 := rfl
theorem lm23_bb12_a2 : stepMirFn lm23Body lm23Bb12S1 = .fail .ub := rfl

/-- **Witness 7 (`wit_lm2_3_inactive_variant_initialized_divergence`)**:
After `_1 = Lm23Enum::V1(42_u32)`, projecting inactive variant `V2`'s first
field `((_1 as 2).0 : u32)` at offset `4` (which overlaps active variant `V1`'s
field `0` at `[4, 8)`) is rejected by Anneal (`stepMirFn = .fail .ub`), whereas
`lean-miri` reads the initialized `u32` scalar `42` from `[4, 8)` without
checking the discriminant tag and writes `42_u32` into `_3`
(`evalProjection_downcast_field_initialized_divergence`). -/
theorem wit_lm2_3_inactive_variant_initialized_divergence :
    ∃ (m₁ m₂ : AnnealStepState),
      stepMirFn lm23Body (lm23InitAnneal 12) = .step lm23Bb12S1 ∧
      Miri.Interpreter.Step.step lm23Hooks () (lm23InitMiri 12) = (m₁, .ok true) ∧
      StateRelLM2_3 lm23Body lm23Env 0 lm23Bb12S1 m₁ ∧
      stepMirFn lm23Body lm23Bb12S1 = .fail .ub ∧
      Miri.Interpreter.Step.step lm23Hooks () m₁ = (m₂, .ok true) ∧
      StateRelLM2_3 lm23Body lm23Env 0 lm23Bb12S2 m₂ := by
  obtain ⟨m₁, hm₁, hst₁, _, himm₁⟩ :=
    lm23_step_agg_v1_at (b := 12) (budget := 0) (by decide) rfl rfl lm23_bb12_a1
  obtain ⟨ha₂, sc, m₂, hsc, hm₂, hst₂, _, _⟩ :=
    evalProjection_downcast_field_initialized_divergence
      hst₁ lm23_phase lm23_env_valid rfl rfl (isMove := false) rfl
      (srcDecl := lm23Decl lm23EnumTy) (dstDecl := lm23Decl lm23U32Ty)
      (v_act := 1) (j := 0) (fieldVals := [.scalar ⟨42, 4⟩])
      rfl rfl rfl (by decide) (by decide) rfl rfl (himm₁ 3 (by decide))
      (by intro h; cases h) rfl (by decide) (by decide) (by decide) (by decide) rfl
  have hsc_eq : sc = ⟨42, 4⟩ := by
    simpa [get?] using hsc.symm
  subst hsc_eq
  exact ⟨m₁, m₂, lm23_bb12_a1, hm₁, hst₁, ha₂, hm₂, hst₂⟩

/-! ## 9. Witness 8: Non-Empty Prefix `SetDiscriminant` + Read (`bb13`) -/

def lm23Bb13S1 : MachineState :=
  { frame := { blockIdx := 13, stmtIdx := 1,
               locals := [.uninit,
                          .init (.aggregate 2 [.scalar ⟨42, 4⟩, .scalar ⟨99, 8⟩]),
                          .uninit, .uninit, .dead] }
    memory := (initMachineState lm23Body []).memory }

def lm23Bb13S2 : MachineState :=
  { frame := { blockIdx := 13, stmtIdx := 2,
               locals := [.uninit,
                          .init (.aggregate 1 [.scalar ⟨42, 4⟩, .scalar ⟨99, 8⟩]),
                          .uninit, .uninit, .dead] }
    memory := (initMachineState lm23Body []).memory }

def lm23Bb13S3 : MachineState :=
  { frame := { blockIdx := 13, stmtIdx := 3,
               locals := [.uninit,
                          .init (.aggregate 1 [.scalar ⟨42, 4⟩, .scalar ⟨99, 8⟩]),
                          .uninit, .init (.scalar ⟨42, 4⟩), .dead] }
    memory := (initMachineState lm23Body []).memory }

theorem lm23_bb13_a1 : stepMirFn lm23Body (lm23InitAnneal 13) = .step lm23Bb13S1 := rfl
theorem lm23_bb13_a2 : stepMirFn lm23Body lm23Bb13S1 = .step lm23Bb13S2 := rfl
theorem lm23_bb13_a3 : stepMirFn lm23Body lm23Bb13S2 = .step lm23Bb13S3 := rfl

/-- **Witness 8 (`wit_lm2_3_prefix_setDiscriminant_read`)**:
After `_1 = Lm23Enum::V2(42_u32, 99_u64)`, `SetDiscriminant(_1, 1)` mutates the
discriminant tag in place from `2` (`V2`) to `1` (`V1`) whose payload layout
`[u32 @ 4]` is a non-empty strict prefix of `V2`'s `[u32 @ 4, u64 @ 8]`
(`lm23Variants[1] <+: lm23Variants[2]`), and `_3 = copy ((_1 as 1).0 : u32)`
then reads `42_u32` in lockstep in both Anneal and `lean-miri`. -/
theorem wit_lm2_3_prefix_setDiscriminant_read :
    ∃ (m₁ m₂ m₃ : AnnealStepState),
      stepMirFn lm23Body (lm23InitAnneal 13) = .step lm23Bb13S1 ∧
      Miri.Interpreter.Step.step lm23Hooks () (lm23InitMiri 13) = (m₁, .ok true) ∧
      StateRelLM2_3 lm23Body lm23Env 0 lm23Bb13S1 m₁ ∧
      stepMirFn lm23Body lm23Bb13S1 = .step lm23Bb13S2 ∧
      Miri.Interpreter.Step.step lm23Hooks () m₁ = (m₂, .ok true) ∧
      StateRelLM2_3 lm23Body lm23Env 0 lm23Bb13S2 m₂ ∧
      stepMirFn lm23Body lm23Bb13S2 = .step lm23Bb13S3 ∧
      Miri.Interpreter.Step.step lm23Hooks () m₂ = (m₃, .ok true) ∧
      StateRelLM2_3 lm23Body lm23Env 0 lm23Bb13S3 m₃ := by
  have hsim₁ := evalRvalue_aggregate_enum_simulation
    (lm23_init_stateRelLM2_3 13 1 (by decide)) lm23_env_valid lm23_phase
    rfl rfl rfl (dstDecl := lm23Decl lm23EnumTy) rfl
    (tagBytes := 4) (variants := lm23Variants) rfl (by decide) rfl
    (fun tf i hi _ => by
      have hi' : i < 2 := hi
      match i with
      | 0 => exact lm23_constU32_wt 42 (by decide) tf
      | 1 => exact lm23_constU64_wt 99 (by decide) tf
      | _ + 2 => omega)
  dsimp only at hsim₁
  rcases hsim₁ with ⟨hrel₁, hpost₁⟩
  rw [lm23_bb13_a1] at hrel₁
  obtain ⟨m₁, hm₁, hst₁⟩ := stepRelLM2_3_inv_step hrel₁
  have hno₁ : ∀ msg, (Miri.Interpreter.Step.step lm23Hooks () (lm23InitMiri 13)).2 ≠
      .error (.undefinedBehavior msg) := by
    rw [hm₁]; intro _ h; cases h
  have himm₁_3 : IsImmediateStepLocal m₁ 3 := by
    simpa [hm₁] using (hpost₁ hno₁).2.2 3 (by decide) (lm23_init_imm 13 3)
  obtain ⟨hrel₂, _, himm₂_fn⟩ := step_setDiscriminant_simulation
    hst₁ lm23_phase lm23_env_valid rfl rfl rfl
    (dstDecl := lm23Decl lm23EnumTy) rfl rfl (by decide)
    (by intro h; cases h)
    (fun v_act hv_act _ hsl i hi => by
      injection hsl with hs; injection hs with hv; injection hv with hv_eq _
      subst hv_eq
      have hi' : i < 1 := hi
      match i with
      | 0 => exact Or.inl ⟨by decide +revert, rfl⟩
      | _ + 1 => omega)
  rw [lm23_bb13_a2] at hrel₂
  obtain ⟨m₂, hm₂, hst₂⟩ := stepRelLM2_3_inv_step hrel₂
  have himm₂_3 : IsImmediateStepLocal m₂ 3 := by
    simpa [hm₂] using himm₂_fn 3 himm₁_3
  obtain ⟨hrel₃, _, _⟩ := evalProjection_downcast_field_simulation
    hst₂ lm23_phase lm23_env_valid rfl rfl (isMove := false) rfl
    (srcDecl := lm23Decl lm23EnumTy) (dstDecl := lm23Decl lm23U32Ty)
    rfl rfl rfl (by decide) (by decide) rfl rfl himm₂_3
    (fun v_act _ hsl hne => by
      injection hsl with hs; injection hs with hv; injection hv with hv_eq _
      exact absurd hv_eq hne)
  rw [lm23_bb13_a3] at hrel₃
  obtain ⟨m₃, hm₃, hst₃⟩ := stepRelLM2_3_inv_step hrel₃
  exact ⟨m₁, m₂, m₃, lm23_bb13_a1, hm₁, hst₁, lm23_bb13_a2, hm₂, hst₂,
    lm23_bb13_a3, hm₃, hst₃⟩

/-! ## 10. Witness 9: Wider-Variant `SetDiscriminant` (`V1 -> V2`) (`bb14`) -/

def lm23Bb14S1 : MachineState :=
  { frame := { blockIdx := 14, stmtIdx := 1,
               locals := [.uninit, .init (.aggregate 1 [.scalar ⟨42, 4⟩]),
                          .uninit, .uninit, .dead] }
    memory := (initMachineState lm23Body []).memory }

def lm23Bb14S2 : MachineState :=
  { frame := { blockIdx := 14, stmtIdx := 2,
               locals := [.uninit, .init (.aggregate 2 [.scalar ⟨42, 4⟩]),
                          .uninit, .uninit, .dead] }
    memory := (initMachineState lm23Body []).memory }

def lm23Bb14S3 : MachineState :=
  { frame := { blockIdx := 14, stmtIdx := 3,
               locals := [.uninit, .init (.aggregate 2 [.scalar ⟨42, 4⟩]),
                          .uninit, .init (.scalar ⟨42, 4⟩), .dead] }
    memory := (initMachineState lm23Body []).memory }

theorem lm23_bb14_a1 : stepMirFn lm23Body (lm23InitAnneal 14) = .step lm23Bb14S1 := rfl
theorem lm23_bb14_a2 : stepMirFn lm23Body lm23Bb14S1 = .step lm23Bb14S2 := rfl
theorem lm23_bb14_a3 : stepMirFn lm23Body lm23Bb14S2 = .step lm23Bb14S3 := rfl
theorem lm23_bb14_a4 : stepMirFn lm23Body lm23Bb14S3 = .fail .ub := rfl

/-- **Witness 9 (`wit_lm2_3_upcast_setDiscriminant_read_and_trailing_ub`)**:
After `_1 = Lm23Enum::V1(42_u32)`, `SetDiscriminant(_1, 2)` mutates the
discriminant tag in place from `1` (`V1`) to `2` (`V2`), a wider variant whose
first field `V2.0 : u32` at `[4, 8)` matches `V1.0` while its trailing second
field `V2.1 : u64` at `[8, 16)` is absent from `fieldVals` (`get? fieldVals 1 =
none`) and uninitialized in memory (`EnumLocalByteUninit m₁ 1 8`). Both machines
step through `SetDiscriminant(_1, 2)` in `StateRelLM2_3`, then read the shared
prefix field `_3 = copy ((_1 as 2).0 : u32)` (`42_u32`) in lockstep, and then
trap with undefined behavior in lockstep on `_0 = copy ((_1 as 2).1 : u64)` when
reading the uninitialized trailing field of active variant `V2`. -/
theorem wit_lm2_3_upcast_setDiscriminant_read_and_trailing_ub :
    ∃ (m₁ m₂ m₃ m₄ : AnnealStepState) (msg : String),
      stepMirFn lm23Body (lm23InitAnneal 14) = .step lm23Bb14S1 ∧
      Miri.Interpreter.Step.step lm23Hooks () (lm23InitMiri 14) = (m₁, .ok true) ∧
      StateRelLM2_3 lm23Body lm23Env 0 lm23Bb14S1 m₁ ∧
      EnumLocalByteUninit m₁ 1 8 ∧
      stepMirFn lm23Body lm23Bb14S1 = .step lm23Bb14S2 ∧
      Miri.Interpreter.Step.step lm23Hooks () m₁ = (m₂, .ok true) ∧
      StateRelLM2_3 lm23Body lm23Env 0 lm23Bb14S2 m₂ ∧
      stepMirFn lm23Body lm23Bb14S2 = .step lm23Bb14S3 ∧
      Miri.Interpreter.Step.step lm23Hooks () m₂ = (m₃, .ok true) ∧
      StateRelLM2_3 lm23Body lm23Env 0 lm23Bb14S3 m₃ ∧
      stepMirFn lm23Body lm23Bb14S3 = .fail .ub ∧
      Miri.Interpreter.Step.step lm23Hooks () m₃ =
        (m₄, .error (.undefinedBehavior msg)) := by
  obtain ⟨m₁, hm₁, hst₁, hu₁, himm₁⟩ :=
    lm23_step_agg_v1_at (b := 14) (budget := 0) (by decide) rfl rfl lm23_bb14_a1
  obtain ⟨hrel₂, _, himm₂_fn⟩ := step_setDiscriminant_simulation
    hst₁ lm23_phase lm23_env_valid rfl rfl rfl
    (dstDecl := lm23Decl lm23EnumTy) rfl rfl (by decide)
    (by intro h; cases h)
    (fun v_act hv_act fieldVals hsl i hi => by
      injection hsl with hs; injection hs with hv; injection hv with hv_eq hfv_eq
      subst hv_eq hfv_eq
      have hi' : i < 2 := hi
      match i with
      | 0 => exact Or.inl ⟨by decide +revert, rfl⟩
      | 1 => exact Or.inr ⟨rfl, 8, by decide +revert, by decide +revert, hu₁⟩
      | _ + 2 => omega)
  rw [lm23_bb14_a2] at hrel₂
  obtain ⟨m₂, hm₂, hst₂⟩ := stepRelLM2_3_inv_step hrel₂
  have himm₂ : ∀ j, j ≠ 1 → IsImmediateStepLocal m₂ j := fun j hj => by
    simpa [hm₂] using himm₂_fn j (himm₁ j hj)
  obtain ⟨hrel₃, _, himm₃_fn⟩ := evalProjection_downcast_field_simulation
    hst₂ lm23_phase lm23_env_valid rfl rfl (isMove := false) rfl
    (srcDecl := lm23Decl lm23EnumTy) (dstDecl := lm23Decl lm23U32Ty)
    rfl rfl rfl (by decide) (by decide) rfl rfl (himm₂ 3 (by decide))
    (fun v_act _ hsl hne => by
      injection hsl with hs; injection hs with hv; injection hv with hv_eq _
      exact absurd hv_eq hne)
  rw [lm23_bb14_a3] at hrel₃
  obtain ⟨m₃, hm₃, hst₃⟩ := stepRelLM2_3_inv_step hrel₃
  have himm₃_0 : IsImmediateStepLocal m₃ 0 := by
    simpa [hm₃] using himm₃_fn 0 (himm₂ 0 (by decide))
  obtain ⟨hrel₄, _, _⟩ := evalProjection_downcast_field_simulation
    hst₃ lm23_phase lm23_env_valid rfl rfl (isMove := false) rfl
    (srcDecl := lm23Decl lm23EnumTy) (dstDecl := lm23Decl lm23U64Ty)
    rfl rfl rfl (by decide) (by decide) rfl rfl himm₃_0
    (fun v_act _ hsl hne => by
      injection hsl with hs; injection hs with hv; injection hv with hv_eq _
      exact absurd hv_eq hne)
  rw [lm23_bb14_a4] at hrel₄
  obtain ⟨m₄, msg, hm₄⟩ := stepRelLM2_3_inv_ub hrel₄
  exact ⟨m₁, m₂, m₃, m₄, msg, lm23_bb14_a1, hm₁, hst₁, hu₁, lm23_bb14_a2,
    hm₂, hst₂, lm23_bb14_a3, hm₃, hst₃, lm23_bb14_a4, hm₄⟩

/-! ## 11. Witness 10: Conservative Extension (`BodyFreeOfLM2_3`) -/

/-- **Witness 10 (`wit_lm2_3_bodyFree_divBody`)**:
`LM-1.1`'s scalar `divBody` satisfies `BodyFreeOfLM2_3`, so
`annealStepHooksLM2_3` steps identically to `annealStepHooksLM2_2` on `miriInit`. -/
theorem wit_lm2_3_bodyFree_divBody (divisor : Nat) :
    BodyFreeOfLM2_3 (divBody divisor).localDecls (divBody divisor).layouts
      (translateBody (divBody divisor)) ∧
    Miri.Interpreter.Step.step
        (annealStepHooksLM2_3 (divBody divisor).localDecls (divBody divisor).layouts)
        () (miriInit divisor) =
      Miri.Interpreter.Step.step
        (annealStepHooksLM2_2 (divBody divisor).localDecls (divBody divisor).layouts)
        () (miriInit divisor) := by
  have hfree :
      BodyFreeOfLM2_3 (divBody divisor).localDecls (divBody divisor).layouts
        (translateBody (divBody divisor)) := by
    intro bb hbb stmt hstmt
    have hbb' : bb ∈
        [translateBasicBlockData
          { statements :=
              [ mkStmt (.storageLive 1)
              , mkStmt (.assign (local_ 1) (.use (.constant (constU8 7))))
              , mkStmt (.assign (local_ 0)
                  (.binaryOp .div (.copy (local_ 1))
                    (.constant (constU8 divisor))))
              , mkStmt (.storageDead 1) ]
            terminator := mkTerm .return_, isCleanup := false }] := hbb
    rcases List.mem_singleton.mp hbb' with rfl
    have hstmt' : stmt ∈
        [ translateStmt (mkStmt (.storageLive 1))
        , translateStmt (mkStmt (.assign (local_ 1) (.use (.constant (constU8 7)))))
        , translateStmt (mkStmt (.assign (local_ 0)
            (.binaryOp .div (.copy (local_ 1)) (.constant (constU8 divisor)))))
        , translateStmt (mkStmt (.storageDead 1)) ] := hstmt
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hstmt'
    rcases hstmt' with rfl | rfl | rfl | rfl
    · trivial
    · rfl
    · rfl
    · trivial
  refine ⟨hfree, step_LM2_3_eq_of_bodyFree ?_ ()⟩
  intro frame hcf
  rw [stack_currentFrame?_singleton (miriInit divisor).stack (miriFrame divisor) rfl] at hcf
  injection hcf with hf
  subst hf
  exact hfree

/-! ## 12. Witness 11: Upcast Field-Write, Move & Storage Lifecycle (`bb15`) -/

def lm23Bb15S1 : MachineState :=
  { frame := { blockIdx := 15, stmtIdx := 1,
               locals := [.uninit, .init (.aggregate 1 [.scalar ⟨42, 4⟩]),
                          .uninit, .uninit, .dead] }
    memory := (initMachineState lm23Body []).memory }

def lm23Bb15S2 : MachineState :=
  { frame := { blockIdx := 15, stmtIdx := 2,
               locals := [.uninit, .init (.aggregate 2 [.scalar ⟨42, 4⟩]),
                          .uninit, .uninit, .dead] }
    memory := (initMachineState lm23Body []).memory }

def lm23Bb15S3 : MachineState :=
  { frame := { blockIdx := 15, stmtIdx := 3,
               locals := [.uninit,
                          .init (.aggregate 2 [.scalar ⟨42, 4⟩, .scalar ⟨99, 8⟩]),
                          .uninit, .uninit, .dead] }
    memory := (initMachineState lm23Body []).memory }

def lm23Bb15S4 : MachineState :=
  { frame := { blockIdx := 15, stmtIdx := 4,
               locals := [.uninit,
                          .init (.aggregate 2 [.scalar ⟨42, 4⟩, .scalar ⟨99, 8⟩]),
                          .uninit, .uninit, .uninit] }
    memory := (initMachineState lm23Body []).memory }

def lm23Bb15S5 : MachineState :=
  { frame := { blockIdx := 15, stmtIdx := 5,
               locals := [.uninit, .uninit, .uninit, .uninit,
                          .init (.aggregate 2 [.scalar ⟨42, 4⟩, .scalar ⟨99, 8⟩])] }
    memory := (initMachineState lm23Body []).memory }

def lm23Bb15S6 : MachineState :=
  { frame := { blockIdx := 15, stmtIdx := 6,
               locals := [.uninit, .dead, .uninit, .uninit,
                          .init (.aggregate 2 [.scalar ⟨42, 4⟩, .scalar ⟨99, 8⟩])] }
    memory := (initMachineState lm23Body []).memory }

def lm23Bb15S7 : MachineState :=
  { frame := { blockIdx := 15, stmtIdx := 7,
               locals := [.init (.scalar ⟨99, 8⟩), .dead, .uninit, .uninit,
                          .init (.aggregate 2 [.scalar ⟨42, 4⟩, .scalar ⟨99, 8⟩])] }
    memory := (initMachineState lm23Body []).memory }

def lm23Bb15S8 : MachineState :=
  { frame := { blockIdx := 15, stmtIdx := 8,
               locals := [.init (.scalar ⟨99, 8⟩), .dead, .uninit, .uninit, .dead] }
    memory := (initMachineState lm23Body []).memory }

theorem lm23_bb15_a1 : stepMirFn lm23Body (lm23InitAnneal 15) = .step lm23Bb15S1 := rfl
theorem lm23_bb15_a2 : stepMirFn lm23Body lm23Bb15S1 = .step lm23Bb15S2 := rfl
theorem lm23_bb15_a3 : stepMirFn lm23Body lm23Bb15S2 = .step lm23Bb15S3 := rfl
theorem lm23_bb15_a4 : stepMirFn lm23Body lm23Bb15S3 = .step lm23Bb15S4 := rfl
theorem lm23_bb15_a5 : stepMirFn lm23Body lm23Bb15S4 = .step lm23Bb15S5 := rfl
theorem lm23_bb15_a6 : stepMirFn lm23Body lm23Bb15S5 = .step lm23Bb15S6 := rfl
theorem lm23_bb15_a7 : stepMirFn lm23Body lm23Bb15S6 = .step lm23Bb15S7 := rfl
theorem lm23_bb15_a8 : stepMirFn lm23Body lm23Bb15S7 = .step lm23Bb15S8 := rfl
theorem lm23_bb15_a9 :
    stepMirFn lm23Body lm23Bb15S8 =
      .retNormal (.scalar ⟨99, 8⟩) (initMachineState lm23Body []).memory := rfl

/-- **Witness 11 (`wit_lm2_3_upcast_field_write_move_and_storage_lifecycle`)**:
End-to-end 9-step lockstep execution exercising Rustc's lowered multi-variant
enum initialization, move, and storage-lifecycle sequence:
1. `_1 = Lm23Enum::V1(42_u32)` (`allocBudget: 2 -> 1`,
   `EnumLocalByteUninit m₁ 1 8`),
2. `SetDiscriminant(_1, 2)` (upcasting `V1 -> V2` with trailing `V2.1` absent),
3. `((_1 as Some("V2") 2).1 : u64) = 99_u64`
   (`step_downcast_field_write_simulation` initializing missing `V2.1`),
4. `StorageLive(_4)` (`step_storageLive_LM2_3_simulation` activating `_4`),
5. `_4 = move _1` (`step_enum_copy_move_simulation` copying bytes + `InitMask`
   into `_4`'s fresh allocation `allocBudget: 1 -> 0` and leaving `_1` immediate
   uninitialized),
6. `StorageDead(_1)` (`step_storageDead_LM2_3_simulation` marking `_1` dead),
7. `_0 = move ((_4 as Some("V2") 2).1 : u64)`
   (`evalProjection_downcast_field_simulation` reading `99_u64` from `_4`),
8. `StorageDead(_4)` (`step_storageDead_LM2_3_simulation` deallocating `_4`'s
   backing stack allocation),
9. `return` (`step_return_scalar_lm2_3_simulation` returning `99_u64` with empty
   call stack). -/
theorem wit_lm2_3_upcast_field_write_move_and_storage_lifecycle :
    ∃ (m₁ m₂ m₃ m₄ m₅ m₆ m₇ m₈ m₉ : AnnealStepState)
      (imm0 : Miri.Interpreter.Immediate AnnealProv),
      Miri.Interpreter.Step.step lm23Hooks () (lm23InitMiri 15) = (m₁, .ok true) ∧
      StateRelLM2_3 lm23Body lm23Env 1 lm23Bb15S1 m₁ ∧
      Miri.Interpreter.Step.step lm23Hooks () m₁ = (m₂, .ok true) ∧
      StateRelLM2_3 lm23Body lm23Env 1 lm23Bb15S2 m₂ ∧
      Miri.Interpreter.Step.step lm23Hooks () m₂ = (m₃, .ok true) ∧
      StateRelLM2_3 lm23Body lm23Env 1 lm23Bb15S3 m₃ ∧
      Miri.Interpreter.Step.step lm23Hooks () m₃ = (m₄, .ok true) ∧
      StateRelLM2_3 lm23Body lm23Env 1 lm23Bb15S4 m₄ ∧
      Miri.Interpreter.Step.step lm23Hooks () m₄ = (m₅, .ok true) ∧
      StateRelLM2_3 lm23Body lm23Env 0 lm23Bb15S5 m₅ ∧
      IsImmediateStepLocal m₅ 1 ∧
      Miri.Interpreter.Step.step lm23Hooks () m₅ = (m₆, .ok true) ∧
      StateRelLM2_3 lm23Body lm23Env 0 lm23Bb15S6 m₆ ∧
      Miri.Interpreter.Step.step lm23Hooks () m₆ = (m₇, .ok true) ∧
      StateRelLM2_3 lm23Body lm23Env 0 lm23Bb15S7 m₇ ∧
      Miri.Interpreter.Step.step lm23Hooks () m₇ = (m₈, .ok true) ∧
      StateRelLM2_3 lm23Body lm23Env 0 lm23Bb15S8 m₈ ∧
      Miri.Interpreter.Step.step lm23Hooks () m₈ = (m₉, .ok true) ∧
      annealControlHooks.returnOperand () m₈ = (m₈, .ok (.immediate imm0)) ∧
      ImmediateRel lm23U64Ty lm23Layouts (.scalar ⟨99, 8⟩) imm0 ∧
      m₉.stack.frames = #[] := by
  -- Step 1: _1 = Lm23Enum::V1(42_u32)
  obtain ⟨m₁, hm₁, hst₁, hu₁, himm₁⟩ :=
    lm23_step_agg_v1_at (b := 15) (budget := 1) (by decide) rfl rfl lm23_bb15_a1
  -- Step 2: SetDiscriminant(_1, 2) (V1 -> V2 upcast)
  obtain ⟨hrel₂, _, himm₂_fn⟩ := step_setDiscriminant_simulation
    hst₁ lm23_phase lm23_env_valid rfl rfl rfl
    (dstDecl := lm23Decl lm23EnumTy) rfl rfl (by decide)
    (by intro h; cases h)
    (fun v_act _ fieldVals hsl i hi => by
      injection hsl with hs; injection hs with hv; injection hv with hv_eq hfv_eq
      subst hv_eq hfv_eq
      have hi' : i < 2 := hi
      match i with
      | 0 => exact Or.inl ⟨by decide +revert, rfl⟩
      | 1 => exact Or.inr ⟨rfl, 8, by decide +revert, by decide +revert, hu₁⟩
      | _ + 2 => omega)
  rw [lm23_bb15_a2] at hrel₂
  obtain ⟨m₂, hm₂, hst₂⟩ := stepRelLM2_3_inv_step hrel₂
  have himm₂_0 : IsImmediateStepLocal m₂ 0 := by
    simpa [hm₂] using himm₂_fn 0 (himm₁ 0 (by decide))
  -- Step 3: ((_1 as Some("V2") 2).1 : u64) = 99_u64 (initializes missing V2.1!)
  have hsim₃ := step_downcast_field_write_simulation
    hst₂ lm23_phase lm23_env_valid rfl rfl rfl
    (dstDecl := lm23Decl lm23EnumTy) rfl rfl (by decide) (by decide) rfl
    (fun tf _ => lm23_constU64_wt 99 (by decide) tf)
    (Or.inr ⟨[.scalar ⟨42, 4⟩], rfl, by decide⟩)
  dsimp only at hsim₃
  rcases hsim₃ with ⟨hrel₃, hpost₃⟩
  rw [lm23_bb15_a3] at hrel₃
  obtain ⟨m₃, hm₃, hst₃⟩ := stepRelLM2_3_inv_step hrel₃
  have hno₃ : ∀ msg, (Miri.Interpreter.Step.step lm23Hooks () m₂).2 ≠
      .error (.undefinedBehavior msg) := by
    rw [hm₃]; intro _ h; cases h
  have himm₃_0 : IsImmediateStepLocal m₃ 0 := by
    simpa [hm₃] using (hpost₃ hno₃).2 0 himm₂_0
  -- Step 4: StorageLive(_4)
  have hsim₄ := step_storageLive_LM2_3_simulation
    hst₃ lm23_phase rfl rfl (decl := lm23Decl lm23EnumTy) rfl
  dsimp only at hsim₄
  rcases hsim₄ with ⟨hrel₄, _, _, himm₄_fn⟩
  rw [lm23_bb15_a4] at hrel₄
  obtain ⟨m₄, hm₄, hst₄⟩ := stepRelLM2_3_inv_step hrel₄
  have himm₄_0 : IsImmediateStepLocal m₄ 0 := by
    simpa [hm₄] using himm₄_fn 0 himm₃_0
  -- Step 5: _4 = move _1 (allocBudget: 1 -> 0; _1 becomes immediate uninit!)
  have hsim₅ := step_enum_copy_move_simulation
    hst₄ lm23_phase lm23_env_valid rfl rfl (isMove := true) rfl (by decide)
    (srcDecl := lm23Decl lm23EnumTy) (dstDecl := lm23Decl lm23EnumTy)
    rfl rfl rfl rfl (by intro h; cases h)
  dsimp only at hsim₅
  rcases hsim₅ with ⟨hrel₅, hpost₅⟩
  rw [lm23_bb15_a5] at hrel₅
  obtain ⟨m₅, hm₅, hst₅⟩ := stepRelLM2_3_inv_step hrel₅
  have hno₅ : ∀ msg, (Miri.Interpreter.Step.step lm23Hooks () m₄).2 ≠
      .error (.undefinedBehavior msg) := by
    rw [hm₅]; intro _ h; cases h
  have himm₅_1 : IsImmediateStepLocal m₅ 1 := by
    simpa [hm₅] using (hpost₅ hno₅).1 rfl
  have himm₅_0 : IsImmediateStepLocal m₅ 0 := by
    simpa [hm₅] using (hpost₅ hno₅).2.2.2 0 (by decide) himm₄_0
  -- Step 6: StorageDead(_1)
  have hsim₆ := step_storageDead_LM2_3_simulation
    hst₅ lm23_phase rfl rfl (decl := lm23Decl lm23EnumTy) rfl (by decide)
  dsimp only at hsim₆
  rcases hsim₆ with ⟨hrel₆, _, himm₆_fn⟩
  rw [lm23_bb15_a6] at hrel₆
  obtain ⟨m₆, hm₆, hst₆⟩ := stepRelLM2_3_inv_step hrel₆
  have himm₆_0 : IsImmediateStepLocal m₆ 0 := by
    simpa [hm₆] using himm₆_fn 0 himm₅_0
  -- Step 7: _0 = move ((_4 as Some("V2") 2).1 : u64)
  obtain ⟨hrel₇, _, himm₇_fn⟩ := evalProjection_downcast_field_simulation
    hst₆ lm23_phase lm23_env_valid rfl rfl (isMove := true) rfl
    (srcDecl := lm23Decl lm23EnumTy) (dstDecl := lm23Decl lm23U64Ty)
    rfl rfl rfl (by decide) (by decide) rfl rfl himm₆_0
    (fun v_act _ hsl hne => by
      injection hsl with hs; injection hs with hv; injection hv with hv_eq _
      exact absurd hv_eq hne)
  rw [lm23_bb15_a7] at hrel₇
  obtain ⟨m₇, hm₇, hst₇⟩ := stepRelLM2_3_inv_step hrel₇
  have himm₇_0 : IsImmediateStepLocal m₇ 0 := by
    simpa [hm₇] using himm₇_fn 0 himm₆_0
  -- Step 8: StorageDead(_4) (deallocates _4's indirect enum stack slot!)
  have hsim₈ := step_storageDead_LM2_3_simulation
    hst₇ lm23_phase rfl rfl (decl := lm23Decl lm23EnumTy) rfl (by decide)
  dsimp only at hsim₈
  rcases hsim₈ with ⟨hrel₈, _, himm₈_fn⟩
  rw [lm23_bb15_a8] at hrel₈
  obtain ⟨m₈, hm₈, hst₈⟩ := stepRelLM2_3_inv_step hrel₈
  have himm₈_0 : IsImmediateStepLocal m₈ 0 := by
    simpa [hm₈] using himm₈_fn 0 himm₇_0
  -- Step 9: return 99_u64
  have hrel₉ := step_return_scalar_lm2_3_simulation
    hst₈ lm23_env_valid lm23_phase rfl rfl rfl rfl rfl
    (decl0 := lm23Decl lm23U64Ty) rfl lm23_isPrim_u64 himm₈_0
  rw [lm23_bb15_a9] at hrel₉
  obtain ⟨d0, imm0, m₉, hm₉, hd0, hret_op, himm_rel, hm₉_eq⟩ :=
    stepRelLM2_3_inv_retNormal hrel₉
  have hd0_eq : d0 = lm23Decl lm23U64Ty := by
    simpa [lm23Body, get?] using hd0.symm
  subst hd0_eq
  refine ⟨m₁, m₂, m₃, m₄, m₅, m₆, m₇, m₈, m₉, imm0,
    hm₁, hst₁, hm₂, hst₂, hm₃, hst₃, hm₄, hst₄,
    hm₅, hst₅, himm₅_1, hm₆, hst₆, hm₇, hst₇, hm₈, hst₈,
    hm₉, hret_op, himm_rel, ?_⟩
  rw [hm₉_eq]

/-! ## 13. Witness 12: Downcast-Write & Enum Copy/Move UB (`bb16..bb18`) -/

def lm23Bb18S1 : MachineState :=
  { frame := { blockIdx := 18, stmtIdx := 1,
               locals := [.uninit, .uninit, .uninit, .uninit, .uninit] }
    memory := (initMachineState lm23Body []).memory }

theorem lm23_bb16_ub : stepMirFn lm23Body (lm23InitAnneal 16) = .fail .ub := rfl
theorem lm23_bb17_ub : stepMirFn lm23Body (lm23InitAnneal 17) = .fail .ub := rfl
theorem lm23_bb18_a1 : stepMirFn lm23Body (lm23InitAnneal 18) = .step lm23Bb18S1 := rfl
theorem lm23_bb18_ub : stepMirFn lm23Body lm23Bb18S1 = .fail .ub := rfl

/-- **Witness 12 (`wit_lm2_3_copy_move_and_downcast_write_ub`)**:
Lockstep undefined-behavior simulation across:
1. `bb16`: `((_4 as Some("V1") 1).0 : u32) = 7_u32` on `.dead` `_4`,
2. `bb17`: `_1 = copy _4` on `.dead` `_4`,
3. `bb18`: `StorageLive(_4)` followed by `_4 = move _1` on `.uninit` `_1`. -/
theorem wit_lm2_3_copy_move_and_downcast_write_ub :
    (∃ m₁ msg₁,
      stepMirFn lm23Body (lm23InitAnneal 16) = .fail .ub ∧
      Miri.Interpreter.Step.step lm23Hooks () (lm23InitMiri 16) =
        (m₁, .error (.undefinedBehavior msg₁))) ∧
    (∃ m₂ msg₂,
      stepMirFn lm23Body (lm23InitAnneal 17) = .fail .ub ∧
      Miri.Interpreter.Step.step lm23Hooks () (lm23InitMiri 17) =
        (m₂, .error (.undefinedBehavior msg₂))) ∧
    (∃ m₃ m₄ msg₃,
      stepMirFn lm23Body (lm23InitAnneal 18) = .step lm23Bb18S1 ∧
      Miri.Interpreter.Step.step lm23Hooks () (lm23InitMiri 18) = (m₃, .ok true) ∧
      StateRelLM2_3 lm23Body lm23Env 1 lm23Bb18S1 m₃ ∧
      stepMirFn lm23Body lm23Bb18S1 = .fail .ub ∧
      Miri.Interpreter.Step.step lm23Hooks () m₃ =
        (m₄, .error (.undefinedBehavior msg₃))) := by
  refine ⟨?_, ?_, ?_⟩
  · have hsim := step_downcast_field_write_simulation
      (lm23_init_stateRelLM2_3 16 0 (by decide)) lm23_phase lm23_env_valid
      rfl rfl rfl (dstDecl := lm23Decl lm23EnumTy) rfl rfl (by decide) (by decide) rfl
      (fun tf _ => lm23_constU32_wt 7 (by decide) tf) (Or.inl rfl)
    dsimp only at hsim
    rcases hsim with ⟨hrel, _⟩
    rw [lm23_bb16_ub] at hrel
    obtain ⟨m₁, msg₁, hm₁⟩ := stepRelLM2_3_inv_ub hrel
    exact ⟨m₁, msg₁, lm23_bb16_ub, hm₁⟩
  · have hsim := step_enum_copy_move_simulation
      (lm23_init_stateRelLM2_3 17 1 (by decide)) lm23_phase lm23_env_valid
      rfl rfl (isMove := false) rfl (by decide)
      (srcDecl := lm23Decl lm23EnumTy) (dstDecl := lm23Decl lm23EnumTy)
      rfl rfl rfl rfl (by intro h; cases h)
    dsimp only at hsim
    rcases hsim with ⟨hrel, _⟩
    rw [lm23_bb17_ub] at hrel
    obtain ⟨m₂, msg₂, hm₂⟩ := stepRelLM2_3_inv_ub hrel
    exact ⟨m₂, msg₂, lm23_bb17_ub, hm₂⟩
  · have hsim₁ := step_storageLive_LM2_3_simulation
      (lm23_init_stateRelLM2_3 18 1 (by decide)) lm23_phase
      rfl rfl (decl := lm23Decl lm23EnumTy) rfl
    dsimp only at hsim₁
    rcases hsim₁ with ⟨hrel₁, _, _, himm₁_fn⟩
    rw [lm23_bb18_a1] at hrel₁
    obtain ⟨m₃, hm₃, hst₁⟩ := stepRelLM2_3_inv_step hrel₁
    have himm₃_1 : IsImmediateStepLocal m₃ 1 := by
      simpa [hm₃] using himm₁_fn 1 (lm23_init_imm 18 1)
    have hsim₂ := step_enum_copy_move_simulation
      hst₁ lm23_phase lm23_env_valid rfl rfl (isMove := true) rfl (by decide)
      (srcDecl := lm23Decl lm23EnumTy) (dstDecl := lm23Decl lm23EnumTy)
      rfl rfl rfl rfl (fun _ => himm₃_1)
    dsimp only at hsim₂
    rcases hsim₂ with ⟨hrel₂, _⟩
    rw [lm23_bb18_ub] at hrel₂
    obtain ⟨m₄, msg₃, hm₄⟩ := stepRelLM2_3_inv_ub hrel₂
    exact ⟨m₃, m₄, msg₃, lm23_bb18_a1, hm₃, hst₁, lm23_bb18_ub, hm₄⟩

/-! ## 14. Witness 13: Inactive Downcast-Write Divergence (`bb19`) -/

def lm23Bb19S1 : MachineState :=
  { frame := { blockIdx := 19, stmtIdx := 1,
               locals := [.uninit, .init (.aggregate 1 [.scalar ⟨42, 4⟩]),
                          .uninit, .uninit, .dead] }
    memory := (initMachineState lm23Body []).memory }

theorem lm23_bb19_a1 : stepMirFn lm23Body (lm23InitAnneal 19) = .step lm23Bb19S1 := rfl

/-- **Witness 13 (`wit_lm2_3_downcast_write_inactive_divergence`)**:
After `_1 = Lm23Enum::V1(42_u32)`, writing `((_1 as Some("V2") 2).1 : u64) = 99`
without first executing `SetDiscriminant(_1, 2)` causes Anneal's value-tree
`writeProjectedValue` to fail with `.fail .ub` (`variantIdx = 2 ≠ 1 = v_act`),
while vendored `lean-miri`'s byte-offset `projectDowncast` + `projectField`
writes `99_u64` into `[8, 16)` and steps `(m₂, .ok true)`. -/
theorem wit_lm2_3_downcast_write_inactive_divergence :
    ∃ (m₁ m₂ : AnnealStepState),
      stepMirFn lm23Body (lm23InitAnneal 19) = .step lm23Bb19S1 ∧
      Miri.Interpreter.Step.step lm23Hooks () (lm23InitMiri 19) = (m₁, .ok true) ∧
      StateRelLM2_3 lm23Body lm23Env 0 lm23Bb19S1 m₁ ∧
      stepMirFn lm23Body lm23Bb19S1 = .fail .ub ∧
      Miri.Interpreter.Step.step lm23Hooks () m₁ = (m₂, .ok true) := by
  obtain ⟨m₁, hm₁, hst₁, _, _⟩ :=
    lm23_step_agg_v1_at (b := 19) (budget := 0) (by decide) rfl rfl lm23_bb19_a1
  obtain ⟨ha_ub, m₂, hm₂⟩ := step_downcast_field_write_inactive_divergence
    hst₁ lm23_phase lm23_env_valid rfl rfl rfl
    (dstDecl := lm23Decl lm23EnumTy) rfl rfl (by decide) (by decide) rfl
    (fun tf _ => lm23_constU64_wt 99 (by decide) tf)
    (by intro h; cases h) rfl (by decide)
  exact ⟨m₁, m₂, lm23_bb19_a1, hm₁, hst₁, ha_ub, hm₂⟩

/-! ## 15. Witness 14: Uninit Downcast-Write Divergence (`bb20`) -/

/-- **Witness 14 (`wit_lm2_3_downcast_write_uninit_divergence`)**:
When `_1` is `.uninit`, writing `((_1 as Some("V1") 1).0 : u32) = 42_u32`
without first initializing `_1` via `Aggregate` or `SetDiscriminant` fails with
`.fail .ub` in Anneal's value-tree `writeProjectedValue`, whereas vendored
`lean-miri`'s byte-offset `projectDowncast` + `projectField` allocates `_1`'s
backing stack slot, writes `42_u32` at offset `4`, and steps `(m₁, .ok true)`
(`step_downcast_field_write_uninit_divergence`). -/
theorem wit_lm2_3_downcast_write_uninit_divergence :
    ∃ (m₁ : AnnealStepState),
      stepMirFn lm23Body (lm23InitAnneal 20) = .fail .ub ∧
      Miri.Interpreter.Step.step lm23Hooks () (lm23InitMiri 20) =
        (m₁, .ok true) := by
  obtain ⟨ha_ub, m₁, hm₁⟩ := step_downcast_field_write_uninit_divergence
    (lm23_init_stateRelLM2_3 20 1 (by decide)) lm23_phase lm23_env_valid
    rfl rfl rfl (dstDecl := lm23Decl lm23EnumTy) rfl rfl (by decide) (by decide) rfl
    (fun tf _ => lm23_constU32_wt 42 (by decide) tf)
    (by intro h; cases h) rfl
  exact ⟨m₁, ha_ub, hm₁⟩

/-! ## 16. Witness 15: Field Write, Self-Move & Copy Overwrite (`bb21`) -/

def lm23Bb21S1 : MachineState :=
  { frame := { blockIdx := 21, stmtIdx := 1,
               locals := [.uninit, .init (.aggregate 1 [.scalar ⟨42, 4⟩]),
                          .uninit, .uninit, .dead] }
    memory := (initMachineState lm23Body []).memory }

def lm23Bb21S2 : MachineState :=
  { frame := { blockIdx := 21, stmtIdx := 2,
               locals := [.uninit, .init (.aggregate 1 [.scalar ⟨77, 4⟩]),
                          .uninit, .uninit, .dead] }
    memory := (initMachineState lm23Body []).memory }

def lm23Bb21S3 : MachineState :=
  { frame := { blockIdx := 21, stmtIdx := 3,
               locals := [.uninit, .init (.aggregate 1 [.scalar ⟨77, 4⟩]),
                          .uninit, .uninit, .dead] }
    memory := (initMachineState lm23Body []).memory }

def lm23Bb21S4 : MachineState :=
  { frame := { blockIdx := 21, stmtIdx := 4,
               locals := [.uninit, .init (.aggregate 1 [.scalar ⟨77, 4⟩]),
                          .uninit, .uninit, .uninit] }
    memory := (initMachineState lm23Body []).memory }

def lm23Bb21S5 : MachineState :=
  { frame := { blockIdx := 21, stmtIdx := 5,
               locals := [.uninit, .init (.aggregate 1 [.scalar ⟨77, 4⟩]),
                          .uninit, .uninit, .init (.aggregate 0 [])] }
    memory := (initMachineState lm23Body []).memory }

def lm23Bb21S6 : MachineState :=
  { frame := { blockIdx := 21, stmtIdx := 6,
               locals := [.uninit, .init (.aggregate 1 [.scalar ⟨77, 4⟩]),
                          .uninit, .uninit,
                          .init (.aggregate 1 [.scalar ⟨77, 4⟩])] }
    memory := (initMachineState lm23Body []).memory }

def lm23Bb21S7 : MachineState :=
  { frame := { blockIdx := 21, stmtIdx := 7,
               locals := [.uninit, .init (.aggregate 1 [.scalar ⟨77, 4⟩]),
                          .uninit, .init (.scalar ⟨77, 4⟩),
                          .init (.aggregate 1 [.scalar ⟨77, 4⟩])] }
    memory := (initMachineState lm23Body []).memory }

def lm23Bb21S8 : MachineState :=
  { frame := { blockIdx := 21, stmtIdx := 8,
               locals := [.uninit, .init (.aggregate 1 [.scalar ⟨77, 4⟩]),
                          .uninit, .init (.scalar ⟨77, 4⟩), .dead] }
    memory := (initMachineState lm23Body []).memory }

theorem lm23_bb21_a1 : stepMirFn lm23Body (lm23InitAnneal 21) = .step lm23Bb21S1 := rfl
theorem lm23_bb21_a2 : stepMirFn lm23Body lm23Bb21S1 = .step lm23Bb21S2 := rfl
theorem lm23_bb21_a3 : stepMirFn lm23Body lm23Bb21S2 = .step lm23Bb21S3 := rfl
theorem lm23_bb21_a4 : stepMirFn lm23Body lm23Bb21S3 = .step lm23Bb21S4 := rfl
theorem lm23_bb21_a5 : stepMirFn lm23Body lm23Bb21S4 = .step lm23Bb21S5 := rfl
theorem lm23_bb21_a6 : stepMirFn lm23Body lm23Bb21S5 = .step lm23Bb21S6 := rfl
theorem lm23_bb21_a7 : stepMirFn lm23Body lm23Bb21S6 = .step lm23Bb21S7 := rfl
theorem lm23_bb21_a8 : stepMirFn lm23Body lm23Bb21S7 = .step lm23Bb21S8 := rfl

/-- **Witness 15 (`wit_lm2_3_field_overwrite_self_move_and_copy_overwrite`)**:
End-to-end 8-step lockstep execution exercising the remaining branches of
`step_downcast_field_write_simulation`, `step_enum_self_move_simulation`, and
`step_enum_copy_move_simulation`:
1. `_1 = Lm23Enum::V1(42_u32)` (`allocBudget: 4 -> 3`),
2. `((_1 as Some("V1") 1).0 : u32) = 77_u32`
   (`step_downcast_field_write_simulation` overwriting existing active field
   `0 < fieldVals.length`),
3. `_1 = move _1` (`step_enum_self_move_simulation` deinitializing `_1` during
   operand read and copying into a fresh stack slot `allocBudget: 3 -> 2`),
4. `StorageLive(_4)` (`step_storageLive_LM2_3_simulation`),
5. `_4 = Lm23Enum::V0` (`evalRvalue_aggregate_enum_simulation` allocating `_4`'s
   indirect stack slot `allocBudget: 2 -> 1`),
6. `_4 = copy _1` (`step_enum_copy_move_simulation` with `isMove = false`
   overwriting `_4`'s existing indirect stack allocation in place),
7. `_3 = copy ((_4 as Some("V1") 1).0 : u32)`
   (`evalProjection_downcast_field_simulation` reading `77_u32` from `_4`),
8. `StorageDead(_4)` (`step_storageDead_LM2_3_simulation`). -/
theorem wit_lm2_3_field_overwrite_self_move_and_copy_overwrite :
    ∃ (m₁ m₂ m₃ m₄ m₅ m₆ m₇ m₈ : AnnealStepState),
      Miri.Interpreter.Step.step lm23Hooks () (lm23InitMiri 21) = (m₁, .ok true) ∧
      StateRelLM2_3 lm23Body lm23Env 3 lm23Bb21S1 m₁ ∧
      Miri.Interpreter.Step.step lm23Hooks () m₁ = (m₂, .ok true) ∧
      StateRelLM2_3 lm23Body lm23Env 3 lm23Bb21S2 m₂ ∧
      Miri.Interpreter.Step.step lm23Hooks () m₂ = (m₃, .ok true) ∧
      StateRelLM2_3 lm23Body lm23Env 2 lm23Bb21S3 m₃ ∧
      Miri.Interpreter.Step.step lm23Hooks () m₃ = (m₄, .ok true) ∧
      StateRelLM2_3 lm23Body lm23Env 2 lm23Bb21S4 m₄ ∧
      Miri.Interpreter.Step.step lm23Hooks () m₄ = (m₅, .ok true) ∧
      StateRelLM2_3 lm23Body lm23Env 1 lm23Bb21S5 m₅ ∧
      Miri.Interpreter.Step.step lm23Hooks () m₅ = (m₆, .ok true) ∧
      StateRelLM2_3 lm23Body lm23Env 0 lm23Bb21S6 m₆ ∧
      Miri.Interpreter.Step.step lm23Hooks () m₆ = (m₇, .ok true) ∧
      StateRelLM2_3 lm23Body lm23Env 0 lm23Bb21S7 m₇ ∧
      Miri.Interpreter.Step.step lm23Hooks () m₇ = (m₈, .ok true) ∧
      StateRelLM2_3 lm23Body lm23Env 0 lm23Bb21S8 m₈ := by
  -- Step 1: _1 = Lm23Enum::V1(42_u32) (budget: 4 -> 3)
  obtain ⟨m₁, hm₁, hst₁, _, himm₁⟩ :=
    lm23_step_agg_v1_at (b := 21) (budget := 3) (by decide) rfl rfl lm23_bb21_a1
  -- Step 2: ((_1 as Some("V1") 1).0 : u32) = 77_u32 (0 < fieldVals.length!)
  have hsim₂ := step_downcast_field_write_simulation
    hst₁ lm23_phase lm23_env_valid rfl rfl rfl
    (dstDecl := lm23Decl lm23EnumTy) rfl rfl (by decide) (by decide) rfl
    (fun tf _ => lm23_constU32_wt 77 (by decide) tf)
    (Or.inr ⟨[.scalar ⟨42, 4⟩], rfl, by decide⟩)
  dsimp only at hsim₂
  rcases hsim₂ with ⟨hrel₂, hpost₂⟩
  rw [lm23_bb21_a2] at hrel₂
  obtain ⟨m₂, hm₂, hst₂⟩ := stepRelLM2_3_inv_step hrel₂
  have hno₂ : ∀ msg, (Miri.Interpreter.Step.step lm23Hooks () m₁).2 ≠
      .error (.undefinedBehavior msg) := by
    rw [hm₂]; intro _ h; cases h
  have himm₂_3 : IsImmediateStepLocal m₂ 3 := by
    simpa [hm₂] using (hpost₂ hno₂).2 3 (himm₁ 3 (by decide))
  -- Step 3: _1 = move _1 (budget: 2 -> 1)
  have hsim₃ := step_enum_self_move_simulation
    hst₂ lm23_phase lm23_env_valid rfl rfl rfl
    (decl := lm23Decl lm23EnumTy) rfl rfl (by intro h; cases h)
  dsimp only at hsim₃
  rcases hsim₃ with ⟨hrel₃, hpost₃⟩
  rw [lm23_bb21_a3] at hrel₃
  obtain ⟨m₃, hm₃, hst₃⟩ := stepRelLM2_3_inv_step hrel₃
  have hno₃ : ∀ msg, (Miri.Interpreter.Step.step lm23Hooks () m₂).2 ≠
      .error (.undefinedBehavior msg) := by
    rw [hm₃]; intro _ h; cases h
  have himm₃_3 : IsImmediateStepLocal m₃ 3 := by
    simpa [hm₃] using (hpost₃ hno₃).2 3 (by decide) himm₂_3
  -- Step 4: StorageLive(_4)
  have hsim₄ := step_storageLive_LM2_3_simulation
    hst₃ lm23_phase rfl rfl (decl := lm23Decl lm23EnumTy) rfl
  dsimp only at hsim₄
  rcases hsim₄ with ⟨hrel₄, _, _, himm₄_fn⟩
  rw [lm23_bb21_a4] at hrel₄
  obtain ⟨m₄, hm₄, hst₄⟩ := stepRelLM2_3_inv_step hrel₄
  have himm₄_3 : IsImmediateStepLocal m₄ 3 := by
    simpa [hm₄] using himm₄_fn 3 himm₃_3
  -- Step 5: _4 = Lm23Enum::V0 (budget: 1 -> 0)
  have hsim₅ := evalRvalue_aggregate_enum_simulation
    hst₄ lm23_env_valid lm23_phase rfl rfl rfl
    (dstDecl := lm23Decl lm23EnumTy) rfl
    (tagBytes := 4) (variants := lm23Variants) rfl (by decide) rfl
    (fun _ _ hi _ => by cases hi)
  dsimp only at hsim₅
  rcases hsim₅ with ⟨hrel₅, hpost₅⟩
  rw [lm23_bb21_a5] at hrel₅
  obtain ⟨m₅, hm₅, hst₅⟩ := stepRelLM2_3_inv_step hrel₅
  have hno₅ : ∀ msg, (Miri.Interpreter.Step.step lm23Hooks () m₄).2 ≠
      .error (.undefinedBehavior msg) := by
    rw [hm₅]; intro _ h; cases h
  have himm₅_3 : IsImmediateStepLocal m₅ 3 := by
    simpa [hm₅] using (hpost₅ hno₅).2.2 3 (by decide) himm₄_3
  -- Step 6: _4 = copy _1 (in-place indirect enum overwrite on _4!)
  have hsim₆ := step_enum_copy_move_simulation
    hst₅ lm23_phase lm23_env_valid rfl rfl (isMove := false) rfl (by decide)
    (srcDecl := lm23Decl lm23EnumTy) (dstDecl := lm23Decl lm23EnumTy)
    rfl rfl rfl rfl (by intro h; cases h)
  dsimp only at hsim₆
  rcases hsim₆ with ⟨hrel₆, hpost₆⟩
  rw [lm23_bb21_a6] at hrel₆
  obtain ⟨m₆, hm₆, hst₆⟩ := stepRelLM2_3_inv_step hrel₆
  have hno₆ : ∀ msg, (Miri.Interpreter.Step.step lm23Hooks () m₅).2 ≠
      .error (.undefinedBehavior msg) := by
    rw [hm₆]; intro _ h; cases h
  have himm₆_3 : IsImmediateStepLocal m₆ 3 := by
    simpa [hm₆] using (hpost₆ hno₆).2.2.2 3 (by decide) himm₅_3
  -- Step 7: _3 = copy ((_4 as Some("V1") 1).0 : u32)
  obtain ⟨hrel₇, _, _⟩ := evalProjection_downcast_field_simulation
    hst₆ lm23_phase lm23_env_valid rfl rfl (isMove := false) rfl
    (srcDecl := lm23Decl lm23EnumTy) (dstDecl := lm23Decl lm23U32Ty)
    rfl rfl rfl (by decide) (by decide) rfl rfl himm₆_3
    (fun v_act _ hsl hne => by
      injection hsl with hs; injection hs with hv; injection hv with hv_eq _
      exact absurd hv_eq hne)
  rw [lm23_bb21_a7] at hrel₇
  obtain ⟨m₇, hm₇, hst₇⟩ := stepRelLM2_3_inv_step hrel₇
  -- Step 8: StorageDead(_4)
  have hsim₈ := step_storageDead_LM2_3_simulation
    hst₇ lm23_phase rfl rfl (decl := lm23Decl lm23EnumTy) rfl (by decide)
  dsimp only at hsim₈
  rcases hsim₈ with ⟨hrel₈, _, _⟩
  rw [lm23_bb21_a8] at hrel₈
  obtain ⟨m₈, hm₈, hst₈⟩ := stepRelLM2_3_inv_step hrel₈
  exact ⟨m₁, m₂, m₃, m₄, m₅, m₆, m₇, m₈,
    hm₁, hst₁, hm₂, hst₂, hm₃, hst₃, hm₄, hst₄,
    hm₅, hst₅, hm₆, hst₆, hm₇, hst₇, hm₈, hst₈⟩

/-! ## 17. Witness 16: Self-Copy Dead & Immediate-Uninit UB (`bb22`, `bb23`) -/

def lm23Bb23S1 : MachineState :=
  { frame := { blockIdx := 23, stmtIdx := 1,
               locals := [.uninit, .dead, .uninit, .uninit, .dead] }
    memory := (initMachineState lm23Body []).memory }

theorem lm23_bb22_ub : stepMirFn lm23Body (lm23InitAnneal 22) = .fail .ub := rfl
theorem lm23_bb23_a1 : stepMirFn lm23Body (lm23InitAnneal 23) = .step lm23Bb23S1 := rfl
theorem lm23_bb23_ub : stepMirFn lm23Body lm23Bb23S1 = .fail .ub := rfl

/-- **Witness 16 (`wit_lm2_3_self_copy_dead_and_uninit_ub`)**:
Lockstep undefined-behavior simulation via
`step_enum_self_copy_dead_or_uninit_simulation` across:
1. `bb22`: `_1 = copy _1` when `_1` is immediate `.uninit`,
2. `bb23`: `StorageDead(_1)` followed by `_1 = copy _1` when `_1` is `.dead`. -/
theorem wit_lm2_3_self_copy_dead_and_uninit_ub :
    (∃ m₁ msg₁,
      stepMirFn lm23Body (lm23InitAnneal 22) = .fail .ub ∧
      Miri.Interpreter.Step.step lm23Hooks () (lm23InitMiri 22) =
        (m₁, .error (.undefinedBehavior msg₁))) ∧
    (∃ m₂ m₃ msg₂,
      stepMirFn lm23Body (lm23InitAnneal 23) = .step lm23Bb23S1 ∧
      Miri.Interpreter.Step.step lm23Hooks () (lm23InitMiri 23) = (m₂, .ok true) ∧
      StateRelLM2_3 lm23Body lm23Env 0 lm23Bb23S1 m₂ ∧
      stepMirFn lm23Body lm23Bb23S1 = .fail .ub ∧
      Miri.Interpreter.Step.step lm23Hooks () m₂ =
        (m₃, .error (.undefinedBehavior msg₂))) := by
  refine ⟨?_, ?_⟩
  · have hsim := step_enum_self_copy_dead_or_uninit_simulation
      (lm23_init_stateRelLM2_3 22 0 (by decide)) lm23_phase lm23_env_valid
      rfl rfl rfl (decl := lm23Decl lm23EnumTy) rfl rfl
      (by intro _ h; cases h) (fun _ => lm23_init_imm 22 1)
    dsimp only at hsim
    rcases hsim with ⟨hrel, _⟩
    rw [lm23_bb22_ub] at hrel
    obtain ⟨m₁, msg₁, hm₁⟩ := stepRelLM2_3_inv_ub hrel
    exact ⟨m₁, msg₁, lm23_bb22_ub, hm₁⟩
  · have hsim₁ := step_storageDead_LM2_3_simulation
      (lm23_init_stateRelLM2_3 23 0 (by decide)) lm23_phase
      rfl rfl (decl := lm23Decl lm23EnumTy) rfl (by decide)
    dsimp only at hsim₁
    rcases hsim₁ with ⟨hrel₁, _, _⟩
    rw [lm23_bb23_a1] at hrel₁
    obtain ⟨m₂, hm₂, hst₁⟩ := stepRelLM2_3_inv_step hrel₁
    have hsim₂ := step_enum_self_copy_dead_or_uninit_simulation
      hst₁ lm23_phase lm23_env_valid rfl rfl rfl
      (decl := lm23Decl lm23EnumTy) rfl rfl
      (by intro _ h; cases h) (by intro h; cases h)
    dsimp only at hsim₂
    rcases hsim₂ with ⟨hrel₂, _⟩
    rw [lm23_bb23_ub] at hrel₂
    obtain ⟨m₃, msg₂, hm₃⟩ := stepRelLM2_3_inv_ub hrel₂
    exact ⟨m₂, m₃, msg₂, lm23_bb23_a1, hm₂, hst₁, lm23_bb23_ub, hm₃⟩

/-! ## 18. Witness 17: Whole-Enum Self-Copy Overlap Divergence (`bb24`) -/

def lm23Bb24S1 : MachineState :=
  { frame := { blockIdx := 24, stmtIdx := 1,
               locals := [.uninit, .init (.aggregate 1 [.scalar ⟨42, 4⟩]),
                          .uninit, .uninit, .dead] }
    memory := (initMachineState lm23Body []).memory }

def lm23Bb24S2 : MachineState :=
  { frame := { blockIdx := 24, stmtIdx := 2,
               locals := [.uninit, .init (.aggregate 1 [.scalar ⟨42, 4⟩]),
                          .uninit, .uninit, .dead] }
    memory := (initMachineState lm23Body []).memory }

theorem lm23_bb24_a1 : stepMirFn lm23Body (lm23InitAnneal 24) = .step lm23Bb24S1 := rfl

/-- **Witness 17 (`wit_lm2_3_self_copy_overlap_divergence`)**:
After `_1 = Lm23Enum::V1(42_u32)`, whole-enum self-copy `_1 = copy _1` steps in
Anneal's value-tree semantics to `lm23Bb24S2`, while vendored `lean-miri`
unconditionally diagnoses `"whole-value copy between overlapping ranges"`
(`step_enum_self_copy_overlap_divergence`). -/
theorem wit_lm2_3_self_copy_overlap_divergence :
    ∃ (m₁ m_err : AnnealStepState),
      stepMirFn lm23Body (lm23InitAnneal 24) = .step lm23Bb24S1 ∧
      Miri.Interpreter.Step.step lm23Hooks () (lm23InitMiri 24) = (m₁, .ok true) ∧
      StateRelLM2_3 lm23Body lm23Env 0 lm23Bb24S1 m₁ ∧
      stepMirFn lm23Body lm23Bb24S1 = .step lm23Bb24S2 ∧
      Miri.Interpreter.Step.step lm23Hooks () m₁ =
        (m_err,
          .error
            (.undefinedBehavior "whole-value copy between overlapping ranges")) := by
  obtain ⟨m₁, hm₁, hst₁, _, _⟩ :=
    lm23_step_agg_v1_at (b := 24) (budget := 0) (by decide) rfl rfl lm23_bb24_a1
  obtain ⟨ha_ok, m_err, hm_err⟩ := step_enum_self_copy_overlap_divergence
    hst₁ lm23_phase lm23_env_valid rfl rfl rfl
    (decl := lm23Decl lm23EnumTy) rfl rfl
    (rootVal := .aggregate 1 [.scalar ⟨42, 4⟩]) rfl
  exact ⟨m₁, m_err, lm23_bb24_a1, hm₁, hst₁, ha_ok, hm_err⟩

/-! ## 19. Witness 18: Indirect-Uninit Copy/Move Divergence -/

def lm23Bb25S1 : MachineState :=
  { frame := { blockIdx := 25, stmtIdx := 1,
               locals := [.uninit, .uninit, .uninit, .uninit, .uninit] }
    memory := (initMachineState lm23Body []).memory }

theorem lm23_bb25_a1 : stepMirFn lm23Body (lm23InitAnneal 25) = .step lm23Bb25S1 := rfl

/-- Given any `StateRelLM2_3` state `(s, m)` with `.uninit` `_1` and all other
locals immediate, materializing an uninitialized backing stack slot for `_1`
produces a `StateRelLM2_3` state `(s, m_u)` in `LocalRelLM2_3.enumUninitInd`
(`¬ IsImmediateStepLocal m_u 1`). -/
theorem lm23_materialize_uninitInd {budget : Nat} {s : MachineState}
    {m : AnnealStepState}
    (hst : StateRelLM2_3 lm23Body lm23Env (budget + 1) s m)
    (hs1 : get? s.frame.locals 1 = some .uninit)
    (himm_other : ∀ k, k ≠ 1 → IsImmediateStepLocal m k) :
    ∃ m_u : AnnealStepState,
      StateRelLM2_3 lm23Body lm23Env budget s m_u ∧
      ¬ IsImmediateStepLocal m_u 1 := by
  rcases hst with ⟨topFrame, hframes, hretC, ⟨retLay, hretP⟩, hframe, halloc,
    hcal, hcs, hbor, hprot, hcaller, _⟩
  let wholeLay := translateTy lm23EnumTy lm23Layouts
  have hlt1 : 1 < topFrame.locals.size := by
    rw [hframe.mf_locals_size]; decide
  obtain ⟨rawAlloc, _, hbs0, hlen0, hmut0, hpmap0, hmask0⟩ :=
    tryNew_uninit_of_pow2_le_29 wholeLay.layout.size wholeLay.layout.align.abi
      lm23_validEnumLayout.align_pow2_le
  obtain ⟨mem', newId, hres, _, hlive_eq, hfresh_old, hwm_next, hovf_all⟩ :=
    halloc.of_succ.reserve_step
  let a0 := rawAlloc.withExtra (none : Option Miri.TreeBorrows.BorrowTree)
  let mach_u := stackAllocMachine m.machine mem' newId a0
  let tf_u :=
    { topFrame with
      locals := topFrame.locals.set 1
        ⟨.live (.indirect (stackAllocPlace newId)), some wholeLay⟩ hlt1 }
  let m_u : AnnealStepState := ⟨⟨#[tf_u]⟩, mach_u⟩
  have hfresh : mem'.live.any (fun entry => entry.1 == newId) = false := by
    rw [hlive_eq]; exact hfresh_old
  have hlive_u : LiveAllocEntry mach_u.memory.live newId ⟨.stack, a0⟩ :=
    LiveAllocEntry.of_push_fresh_self ⟨.stack, a0⟩ hfresh
  have hbase_u : mach_u.lookupBaseAddr newId = some (annealStackBaseAddr newId) :=
    lookupBaseAddr_stackAllocMachine_self m.machine mem' newId a0
  have hovf_u := hovf_all _ lm23_validEnumLayout.size_lt_4gib
  have halign_u :=
    annealStackBaseAddr_isAligned newId _ lm23_validEnumLayout.align_pow2_le
  have hlen_a0 : a0.len = a0.byteSize.bytes.toNat := by
    dsimp [a0]; rw [hlen0, ← hbs0]
  have humpr :
      UninitEnumMemRel mach_u lm23EnumTy lm23Layouts 4 lm23Variants
        (stackAllocPlace newId) :=
    .mk newId Miri.Memory.BorTag.one (annealStackBaseAddr newId) ⟨.stack, a0⟩
      lm23_validEnumLayout rfl rfl rfl hlive_u hbase_u rfl hovf_u hmut0 halign_u
      hbs0 hlen_a0 hpmap0 hmask0
  have hdecl1 : get? lm23Body.localDecls 1 = some (lm23Decl lm23EnumTy) := rfl
  have hfr_u : FrameRelLM2_3 lm23Body lm23Env mach_u s.frame tf_u := by
    refine ⟨hframe.body_eq, hframe.location_eq, hframe.af_locals_len, ?_, ?_⟩
    · dsimp [tf_u]; rw [Array.size_set]; exact hframe.mf_locals_size
    · intro j d sl mls hd hsl hm
      dsimp [tf_u] at hm
      by_cases hj : 1 = j
      · subst hj
        rw [hdecl1] at hd
        have hd_eq : d = lm23Decl lm23EnumTy := (Option.some.inj hd).symm
        have hsl_eq : sl = .uninit := by
          rw [hs1] at hsl; exact (Option.some.inj hsl).symm
        rw [Array.getElem?_set_self hlt1] at hm
        have hm_eq :
            mls = ⟨.live (.indirect (stackAllocPlace newId)), some wholeLay⟩ :=
          (Option.some.inj hm).symm
        subst hd_eq hsl_eq hm_eq
        exact .enumUninitInd 4 lm23Variants (stackAllocPlace newId)
          (some wholeLay) rfl
          (fun _ hl => (Option.some.inj (Option.mem_def.mp hl)).symm) humpr
      · rw [Array.getElem?_set_ne _ hj] at hm
        exact (hframe.locals_rel j d sl mls hd hsl hm).of_stackAlloc_other hres
  have hdisj_u : MemoryAllocDisjoint tf_u := by
    intro i j mpi mpj ci cj hij hi hj
    by_cases hi1 : 1 = i
    · subst hi1
      have hj1 : j ≠ 1 := Ne.symm hij
      dsimp [tf_u] at hj
      rw [Array.getElem?_set_ne _ hij] at hj
      exact False.elim (himm_other j hj1 topFrame hframes _ hj mpj rfl)
    · dsimp [tf_u] at hi
      rw [Array.getElem?_set_ne _ hi1] at hi
      exact False.elim (himm_other i (Ne.symm hi1) topFrame hframes _ hi mpi rfl)
  have hnot_imm : ¬ IsImmediateStepLocal m_u 1 := by
    intro himm
    have hget_u :
        tf_u.locals[1]? =
          some ⟨.live (.indirect (stackAllocPlace newId)), some wholeLay⟩ := by
      dsimp [tf_u]; rw [Array.getElem?_set_self hlt1]
    exact himm tf_u rfl _ hget_u (stackAllocPlace newId) rfl
  exact ⟨m_u,
    .mk tf_u rfl hretC ⟨retLay, hretP⟩ hfr_u (Or.inr (hwm_next _))
      hcal hcs hbor hprot hcaller hdisj_u,
    hnot_imm⟩

/-- **Witness 18 (`wit_lm2_3_uninitInd_copy_and_move_divergence`)**:
Constructs concrete `StateRelLM2_3` states with `_1` in
`LocalRelLM2_3.enumUninitInd` (`¬ IsImmediateStepLocal m_u 1`) and certifies all
four `(self vs. distinct) × (copy vs. move)` quadrants of
`step_enum_copy_move_uninitInd_divergence`:
1. `bb22`: self-copy `_1 = copy _1` (contrast Witness 16(1), where immediate
   `_1` in `lm23InitMiri 22` traps in lockstep),
2. `bb26`: self-move `_1 = move _1`,
3. `bb25`: distinct-local copy `_4 = copy _1` after `StorageLive(_4)`,
4. `bb18`: distinct-local move `_4 = move _1` after `StorageLive(_4)` (contrast
   Witness 12(3), where immediate `_1` traps in lockstep). -/
theorem wit_lm2_3_uninitInd_copy_and_move_divergence :
    (∃ m_u1 m₁,
      StateRelLM2_3 lm23Body lm23Env 1 (lm23InitAnneal 22) m_u1 ∧
      ¬ IsImmediateStepLocal m_u1 1 ∧
      stepMirFn lm23Body (lm23InitAnneal 22) = .fail .ub ∧
      Miri.Interpreter.Step.step lm23Hooks () m_u1 = (m₁, .ok true)) ∧
    (∃ m_u2 m₂,
      StateRelLM2_3 lm23Body lm23Env 1 (lm23InitAnneal 26) m_u2 ∧
      ¬ IsImmediateStepLocal m_u2 1 ∧
      stepMirFn lm23Body (lm23InitAnneal 26) = .fail .ub ∧
      Miri.Interpreter.Step.step lm23Hooks () m_u2 = (m₂, .ok true)) ∧
    (∃ m_u3 m₃,
      StateRelLM2_3 lm23Body lm23Env 1 lm23Bb25S1 m_u3 ∧
      ¬ IsImmediateStepLocal m_u3 1 ∧
      stepMirFn lm23Body lm23Bb25S1 = .fail .ub ∧
      Miri.Interpreter.Step.step lm23Hooks () m_u3 = (m₃, .ok true)) ∧
    (∃ m_u4 m₄,
      StateRelLM2_3 lm23Body lm23Env 1 lm23Bb18S1 m_u4 ∧
      ¬ IsImmediateStepLocal m_u4 1 ∧
      stepMirFn lm23Body lm23Bb18S1 = .fail .ub ∧
      Miri.Interpreter.Step.step lm23Hooks () m_u4 = (m₄, .ok true)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨m_u1, hst_u1, hnot_imm1⟩ := lm23_materialize_uninitInd
      (budget := 1) (lm23_init_stateRelLM2_3 22 2 (by decide)) rfl
      (fun k _ => lm23_init_imm 22 k)
    obtain ⟨ha_ub, m₁, hm₁⟩ := step_enum_copy_move_uninitInd_divergence
      hst_u1 lm23_phase lm23_env_valid rfl rfl (isMove := false) rfl
      (srcDecl := lm23Decl lm23EnumTy) (dstDecl := lm23Decl lm23EnumTy)
      rfl rfl rfl rfl rfl hnot_imm1 (by intro h; cases h)
    exact ⟨m_u1, m₁, hst_u1, hnot_imm1, ha_ub, hm₁⟩
  · obtain ⟨m_u2, hst_u2, hnot_imm2⟩ := lm23_materialize_uninitInd
      (budget := 1) (lm23_init_stateRelLM2_3 26 2 (by decide)) rfl
      (fun k _ => lm23_init_imm 26 k)
    obtain ⟨ha_ub, m₂, hm₂⟩ := step_enum_copy_move_uninitInd_divergence
      hst_u2 lm23_phase lm23_env_valid rfl rfl (isMove := true) rfl
      (srcDecl := lm23Decl lm23EnumTy) (dstDecl := lm23Decl lm23EnumTy)
      rfl rfl rfl rfl rfl hnot_imm2 (by intro h; cases h)
    exact ⟨m_u2, m₂, hst_u2, hnot_imm2, ha_ub, hm₂⟩
  · have hsim_sl := step_storageLive_LM2_3_simulation
      (lm23_init_stateRelLM2_3 25 2 (by decide)) lm23_phase
      rfl rfl (decl := lm23Decl lm23EnumTy) rfl
    dsimp only at hsim_sl
    rcases hsim_sl with ⟨hrel_sl, _, _, himm_fn⟩
    rw [lm23_bb25_a1] at hrel_sl
    obtain ⟨m_sl, hm_sl, hst_sl⟩ := stepRelLM2_3_inv_step hrel_sl
    obtain ⟨m_u3, hst_u3, hnot_imm3⟩ := lm23_materialize_uninitInd
      (budget := 1) hst_sl rfl
      (fun k _ => by simpa [hm_sl] using himm_fn k (lm23_init_imm 25 k))
    obtain ⟨ha_ub, m₃, hm₃⟩ := step_enum_copy_move_uninitInd_divergence
      hst_u3 lm23_phase lm23_env_valid rfl rfl (isMove := false) rfl
      (srcDecl := lm23Decl lm23EnumTy) (dstDecl := lm23Decl lm23EnumTy)
      rfl rfl rfl rfl rfl hnot_imm3 (by intro h; cases h)
    exact ⟨m_u3, m₃, hst_u3, hnot_imm3, ha_ub, hm₃⟩
  · have hsim_sl := step_storageLive_LM2_3_simulation
      (lm23_init_stateRelLM2_3 18 2 (by decide)) lm23_phase
      rfl rfl (decl := lm23Decl lm23EnumTy) rfl
    dsimp only at hsim_sl
    rcases hsim_sl with ⟨hrel_sl, _, _, himm_fn⟩
    rw [lm23_bb18_a1] at hrel_sl
    obtain ⟨m_sl, hm_sl, hst_sl⟩ := stepRelLM2_3_inv_step hrel_sl
    obtain ⟨m_u4, hst_u4, hnot_imm4⟩ := lm23_materialize_uninitInd
      (budget := 1) hst_sl rfl
      (fun k _ => by simpa [hm_sl] using himm_fn k (lm23_init_imm 18 k))
    obtain ⟨ha_ub, m₄, hm₄⟩ := step_enum_copy_move_uninitInd_divergence
      hst_u4 lm23_phase lm23_env_valid rfl rfl (isMove := true) rfl
      (srcDecl := lm23Decl lm23EnumTy) (dstDecl := lm23Decl lm23EnumTy)
      rfl rfl rfl rfl rfl hnot_imm4 (by intro h; cases h)
    exact ⟨m_u4, m₄, hst_u4, hnot_imm4, ha_ub, hm₄⟩

/-! ## 20. Witness 19: Root-Frame Enum Return and `enumUninitInd` Boundary -/

theorem stepRelEnumReturnLM2_3_inv_ret {body : CapturedMir} {env : EnumTypeEnv}
    {m : AnnealStepState} {v_act : Nat} {fieldVals : List Value} {mem : Memory}
    {mRes : Miri.Interpreter.StepResult AnnealStepState Bool}
    (h : StepRelEnumReturnLM2_3 body env m
      (.retNormal (.aggregate v_act fieldVals) mem) mRes) :
    ∃ d0 tagBytes variants mp0 m',
      mRes = (m', .ok true) ∧
      get? body.localDecls 0 = some d0 ∧
      env d0.ty = some (tagBytes, variants) ∧
      annealControlHooks.returnOperand () m = (m, .ok (.indirect mp0)) ∧
      EnumMemRel m'.machine d0.ty body.layouts tagBytes variants
        v_act fieldVals mp0 ∧
      m' = { m with stack := ⟨#[]⟩ } := by
  generalize ha :
    MirStepNode.retNormal (.aggregate v_act fieldVals) mem = aRes at h
  cases h with
  | retRootEnum d0 tb vs v₁ fvs mp0 mem₁ m' hd0 henv0 hop0 hemr hm' =>
    dsimp [MirStepNode.retNormal] at ha
    injection ha with hr
    injection hr with hp
    injection hp with hv _
    injection hv with hv_eq hf_eq
    subst hv_eq hf_eq
    exact ⟨d0, tb, vs, mp0, m', rfl, hd0, henv0, hop0, hemr, hm'⟩
  | ub _ _ => cases ha

theorem stepRelEnumReturnLM2_3_inv_ub {body : CapturedMir} {env : EnumTypeEnv}
    {m : AnnealStepState}
    {mRes : Miri.Interpreter.StepResult AnnealStepState Bool}
    (h : StepRelEnumReturnLM2_3 body env m (.fail .ub) mRes) :
    ∃ m' msg, mRes = (m', .error (.undefinedBehavior msg)) := by
  generalize ha : MirStepNode.fail .ub = aRes at h
  cases h with
  | retRootEnum _ _ _ _ _ _ _ _ _ _ _ _ _ => cases ha
  | ub m' msg => exact ⟨m', msg, rfl⟩

def lm23ReturnEnumFnAbi : FnAbi :=
  { args := [], ret := { layout := lm23EnumLayout, mode := .direct },
    conv := .rust, canUnwind := false }

/-- Enum-returning MIR body (`fn() -> Lm23Enum`, `_0 : Lm23Enum`):
* `bb0`: `_0 = Lm23Enum::V2(42_u32, 99_u64); return`;
* `bb1`: `return` (exercising immediate `.uninit` `_0` UB, `.dead` `_0` UB, and
  indirect `enumUninitInd` `_0` return divergence). -/
def lm23ReturnEnumBody : CapturedMir where
  defPath := "lm_2_3_witness::return_enum"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [lm23Decl lm23EnumTy]
  basicBlocks :=
    [ { statements := [lm23AggV2ConstStmt 0 42 99]
        terminator := lm23Term .return_
        isCleanup := false }
    , { statements := []
        terminator := lm23Term .return_
        isCleanup := false } ]
  fnAbi := lm23ReturnEnumFnAbi
  layouts := lm23Layouts
  allocations := []

theorem lm23Ret_phase : ∀ p, lm23ReturnEnumBody.phase ≠ .other p := by
  intro p h; cases h

abbrev lm23RetHooks :=
  annealStepHooksLM2_3 lm23ReturnEnumBody.localDecls lm23ReturnEnumBody.layouts

def lm23RetInitAnneal (b : Nat) : MachineState :=
  { frame := { blockIdx := b, stmtIdx := 0, locals := [.uninit] }
    memory := (initMachineState lm23ReturnEnumBody []).memory }

def lm23RetInitMiriFrame (b : Nat) :
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { body := translateBody lm23ReturnEnumBody
    bodyIdentity := .ofCanonicalIndex 0
    functionInstance := { kind := .Item 0, args := #[] }
    extra := ()
    returnContinuation := .stop false
    returnPlace :=
      .frameLocal 0 0 none (translateTy lm23EnumTy lm23Layouts)
        (.ofAllocationToken 0)
    localsIdentity := .ofAllocationToken 0
    locals := #[{ value := .live (.immediate .uninit), layout := none }]
    vaList := #[]
    trackCallerArg := none
    location := .mir ⟨b, 0⟩ }

def lm23RetInitMiri (b : Nat) : AnnealStepState :=
  { stack := ⟨#[lm23RetInitMiriFrame b]⟩, machine := AnnealMachine.empty }

theorem lm23Ret_init_stateRelLM2_3 (b budget : Nat)
    (hbud : 1 + budget < 2 ^ 32) :
    StateRelLM2_3 lm23ReturnEnumBody lm23Env budget
      (lm23RetInitAnneal b) (lm23RetInitMiri b) := by
  refine StateRelLM2_3.mk (lm23RetInitMiriFrame b) rfl rfl
    ⟨translateTy lm23EnumTy lm23Layouts, rfl⟩
    ⟨rfl, rfl, rfl, rfl, ?_⟩
    (Or.inr (AllocIdWatermark.empty budget hbud))
    rfl rfl rfl rfl rfl
    (by
      intro i _ _ _ _ _ _ hi _
      revert hi
      match i with
      | 0 => rintro ⟨⟩
      | _ + 1 => rintro ⟨⟩)
  intro i decl slot mls hdecl hslot hmls
  match i with
  | 0 =>
    have hd : decl = lm23Decl lm23EnumTy := by
      simpa [lm23ReturnEnumBody, get?] using hdecl.symm
    have hs : slot = .uninit := by
      simpa [lm23RetInitAnneal, get?] using hslot.symm
    have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
      simpa [lm23RetInitMiriFrame] using hmls.symm
    subst hd hs hm
    exact .enumUninitImm 4 lm23Variants none rfl lm23_validEnumLayout
      (fun _ h => nomatch h)
  | _ + 1 =>
    simp [lm23ReturnEnumBody, get?] at hdecl

theorem lm23Ret_init_imm (b j : Nat) :
    IsImmediateStepLocal (lm23RetInitMiri b) j := by
  intro tf hframes mls hmls mp hv
  have htf : lm23RetInitMiriFrame b = tf := by
    simpa [lm23RetInitMiri] using hframes
  subst htf
  match j with
  | 0 => simp [lm23RetInitMiriFrame] at hmls; subst hmls; cases hv
  | _ + 1 => simp [lm23RetInitMiriFrame] at hmls

def lm23RetDeadAnneal (b : Nat) : MachineState :=
  { frame := { blockIdx := b, stmtIdx := 0, locals := [.dead] }
    memory := (initMachineState lm23ReturnEnumBody []).memory }

def lm23RetDeadMiriFrame (b : Nat) :
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { lm23RetInitMiriFrame b with
    locals := #[{ value := .dead, layout := none }] }

def lm23RetDeadMiri (b : Nat) : AnnealStepState :=
  { stack := ⟨#[lm23RetDeadMiriFrame b]⟩, machine := AnnealMachine.empty }

theorem lm23Ret_dead_stateRelLM2_3 (b budget : Nat)
    (hbud : 1 + budget < 2 ^ 32) :
    StateRelLM2_3 lm23ReturnEnumBody lm23Env budget
      (lm23RetDeadAnneal b) (lm23RetDeadMiri b) := by
  refine StateRelLM2_3.mk (lm23RetDeadMiriFrame b) rfl rfl
    ⟨translateTy lm23EnumTy lm23Layouts, rfl⟩
    ⟨rfl, rfl, rfl, rfl, ?_⟩
    (Or.inr (AllocIdWatermark.empty budget hbud))
    rfl rfl rfl rfl rfl
    (by
      intro i _ _ _ _ _ _ hi _
      revert hi
      match i with
      | 0 => rintro ⟨⟩
      | _ + 1 => rintro ⟨⟩)
  intro i decl slot mls hdecl hslot hmls
  match i with
  | 0 =>
    have hd : decl = lm23Decl lm23EnumTy := by
      simpa [lm23ReturnEnumBody, get?] using hdecl.symm
    have hs : slot = .dead := by
      simpa [lm23RetDeadAnneal, get?] using hslot.symm
    have hm : mls = { value := .dead, layout := none } := by
      simpa [lm23RetDeadMiriFrame, lm23RetInitMiriFrame] using hmls.symm
    subst hd hs hm
    exact .enumDead 4 lm23Variants none rfl lm23_validEnumLayout
      (fun _ h => nomatch h)
  | _ + 1 =>
    simp [lm23ReturnEnumBody, get?] at hdecl

theorem lm23Ret_materialize_uninitInd0 {budget : Nat} {s : MachineState}
    {m : AnnealStepState}
    (hst : StateRelLM2_3 lm23ReturnEnumBody lm23Env (budget + 1) s m)
    (hs0 : get? s.frame.locals 0 = some .uninit) :
    ∃ m_u : AnnealStepState,
      StateRelLM2_3 lm23ReturnEnumBody lm23Env budget s m_u ∧
      ¬ IsImmediateStepLocal m_u 0 := by
  rcases hst with ⟨topFrame, hframes, hretC, ⟨retLay, hretP⟩, hframe, halloc,
    hcal, hcs, hbor, hprot, hcaller, _⟩
  let wholeLay := translateTy lm23EnumTy lm23Layouts
  have hlt0 : 0 < topFrame.locals.size := by
    rw [hframe.mf_locals_size]; decide
  obtain ⟨rawAlloc, _, hbs0, hlen0, hmut0, hpmap0, hmask0⟩ :=
    tryNew_uninit_of_pow2_le_29 wholeLay.layout.size wholeLay.layout.align.abi
      lm23_validEnumLayout.align_pow2_le
  obtain ⟨mem', newId, hres, _, hlive_eq, hfresh_old, hwm_next, hovf_all⟩ :=
    halloc.of_succ.reserve_step
  let a0 := rawAlloc.withExtra (none : Option Miri.TreeBorrows.BorrowTree)
  let mach_u := stackAllocMachine m.machine mem' newId a0
  let tf_u :=
    { topFrame with
      locals := topFrame.locals.set 0
        ⟨.live (.indirect (stackAllocPlace newId)), some wholeLay⟩ hlt0 }
  let m_u : AnnealStepState := ⟨⟨#[tf_u]⟩, mach_u⟩
  have hfresh : mem'.live.any (fun entry => entry.1 == newId) = false := by
    rw [hlive_eq]; exact hfresh_old
  have hlive_u : LiveAllocEntry mach_u.memory.live newId ⟨.stack, a0⟩ :=
    LiveAllocEntry.of_push_fresh_self ⟨.stack, a0⟩ hfresh
  have hbase_u :
      mach_u.lookupBaseAddr newId = some (annealStackBaseAddr newId) :=
    lookupBaseAddr_stackAllocMachine_self m.machine mem' newId a0
  have hovf_u := hovf_all _ lm23_validEnumLayout.size_lt_4gib
  have halign_u :=
    annealStackBaseAddr_isAligned newId _ lm23_validEnumLayout.align_pow2_le
  have hlen_a0 : a0.len = a0.byteSize.bytes.toNat := by
    dsimp [a0]; rw [hlen0, ← hbs0]
  have humpr :
      UninitEnumMemRel mach_u lm23EnumTy lm23Layouts 4 lm23Variants
        (stackAllocPlace newId) :=
    .mk newId Miri.Memory.BorTag.one (annealStackBaseAddr newId) ⟨.stack, a0⟩
      lm23_validEnumLayout rfl rfl rfl hlive_u hbase_u rfl hovf_u hmut0 halign_u
      hbs0 hlen_a0 hpmap0 hmask0
  have hdecl0 :
      get? lm23ReturnEnumBody.localDecls 0 = some (lm23Decl lm23EnumTy) := rfl
  have hfr_u : FrameRelLM2_3 lm23ReturnEnumBody lm23Env mach_u s.frame tf_u := by
    refine ⟨hframe.body_eq, hframe.location_eq, hframe.af_locals_len, ?_, ?_⟩
    · dsimp [tf_u]; rw [Array.size_set]; exact hframe.mf_locals_size
    · intro j d sl mls hd hsl hm
      match j with
      | 0 =>
        rw [hdecl0] at hd
        have hd_eq : d = lm23Decl lm23EnumTy := (Option.some.inj hd).symm
        have hsl_eq : sl = .uninit := by
          rw [hs0] at hsl; exact (Option.some.inj hsl).symm
        dsimp [tf_u] at hm
        rw [Array.getElem?_set_self hlt0] at hm
        have hm_eq :
            mls = ⟨.live (.indirect (stackAllocPlace newId)), some wholeLay⟩ :=
          (Option.some.inj hm).symm
        subst hd_eq hsl_eq hm_eq
        exact .enumUninitInd 4 lm23Variants (stackAllocPlace newId)
          (some wholeLay) rfl
          (fun _ hl => (Option.some.inj (Option.mem_def.mp hl)).symm) humpr
      | _ + 1 =>
        simp [lm23ReturnEnumBody, get?] at hd
  have hdisj_u : MemoryAllocDisjoint tf_u := by
    intro i j _ _ _ _ hij hi hj
    have hsz : tf_u.locals.size = 1 := by
      dsimp [tf_u]; rw [Array.size_set]; exact hframe.mf_locals_size
    have hi_lt := (Array.getElem?_eq_some_iff.mp hi).1
    have hj_lt := (Array.getElem?_eq_some_iff.mp hj).1
    omega
  have hnot_imm : ¬ IsImmediateStepLocal m_u 0 := by
    intro himm
    have hget_u :
        tf_u.locals[0]? =
          some ⟨.live (.indirect (stackAllocPlace newId)), some wholeLay⟩ := by
      dsimp [tf_u]; rw [Array.getElem?_set_self hlt0]
    exact himm tf_u rfl _ hget_u (stackAllocPlace newId) rfl
  exact ⟨m_u,
    .mk tf_u rfl hretC ⟨retLay, hretP⟩ hfr_u (Or.inr (hwm_next _))
      hcal hcs hbor hprot hcaller hdisj_u,
    hnot_imm⟩

def lm23RetBb0S1 : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 1,
               locals := [.init (.aggregate 2
                 [.scalar ⟨42, 4⟩, .scalar ⟨99, 8⟩])] }
    memory := (initMachineState lm23ReturnEnumBody []).memory }

theorem lm23Ret_bb0_a1 :
    stepMirFn lm23ReturnEnumBody (lm23RetInitAnneal 0) = .step lm23RetBb0S1 := rfl

theorem lm23Ret_bb0_a2 :
    stepMirFn lm23ReturnEnumBody lm23RetBb0S1 =
      .retNormal (.aggregate 2 [.scalar ⟨42, 4⟩, .scalar ⟨99, 8⟩])
        lm23RetBb0S1.memory := rfl

/-- **Witness 19 (`wit_lm2_3_return_enum_and_ub`)**:
Exercises `step_return_enum_lm2_3_simulation` and
`step_return_enum_uninitInd_divergence` on `lm23ReturnEnumBody`
(`_0 : Lm23Enum`):
1. `bb0`: `_0 = Lm23Enum::V2(42_u32, 99_u64); return` steps to `lm23RetBb0S1`
   and returns `.retNormal (.aggregate 2 [.scalar ⟨42, 4⟩, .scalar ⟨99, 8⟩])`
   in lockstep with
   `annealControlHooks.returnOperand () m₁ = (m₁, .ok (.indirect mp0))`
   and `EnumMemRel m₂.machine lm23EnumTy lm23Layouts 4 lm23Variants 2
   [.scalar ⟨42, 4⟩, .scalar ⟨99, 8⟩] mp0` in `m₂ = { m₁ with stack := ⟨#[]⟩ }`;
2. `bb1` on immediate `.uninit` `_0`: `return` traps with `.ub` in lockstep;
3. `bb1` on `.dead` `_0`: `return` traps with `.ub` in lockstep;
4. `bb1` on indirect `.uninit` (`enumUninitInd`) `_0`: Anneal traps with
   `.fail .ub`, while `lean-miri` returns `.indirect mp_u0` with
   `UninitEnumMemRel` and steps `({ m_u0 with stack := ⟨#[]⟩ }, .ok true)`. -/
theorem wit_lm2_3_return_enum_and_ub :
    (∃ m₁ m₂ mp0,
      Miri.Interpreter.Step.step lm23RetHooks () (lm23RetInitMiri 0) =
        (m₁, .ok true) ∧
      StateRelLM2_3 lm23ReturnEnumBody lm23Env 0 lm23RetBb0S1 m₁ ∧
      Miri.Interpreter.Step.step lm23RetHooks () m₁ = (m₂, .ok true) ∧
      annealControlHooks.returnOperand () m₁ = (m₁, .ok (.indirect mp0)) ∧
      EnumMemRel m₂.machine lm23EnumTy lm23Layouts 4 lm23Variants 2
        [.scalar ⟨42, 4⟩, .scalar ⟨99, 8⟩] mp0 ∧
      m₂ = { m₁ with stack := ⟨#[]⟩ }) ∧
    (∃ m_err1 msg1,
      stepMirFn lm23ReturnEnumBody (lm23RetInitAnneal 1) = .fail .ub ∧
      Miri.Interpreter.Step.step lm23RetHooks () (lm23RetInitMiri 1) =
        (m_err1, .error (.undefinedBehavior msg1))) ∧
    (∃ m_err2 msg2,
      stepMirFn lm23ReturnEnumBody (lm23RetDeadAnneal 1) = .fail .ub ∧
      Miri.Interpreter.Step.step lm23RetHooks () (lm23RetDeadMiri 1) =
        (m_err2, .error (.undefinedBehavior msg2))) ∧
    (∃ m_u0 mp_u0,
      StateRelLM2_3 lm23ReturnEnumBody lm23Env 0 (lm23RetInitAnneal 1) m_u0 ∧
      ¬ IsImmediateStepLocal m_u0 0 ∧
      stepMirFn lm23ReturnEnumBody (lm23RetInitAnneal 1) = .fail .ub ∧
      annealControlHooks.returnOperand () m_u0 = (m_u0, .ok (.indirect mp_u0)) ∧
      UninitEnumMemRel m_u0.machine lm23EnumTy lm23Layouts 4 lm23Variants
        mp_u0 ∧
      Miri.Interpreter.Step.step lm23RetHooks () m_u0 =
        ({ m_u0 with stack := ⟨#[]⟩ }, .ok true)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hsim1 := evalRvalue_aggregate_enum_simulation
      (lm23Ret_init_stateRelLM2_3 0 1 (by decide)) lm23_env_valid lm23Ret_phase
      rfl rfl rfl (dstDecl := lm23Decl lm23EnumTy) rfl
      (tagBytes := 4) (variants := lm23Variants) rfl (by decide) rfl
      (fun tf i hi _ => by
        have hi' : i < 2 := hi
        match i with
        | 0 =>
          exact .constScalar (lm23ConstU32 42) ⟨42, 4⟩ rfl lm23_isPrim_u32
            (Or.inr (Or.inr (Or.inl rfl))) (by decide) rfl
            (fun h => nomatch h) (fun h => nomatch h)
        | 1 =>
          exact .constScalar (lm23ConstU64 99) ⟨99, 8⟩ rfl lm23_isPrim_u64
            (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) (by decide) rfl
            (fun h => nomatch h) (fun h => nomatch h)
        | _ + 2 => omega)
    dsimp only at hsim1
    rcases hsim1 with ⟨hrel1, _⟩
    rw [lm23Ret_bb0_a1] at hrel1
    obtain ⟨m₁, hm₁, hst₁⟩ := stepRelLM2_3_inv_step hrel1
    have hsim2 := step_return_enum_lm2_3_simulation
      hst₁ lm23Ret_phase rfl rfl rfl rfl rfl
      (decl0 := lm23Decl lm23EnumTy) rfl rfl
      (by intro h; cases h)
    rw [lm23Ret_bb0_a2] at hsim2
    obtain ⟨d0, tb, vs, mp0, m₂, hm₂, hd0, henv0, hop0, hemr, hm₂_eq⟩ :=
      stepRelEnumReturnLM2_3_inv_ret hsim2
    have hd0_eq : d0 = lm23Decl lm23EnumTy := Option.some.inj hd0.symm
    subst hd0_eq
    have henv0_eq : (tb, vs) = (4, lm23Variants) := Option.some.inj henv0.symm
    rcases Prod.mk.inj henv0_eq with ⟨rfl, rfl⟩
    exact ⟨m₁, m₂, mp0, hm₁, hst₁, hm₂, hop0, hemr, hm₂_eq⟩
  · have hsim := step_return_enum_lm2_3_simulation
      (lm23Ret_init_stateRelLM2_3 1 0 (by decide)) lm23Ret_phase
      rfl rfl rfl rfl rfl (decl0 := lm23Decl lm23EnumTy) rfl rfl
      (fun _ => lm23Ret_init_imm 1 0)
    have ha_ub :
        stepMirFn lm23ReturnEnumBody (lm23RetInitAnneal 1) = .fail .ub := rfl
    rw [ha_ub] at hsim
    obtain ⟨m_err1, msg1, hm_err1⟩ := stepRelEnumReturnLM2_3_inv_ub hsim
    exact ⟨m_err1, msg1, ha_ub, hm_err1⟩
  · have hsim := step_return_enum_lm2_3_simulation
      (lm23Ret_dead_stateRelLM2_3 1 0 (by decide)) lm23Ret_phase
      rfl rfl rfl rfl rfl (decl0 := lm23Decl lm23EnumTy) rfl rfl
      (by intro h; cases h)
    have ha_ub :
        stepMirFn lm23ReturnEnumBody (lm23RetDeadAnneal 1) = .fail .ub := rfl
    rw [ha_ub] at hsim
    obtain ⟨m_err2, msg2, hm_err2⟩ := stepRelEnumReturnLM2_3_inv_ub hsim
    exact ⟨m_err2, msg2, ha_ub, hm_err2⟩
  · obtain ⟨m_u0, hst_u0, hnot_imm0⟩ := lm23Ret_materialize_uninitInd0
      (budget := 0) (lm23Ret_init_stateRelLM2_3 1 1 (by decide)) rfl
    obtain ⟨ha_ub, mp_u0, hop_u0, humpr_u0, hm_u0⟩ :=
      step_return_enum_uninitInd_divergence
        hst_u0 lm23Ret_phase rfl rfl rfl rfl rfl
        (decl0 := lm23Decl lm23EnumTy) rfl rfl rfl hnot_imm0
    exact ⟨m_u0, mp_u0, hst_u0, hnot_imm0, ha_ub, hop_u0, humpr_u0, hm_u0⟩

end LeanMiriSpec.Correspondence.Witness
