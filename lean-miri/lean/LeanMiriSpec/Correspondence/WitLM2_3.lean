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
genuine 3-variant direct-tagged enum `enum Lm23Enum { V0, V1(u32), V2(u32, u64) }`
(16 bytes, 8-byte aligned, `u32` direct tag at `[0, 4)`, `V0` fieldless, `V1`
with `u32` at `[4, 8)`, and `V2` with `u32` at `[4, 8)` and `u64` at `[8, 16)`)
and proves concrete `rfl`-verified execution witnesses exercising all five
`LM-2.3` simulation theorems plus control-flow helpers and `StateRel.toLM2_3`:

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
7. `wit_lm2_3_bodyFree_divBody`: `BodyFreeOfLM2_3` and
   `step_LM2_3_eq_of_bodyFree` on `LM-1.1`'s `divBody`.
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
    , -- bb3: construct V1(42), SetDiscriminant(0), then read inactive V2.1 -> UB
      { statements :=
          [ lm23AggV1Stmt 1 42
          , lm23SetDiscrStmt 1 0
          , lm23DowncastReadStmt false 0 1 (some "V2") 2 1 lm23U64Ty ]
        terminator := lm23Term .return_
        isCleanup := false }
    , -- bb4: construct V2(7, 88), read discriminant = 2, SwitchInt otherwise -> bb5
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
on any block whose `stmt 0` is `lm23AggV1Stmt 1 42`, establishing `StateRelLM2_3`,
`EnumLocalByteUninit m₁ 1 8` (byte `8` in inactive `V2.1`), and immediacy of
`_0`, `_2`, `_3`. -/
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
    (by intro h; cases h) (fun _ _ _ _ => List.nil_prefix)
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
    (by intro h; cases h) (fun _ _ _ _ => List.nil_prefix)
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

/-! ## 5. Witness 4: `SwitchInt` `otherwise` Arm + `Goto` + `Return` (`bb4..bb6`) -/

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
Constructing `Lm23Enum::V2(7_u32, 88_u64)`, reading `discriminant(_1) = 2_isize`,
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

/-! ## 6. Witness 5: Lockstep `.uninit` and `.dead` Enum UB Paths (`bb7`, `bb9..bb11`) -/

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
      (fun _ _ _ hsl => by simp [lm23InitAnneal, get?] at hsl)
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

/-! ## 8. Witness 7: Conservative Extension (`BodyFreeOfLM2_3`) -/

/-- **Witness 7 (`wit_lm2_3_bodyFree_divBody`)**:
`LM-1.1`'s scalar `divBody` satisfies `BodyFreeOfLM2_3`, so
`annealStepHooksLM2_3` steps identically to `annealStepHooks` on `miriInit`. -/
theorem wit_lm2_3_bodyFree_divBody (divisor : Nat) :
    BodyFreeOfLM2_3 (divBody divisor).localDecls (divBody divisor).layouts
      (translateBody (divBody divisor)) ∧
    Miri.Interpreter.Step.step
        (annealStepHooksLM2_3 (divBody divisor).localDecls (divBody divisor).layouts)
        () (miriInit divisor) =
      Miri.Interpreter.Step.step
        (annealStepHooks (divBody divisor).localDecls (divBody divisor).layouts)
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

end LeanMiriSpec.Correspondence.Witness
