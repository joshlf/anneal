-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Lean
import Trusted
import Anneal.SpecRealizability

/-!
# Test Suite & Kernel Axiom Audit for `Anneal.SpecRealizability`

Exercises:
1. **Positive Suite**: Concrete realistic contracts (`sliceIsEmpty`, `u32CheckedAdd`,
   `rangeClamp`, `statefulCounterStep`, plus conditional boilerplate-branching
   `MirCallContract`), proving `PreconditionSatisfiable`, `ContractRealizable`,
   `PostconditionDichotomy`, `ContractDeterministic`, `StatefulClaimReturnDichotomy`,
   `MirCallContractRealizable`, `MirCallContractNormalDichotomy`, and
   `ExternalSpecEnsuresDichotomy`, paired with compile-time `#eval` checks via
   `assertEnsuresBindsOutput` and `assertDeclEnsuresBindsOutput`.
2. **Negative & Domain-Trap Suite**: All 5 `VacuityClass` failure modes
   (`DeadPrecondition`, `SpecViolation`, `TrivialPostcondition`,
   `UnboundReturnOutput`, `SurvivedAllMutants`) plus explicit instantiations of
   external-spec Soundness Traps 1, 2, and 3, paired with kernel refutation theorems
   and compile-time `#eval assertEnsuresVacuous` / `assertDeclEnsuresVacuous` checks.
3. **Checker Hardening Regression Suite**: Paired kernel theorems and compile-time
   `#eval` checks for probe-budget containment (heartbeat exhaustion never escapes and
   never becomes Lean's unlimited `maxHeartbeats = 0`), `strictReturnValue` on
   postconditions that merely mention `retVal`, uninhabited and inhabited recursive
   output types, non-reflexive `LE`, outputs hidden behind definitions, input-only
   tautologies, contradictory and `requires`-vacuous boilerplate fibres,
   type-checked substituted goals, degradation notes that tell a probe the tactics
   failed to prove apart from one a heartbeat or recursion cap cut off,
   starved-budget syntactic fibre classification, native `Option`/`Except`/`BinTree`
   negative controls, `TotalClaim` / `ModularClaim` declarations, the literal
   cross-language `VacuityClass` wire names, and the prover-free syntactic layer
   (contradictory `requires` / `ensures`, ex falso, conjunctive and symmetric
   hypotheses, `decide`-wrapped and quantified reflexivity) under a starved budget.
   It closes with the **Cross-Language 1:1 Vacuity Parity Suite**
   (`CrossLanguageParitySuite`): 4 strong contracts (`CL_POS_01..CL_POS_04`) and 5
   intentional vacuity mutants (`CL_VAC_01..CL_VAC_05`) shared ID-for-ID with the Rust
   dynamic checker's `cross_language_parity_suite` test module, asserting that both
   languages emit the same canonical `VacuityClass` names in the same order.
4. **Compile-Time Kernel Axiom Audit (EOF)**: Audits every constant defined by the
   `Anneal.SpecRealizability` module and by this file (selected by defining module, not
   by name prefix), of every kind (theorems, definitions, instances), for
   `isUnsafe == false`, no `axiom`, no `opaque`/`partial`, and transitive axioms
   strictly within `[propext, Classical.choice, Quot.sound]` (so `sorryAx`,
   `Lean.ofReduceBool`, and `Lean.trustCompiler` are rejected); requires the
   load-bearing results to be kernel theorems and `≥ 140` theorems overall.
-/

namespace SpecRealizabilityTests

open Trusted.Refinement
open Trusted.Effect
open Trusted.ITree
open Trusted.Sequence
open Trusted.Layout
open Trusted.MirAst
open Trusted.MirSemantics
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.SpecRealizability

/-! ## Shared MIR Test Fixtures & Structural Injectivity Helpers -/

@[reducible] private def boolMirTy : Ty := { kind := .bool, layoutIdx := 0 }
@[reducible] private def u32MirTy : Ty := { kind := .uint .u32, layoutIdx := 0 }
@[reducible] private def usizeMirTy : Ty := { kind := .uint .usize, layoutIdx := 0 }
@[reducible] private def optionU32MirTy : Ty :=
  { kind := .adt "core::option::Option" [.uint .u32], layoutIdx := 0 }

@[reducible] private def mkPrimLayout (bytes : Nat) : TypeLayout := {
  size := { bytes := bytes }
  align := { bytes := bytes }
  backendRepr := .memory
  fields := .primitive
  variants := .single 0
  isUninhabited := false
}

@[reducible] private def boolLayout : TypeLayout := mkPrimLayout 1
@[reducible] private def u32Layout : TypeLayout := mkPrimLayout 4

@[reducible] private def mkLocalDecl (ty : Ty) : LocalDecl :=
  { mutability := .not, ty := ty, debugName := none }

@[reducible] private def mkStubBody
    (defPath : DefPath) (argCount : Nat)
    (localDecls : List LocalDecl) (retLayout : TypeLayout)
    (canUnwind : Bool := true) : CapturedMir := {
  defPath := defPath
  phase := .runtimePostCleanup
  role := .subject
  argCount := argCount
  localDecls := localDecls
  basicBlocks := []
  fnAbi := {
    args := []
    ret := { layout := retLayout, mode := .direct }
    conv := .rust
    canUnwind := canUnwind
  }
  layouts := emptyLayoutTable
  allocations := []
}

private theorem scalar_bits_inj {b₁ b₂ s₁ s₂ : Nat}
    (h : Value.scalar { bits := b₁, sizeBytes := s₁ } =
         Value.scalar { bits := b₂, sizeBytes := s₂ }) :
    b₁ = b₂ ∧ s₁ = s₂ := by
  cases h
  exact ⟨rfl, rfl⟩

private theorem aggregate_variant_inj {v₁ v₂ : VariantIdx} {f₁ f₂ : List Value}
    (h : Value.aggregate v₁ f₁ = Value.aggregate v₂ f₂) :
    v₁ = v₂ ∧ f₁ = f₂ := by
  cases h
  exact ⟨rfl, rfl⟩

private theorem list_singleton_inj {α : Type} {a b : α} (h : [a] = [b]) : a = b := by
  cases h
  rfl

private theorem list_pair_inj {α : Type} {a₁ a₂ b₁ b₂ : α}
    (h : [a₁, a₂] = [b₁, b₂]) : a₁ = b₁ ∧ a₂ = b₂ := by
  cases h
  exact ⟨rfl, rfl⟩

private theorem list_triple_inj {α : Type} {a₁ a₂ a₃ b₁ b₂ b₃ : α}
    (h : [a₁, a₂, a₃] = [b₁, b₂, b₃]) : a₁ = b₁ ∧ a₂ = b₂ ∧ a₃ = b₃ := by
  cases h
  exact ⟨rfl, rfl, rfl⟩

private theorem memory_nextTag_ne_1_2 :
    emptyMemory ≠ { emptyMemory with nextTag := 2 } := by
  intro h
  have hTag : emptyMemory.nextTag = ({ emptyMemory with nextTag := 2 } : Memory).nextTag :=
    congrArg Memory.nextTag h
  dsimp [emptyMemory] at hTag
  omega

private theorem optionEmpty_subsingleton : Subsingleton (Option Empty) :=
  ⟨fun a b => by
    cases a with
    | none =>
      cases b with
      | none => rfl
      | some e => exact nomatch e
    | some e => exact nomatch e⟩

/-! ## 1. Positive Suite -/

/-! ### 1.1 `sliceIsEmpty` (`ret = 1` iff `len = 0`) -/

def sliceIsEmptySidecar : CapturedMir :=
  mkStubBody "core::slice::is_empty" 1
    [mkLocalDecl boolMirTy, mkLocalDecl usizeMirTy]
    boolLayout true

def sliceIsEmptyPre (args : List Value) : Prop :=
  ∃ len : Nat, len < scalarModulus 8 ∧ args = [.scalar { bits := len, sizeBytes := 8 }]

def sliceIsEmptyPost (args : List Value) (ret : Value) : Prop :=
  ∃ len : Nat,
    args = [.scalar { bits := len, sizeBytes := 8 }] ∧
    ret = .scalar { bits := if len = 0 then 1 else 0, sizeBytes := 1 }

def sliceIsEmptyClaim : Claim := {
  body := sliceIsEmptySidecar
  pre := sliceIsEmptyPre
  post := sliceIsEmptyPost
}

def sliceIsEmptyExtContract : MirCallContract :=
  externalSpecCallContract "core::slice::is_empty" sliceIsEmptySidecar
    sliceIsEmptyPre sliceIsEmptyPost

theorem sliceIsEmpty_preSatisfiable : ClaimPreSatisfiable sliceIsEmptyClaim :=
  ⟨[.scalar { bits := 0, sizeBytes := 8 }], 0, by decide, rfl⟩

theorem sliceIsEmpty_realizable : ClaimRealizable sliceIsEmptyClaim :=
  ⟨[.scalar { bits := 0, sizeBytes := 8 }],
    ⟨0, by decide, rfl⟩,
    .scalar { bits := 1, sizeBytes := 1 },
    ⟨0, rfl, rfl⟩⟩

theorem sliceIsEmpty_dichotomy : ClaimDichotomy sliceIsEmptyClaim := by
  refine ⟨[.scalar { bits := 0, sizeBytes := 8 }], ⟨0, by decide, rfl⟩,
    ⟨.scalar { bits := 1, sizeBytes := 1 }, ⟨0, rfl, rfl⟩⟩,
    ⟨.scalar { bits := 0, sizeBytes := 1 }, ?_⟩⟩
  rintro ⟨len, hArgs, hRet⟩
  have hLen : (0 : Nat) = len := (scalar_bits_inj (list_singleton_inj hArgs)).1
  subst hLen
  have hBits : (0 : Nat) = (if (0 : Nat) = 0 then 1 else 0) := (scalar_bits_inj hRet).1
  exact absurd hBits (by decide)

theorem sliceIsEmpty_deterministic : ClaimDeterministic sliceIsEmptyClaim := by
  rintro args y₁ y₂ _ ⟨len₁, hArgs₁, hRet₁⟩ ⟨len₂, hArgs₂, hRet₂⟩
  have hEqArgs : [Value.scalar { bits := len₁, sizeBytes := 8 }] =
      [Value.scalar { bits := len₂, sizeBytes := 8 }] :=
    hArgs₁.symm.trans hArgs₂
  have hLen : len₁ = len₂ := (scalar_bits_inj (list_singleton_inj hEqArgs)).1
  subst hLen
  exact hRet₁.trans hRet₂.symm

theorem sliceIsEmpty_ext_realizable :
    MirCallContractRealizable sliceIsEmptyExtContract := by
  let req : MirCallReq := {
    defPath := "core::slice::is_empty"
    args := [.scalar { bits := 0, sizeBytes := 8 }]
    memory := emptyMemory
  }
  refine externalSpecCallContract_realizable_of_witness
    req (.scalar { bits := 1, sizeBytes := 1 }) ?_ ?_ ?_
  · exact ⟨rfl, rfl, ⟨⟨0, by decide, rfl⟩, trivial⟩, ⟨0, by decide, rfl⟩⟩
  · exact ⟨1, by decide, rfl⟩
  · exact ⟨0, rfl, rfl⟩

theorem sliceIsEmpty_ext_ensuresDichotomy :
    ExternalSpecEnsuresDichotomy "core::slice::is_empty" sliceIsEmptySidecar
      sliceIsEmptyPre sliceIsEmptyPost := by
  apply (externalSpecEnsuresDichotomy_iff_moduloObservation
    "core::slice::is_empty" sliceIsEmptySidecar sliceIsEmptyPre sliceIsEmptyPost).mpr
  let req : MirCallReq := {
    defPath := "core::slice::is_empty"
    args := [.scalar { bits := 0, sizeBytes := 8 }]
    memory := emptyMemory
  }
  refine ⟨req, emptyMemory,
    .scalar { bits := 1, sizeBytes := 1 },
    .scalar { bits := 0, sizeBytes := 1 },
    ⟨rfl, rfl, ⟨⟨0, by decide, rfl⟩, trivial⟩, ⟨0, by decide, rfl⟩⟩,
    callFramePreserved_refl emptyMemory,
    ⟨1, by decide, rfl⟩,
    ⟨0, by decide, rfl⟩,
    ⟨0, rfl, rfl⟩,
    ?_⟩
  rintro ⟨len, hArgs, hRet⟩
  have hLen : (0 : Nat) = len := (scalar_bits_inj (list_singleton_inj hArgs)).1
  subst hLen
  have hBits : (0 : Nat) = (if (0 : Nat) = 0 then 1 else 0) := (scalar_bits_inj hRet).1
  exact absurd hBits (by decide)

theorem sliceIsEmpty_ext_normalDichotomy :
    MirCallContractNormalDichotomy sliceIsEmptyExtContract :=
  (externalSpecEnsuresDichotomy_to_returnValueDichotomy
    sliceIsEmpty_ext_ensuresDichotomy).toNormalDichotomy

#eval assertEnsuresBindsOutput
  (Lean.mkConst ``sliceIsEmptyPost) (some (Lean.mkConst ``sliceIsEmptyPre))
#eval assertDeclEnsuresBindsOutput ``sliceIsEmptyClaim
#eval assertDeclEnsuresBindsOutput ``sliceIsEmptyExtContract

/-! ### 1.2 `u32CheckedAdd` (in-range `Some (a + b)` and overflow `None`) -/

def u32CheckedAddSidecar : CapturedMir :=
  mkStubBody "core::num::u32::checked_add" 2
    [mkLocalDecl optionU32MirTy, mkLocalDecl u32MirTy, mkLocalDecl u32MirTy]
    u32Layout true

def u32CheckedAddPre (args : List Value) : Prop :=
  ∃ a b : Nat,
    a < scalarModulus 4 ∧ b < scalarModulus 4 ∧
    args = [.scalar { bits := a, sizeBytes := 4 }, .scalar { bits := b, sizeBytes := 4 }]

def u32CheckedAddPost (args : List Value) (ret : Value) : Prop :=
  ∃ a b : Nat,
    args = [.scalar { bits := a, sizeBytes := 4 }, .scalar { bits := b, sizeBytes := 4 }] ∧
    ((a + b < scalarModulus 4 ∧
        ret = .aggregate 1 [.scalar { bits := a + b, sizeBytes := 4 }]) ∨
     (scalarModulus 4 ≤ a + b ∧ ret = .aggregate 0 []))

def u32CheckedAddClaim : Claim := {
  body := u32CheckedAddSidecar
  pre := u32CheckedAddPre
  post := u32CheckedAddPost
}

def u32CheckedAddExtContract : MirCallContract :=
  externalSpecCallContract "core::num::u32::checked_add" u32CheckedAddSidecar
    u32CheckedAddPre u32CheckedAddPost

theorem u32CheckedAdd_preSatisfiable : ClaimPreSatisfiable u32CheckedAddClaim :=
  ⟨[.scalar { bits := 2, sizeBytes := 4 }, .scalar { bits := 3, sizeBytes := 4 }],
    2, 3, by decide, by decide, rfl⟩

theorem u32CheckedAdd_realizable_inRange : ClaimRealizable u32CheckedAddClaim :=
  ⟨[.scalar { bits := 2, sizeBytes := 4 }, .scalar { bits := 3, sizeBytes := 4 }],
    ⟨2, 3, by decide, by decide, rfl⟩,
    .aggregate 1 [.scalar { bits := 5, sizeBytes := 4 }],
    ⟨2, 3, rfl, Or.inl ⟨by decide, rfl⟩⟩⟩

theorem u32CheckedAdd_realizable_overflow : ClaimRealizable u32CheckedAddClaim :=
  ⟨[.scalar { bits := scalarModulus 4 - 1, sizeBytes := 4 },
    .scalar { bits := 1, sizeBytes := 4 }],
    ⟨scalarModulus 4 - 1, 1, by decide, by decide, rfl⟩,
    .aggregate 0 [],
    ⟨scalarModulus 4 - 1, 1, rfl, Or.inr ⟨by decide, rfl⟩⟩⟩

theorem u32CheckedAdd_dichotomy : ClaimDichotomy u32CheckedAddClaim := by
  refine ⟨[.scalar { bits := 2, sizeBytes := 4 }, .scalar { bits := 3, sizeBytes := 4 }],
    ⟨2, 3, by decide, by decide, rfl⟩,
    ⟨.aggregate 1 [.scalar { bits := 5, sizeBytes := 4 }],
      ⟨2, 3, rfl, Or.inl ⟨by decide, rfl⟩⟩⟩,
    ⟨.aggregate 0 [], ?_⟩⟩
  rintro ⟨a, b, hArgs, hBranch⟩
  rcases list_pair_inj hArgs with ⟨ha, hb⟩
  have ha' : (2 : Nat) = a := (scalar_bits_inj ha).1
  have hb' : (3 : Nat) = b := (scalar_bits_inj hb).1
  subst ha'; subst hb'
  rcases hBranch with ⟨_, hEq⟩ | ⟨hOvf, _⟩
  · have hv : (0 : Nat) = 1 := (aggregate_variant_inj hEq).1
    omega
  · exact absurd hOvf (by decide)

theorem u32CheckedAdd_deterministic : ClaimDeterministic u32CheckedAddClaim := by
  rintro args y₁ y₂ _ ⟨a₁, b₁, hArgs₁, hB₁⟩ ⟨a₂, b₂, hArgs₂, hB₂⟩
  have hPair := list_pair_inj (hArgs₁.symm.trans hArgs₂)
  have ha : a₁ = a₂ := (scalar_bits_inj hPair.1).1
  have hb : b₁ = b₂ := (scalar_bits_inj hPair.2).1
  subst ha; subst hb
  rcases hB₁ with ⟨hLt₁, hEq₁⟩ | ⟨hGe₁, hEq₁⟩
  · rcases hB₂ with ⟨_, hEq₂⟩ | ⟨hGe₂, _⟩
    · exact hEq₁.trans hEq₂.symm
    · omega
  · rcases hB₂ with ⟨hLt₂, _⟩ | ⟨_, hEq₂⟩
    · omega
    · exact hEq₁.trans hEq₂.symm

theorem u32CheckedAdd_ext_realizable :
    MirCallContractRealizable u32CheckedAddExtContract := by
  let req : MirCallReq := {
    defPath := "core::num::u32::checked_add"
    args := [.scalar { bits := 2, sizeBytes := 4 }, .scalar { bits := 3, sizeBytes := 4 }]
    memory := emptyMemory
  }
  refine externalSpecCallContract_realizable_of_witness
    req (.aggregate 1 [.scalar { bits := 5, sizeBytes := 4 }]) ?_ ?_ ?_
  · exact ⟨rfl, rfl, ⟨⟨2, by decide, rfl⟩, ⟨3, by decide, rfl⟩, trivial⟩,
      ⟨2, 3, by decide, by decide, rfl⟩⟩
  · rfl
  · exact ⟨2, 3, rfl, Or.inl ⟨by decide, rfl⟩⟩

theorem u32CheckedAdd_ext_ensuresDichotomy :
    ExternalSpecEnsuresDichotomy "core::num::u32::checked_add" u32CheckedAddSidecar
      u32CheckedAddPre u32CheckedAddPost := by
  apply (externalSpecEnsuresDichotomy_iff_moduloObservation
    "core::num::u32::checked_add" u32CheckedAddSidecar u32CheckedAddPre u32CheckedAddPost).mpr
  let req : MirCallReq := {
    defPath := "core::num::u32::checked_add"
    args := [.scalar { bits := 2, sizeBytes := 4 }, .scalar { bits := 3, sizeBytes := 4 }]
    memory := emptyMemory
  }
  refine ⟨req, emptyMemory,
    .aggregate 1 [.scalar { bits := 5, sizeBytes := 4 }],
    .aggregate 0 [],
    ⟨rfl, rfl, ⟨⟨2, by decide, rfl⟩, ⟨3, by decide, rfl⟩, trivial⟩,
      ⟨2, 3, by decide, by decide, rfl⟩⟩,
    callFramePreserved_refl emptyMemory,
    rfl,
    rfl,
    ⟨2, 3, rfl, Or.inl ⟨by decide, rfl⟩⟩,
    ?_⟩
  rintro ⟨a, b, hArgs, hBranch⟩
  rcases list_pair_inj hArgs with ⟨ha, hb⟩
  have ha' : (2 : Nat) = a := (scalar_bits_inj ha).1
  have hb' : (3 : Nat) = b := (scalar_bits_inj hb).1
  subst ha'; subst hb'
  rcases hBranch with ⟨_, hEq⟩ | ⟨hOvf, _⟩
  · have hv : (0 : Nat) = 1 := (aggregate_variant_inj hEq).1
    omega
  · exact absurd hOvf (by decide)

theorem u32CheckedAdd_ext_normalDichotomy :
    MirCallContractNormalDichotomy u32CheckedAddExtContract :=
  (externalSpecEnsuresDichotomy_to_returnValueDichotomy
    u32CheckedAdd_ext_ensuresDichotomy).toNormalDichotomy

#eval assertEnsuresBindsOutput
  (Lean.mkConst ``u32CheckedAddPost) (some (Lean.mkConst ``u32CheckedAddPre))
#eval assertDeclEnsuresBindsOutput ``u32CheckedAddClaim
#eval assertDeclEnsuresBindsOutput ``u32CheckedAddExtContract

/-! ### 1.3 `rangeClamp` (`lo ≤ hi`, `ret = min (max val lo) hi`) -/

def rangeClampSidecar : CapturedMir :=
  mkStubBody "core::cmp::Ord::clamp" 3
    [mkLocalDecl u32MirTy, mkLocalDecl u32MirTy, mkLocalDecl u32MirTy, mkLocalDecl u32MirTy]
    u32Layout true

def rangeClampPre (args : List Value) : Prop :=
  ∃ val lo hi : Nat,
    val < scalarModulus 4 ∧ lo < scalarModulus 4 ∧ hi < scalarModulus 4 ∧ lo ≤ hi ∧
    args = [
      .scalar { bits := val, sizeBytes := 4 },
      .scalar { bits := lo, sizeBytes := 4 },
      .scalar { bits := hi, sizeBytes := 4 }
    ]

def rangeClampPost (args : List Value) (ret : Value) : Prop :=
  ∃ val lo hi : Nat,
    args = [
      .scalar { bits := val, sizeBytes := 4 },
      .scalar { bits := lo, sizeBytes := 4 },
      .scalar { bits := hi, sizeBytes := 4 }
    ] ∧
    ret = .scalar { bits := min (max val lo) hi, sizeBytes := 4 }

def rangeClampClaim : Claim := {
  body := rangeClampSidecar
  pre := rangeClampPre
  post := rangeClampPost
}

def rangeClampExtContract : MirCallContract :=
  externalSpecCallContract "core::cmp::Ord::clamp" rangeClampSidecar
    rangeClampPre rangeClampPost

theorem rangeClamp_preSatisfiable : ClaimPreSatisfiable rangeClampClaim :=
  ⟨[.scalar { bits := 15, sizeBytes := 4 },
    .scalar { bits := 10, sizeBytes := 4 },
    .scalar { bits := 20, sizeBytes := 4 }],
    15, 10, 20, by decide, by decide, by decide, by omega, rfl⟩

theorem rangeClamp_realizable : ClaimRealizable rangeClampClaim :=
  ⟨[.scalar { bits := 15, sizeBytes := 4 },
    .scalar { bits := 10, sizeBytes := 4 },
    .scalar { bits := 20, sizeBytes := 4 }],
    ⟨15, 10, 20, by decide, by decide, by decide, by omega, rfl⟩,
    .scalar { bits := 15, sizeBytes := 4 },
    ⟨15, 10, 20, rfl, rfl⟩⟩

theorem rangeClamp_dichotomy : ClaimDichotomy rangeClampClaim := by
  refine ⟨[.scalar { bits := 15, sizeBytes := 4 },
      .scalar { bits := 10, sizeBytes := 4 },
      .scalar { bits := 20, sizeBytes := 4 }],
    ⟨15, 10, 20, by decide, by decide, by decide, by omega, rfl⟩,
    ⟨.scalar { bits := 15, sizeBytes := 4 }, ⟨15, 10, 20, rfl, rfl⟩⟩,
    ⟨.scalar { bits := 0, sizeBytes := 4 }, ?_⟩⟩
  rintro ⟨val, lo, hi, hArgs, hRet⟩
  rcases list_triple_inj hArgs with ⟨hv, hlo, hhi⟩
  have hv' : (15 : Nat) = val := (scalar_bits_inj hv).1
  have hlo' : (10 : Nat) = lo := (scalar_bits_inj hlo).1
  have hhi' : (20 : Nat) = hi := (scalar_bits_inj hhi).1
  subst hv'; subst hlo'; subst hhi'
  have hBits : (0 : Nat) = min (max 15 10) 20 := (scalar_bits_inj hRet).1
  exact absurd hBits (by decide)

theorem rangeClamp_deterministic : ClaimDeterministic rangeClampClaim := by
  rintro args y₁ y₂ _ ⟨v₁, lo₁, hi₁, hArgs₁, hRet₁⟩ ⟨v₂, lo₂, hi₂, hArgs₂, hRet₂⟩
  rcases list_triple_inj (hArgs₁.symm.trans hArgs₂) with ⟨hv, hlo, hhi⟩
  have hv' : v₁ = v₂ := (scalar_bits_inj hv).1
  have hlo' : lo₁ = lo₂ := (scalar_bits_inj hlo).1
  have hhi' : hi₁ = hi₂ := (scalar_bits_inj hhi).1
  subst hv'; subst hlo'; subst hhi'
  exact hRet₁.trans hRet₂.symm

theorem rangeClamp_ext_ensuresDichotomy :
    ExternalSpecEnsuresDichotomy "core::cmp::Ord::clamp" rangeClampSidecar
      rangeClampPre rangeClampPost := by
  apply (externalSpecEnsuresDichotomy_iff_moduloObservation
    "core::cmp::Ord::clamp" rangeClampSidecar rangeClampPre rangeClampPost).mpr
  let req : MirCallReq := {
    defPath := "core::cmp::Ord::clamp"
    args := [
      .scalar { bits := 15, sizeBytes := 4 },
      .scalar { bits := 10, sizeBytes := 4 },
      .scalar { bits := 20, sizeBytes := 4 }
    ]
    memory := emptyMemory
  }
  refine ⟨req, emptyMemory,
    .scalar { bits := 15, sizeBytes := 4 },
    .scalar { bits := 0, sizeBytes := 4 },
    ⟨rfl, rfl,
      ⟨⟨15, by decide, rfl⟩, ⟨10, by decide, rfl⟩, ⟨20, by decide, rfl⟩, trivial⟩,
      ⟨15, 10, 20, by decide, by decide, by decide, by omega, rfl⟩⟩,
    callFramePreserved_refl emptyMemory,
    ⟨15, by decide, rfl⟩,
    ⟨0, by decide, rfl⟩,
    ⟨15, 10, 20, rfl, rfl⟩,
    ?_⟩
  rintro ⟨val, lo, hi, hArgs, hRet⟩
  rcases list_triple_inj hArgs with ⟨hv, hlo, hhi⟩
  have hv' : (15 : Nat) = val := (scalar_bits_inj hv).1
  have hlo' : (10 : Nat) = lo := (scalar_bits_inj hlo).1
  have hhi' : (20 : Nat) = hi := (scalar_bits_inj hhi).1
  subst hv'; subst hlo'; subst hhi'
  have hBits : (0 : Nat) = min (max 15 10) 20 := (scalar_bits_inj hRet).1
  exact absurd hBits (by decide)

theorem rangeClamp_ext_realizable :
    MirCallContractRealizable rangeClampExtContract :=
  (externalSpecEnsuresDichotomy_to_returnValueDichotomy
    rangeClamp_ext_ensuresDichotomy).toNormalDichotomy.toRealizable

theorem rangeClamp_ext_normalDichotomy :
    MirCallContractNormalDichotomy rangeClampExtContract :=
  (externalSpecEnsuresDichotomy_to_returnValueDichotomy
    rangeClamp_ext_ensuresDichotomy).toNormalDichotomy

#eval assertEnsuresBindsOutput
  (Lean.mkConst ``rangeClampPost) (some (Lean.mkConst ``rangeClampPre))
#eval assertDeclEnsuresBindsOutput ``rangeClampClaim
#eval assertDeclEnsuresBindsOutput ``rangeClampExtContract

/-! ### 1.4 `statefulCounterStep` (`StatefulClaim` & `StatefulClaimReturnDichotomy`) -/

def statefulCounterStepBody : CapturedMir :=
  mkStubBody "counter::step" 0 [mkLocalDecl u32MirTy] u32Layout true

def statefulCounterStepPre (args : List Value) (mem : Memory) : Prop :=
  args = [] ∧ mem.nextTag < scalarModulus 4

def statefulCounterStepPost
    (_args : List Value) (mem : Memory) (ret : Value) (mem' : Memory) : Prop :=
  ret = .scalar { bits := mem.nextTag, sizeBytes := 4 } ∧
  mem' = { mem with nextTag := mem.nextTag + 1 }

def statefulCounterStepClaim : StatefulClaim := {
  body := statefulCounterStepBody
  pre := statefulCounterStepPre
  post := statefulCounterStepPost
}

theorem statefulCounterStep_preSatisfiable :
    StatefulClaimPreSatisfiable statefulCounterStepClaim :=
  ⟨([], emptyMemory), rfl, by decide⟩

theorem statefulCounterStep_realizable :
    StatefulClaimRealizable statefulCounterStepClaim :=
  ⟨([], emptyMemory), ⟨rfl, by decide⟩,
    (.scalar { bits := emptyMemory.nextTag, sizeBytes := 4 },
      { emptyMemory with nextTag := emptyMemory.nextTag + 1 }),
    ⟨rfl, rfl⟩⟩

theorem statefulCounterStep_returnDichotomy :
    StatefulClaimReturnDichotomy statefulCounterStepClaim := by
  refine ⟨[], emptyMemory, { emptyMemory with nextTag := emptyMemory.nextTag + 1 },
    .scalar { bits := emptyMemory.nextTag, sizeBytes := 4 },
    .scalar { bits := 0, sizeBytes := 4 },
    ⟨rfl, by decide⟩, ⟨rfl, rfl⟩, ?_⟩
  rintro ⟨hRet, _⟩
  have hBits : (0 : Nat) = emptyMemory.nextTag := (scalar_bits_inj hRet).1
  dsimp [emptyMemory] at hBits
  omega

theorem statefulCounterStep_dichotomy :
    StatefulClaimDichotomy statefulCounterStepClaim :=
  statefulCounterStep_returnDichotomy.toDichotomy

theorem statefulCounterStep_deterministic :
    StatefulClaimDeterministic statefulCounterStepClaim := by
  rintro ⟨args, mem⟩ ⟨v₁, m₁⟩ ⟨v₂, m₂⟩ _ ⟨hv₁, hm₁⟩ ⟨hv₂, hm₂⟩
  have hv : v₁ = v₂ := hv₁.trans hv₂.symm
  have hm : m₁ = m₂ := hm₁.trans hm₂.symm
  cases hv; cases hm; rfl

#eval assertDeclEnsuresBindsOutput ``statefulCounterStepClaim
#eval assertDeclEnsuresBindsOutput ``statefulCounterStepClaim { strictReturnValue := true }

/-! ### 1.5 Conditional Boilerplate Contract (Must Not Be False-Flagged) -/

open scoped Classical in
def condFrameContract : MirCallContract := {
  pre := fun _ => True
  post := fun req ans =>
    match ans with
    | .returned retVal memAfter =>
      if callFramePreserved req.memory memAfter then
        retVal = .scalar { bits := 1, sizeBytes := 4 }
      else
        retVal = .scalar { bits := 2, sizeBytes := 4 }
    | .panicked _ => False
    | .aborted => True
}

#eval assertDeclEnsuresBindsOutput ``condFrameContract

/-! ## 2. Negative & Domain-Trap Suite (All 5 `VacuityClass` Variants) -/

/-! ### Class 1: `DeadPrecondition` -/

def deadPre (x : Nat) : Prop := x > 100 ∧ x < 50
def deadPost (x ret : Nat) : Prop := ret = x

theorem deadPre_not_satisfiable : ¬ PreconditionSatisfiable deadPre := by
  rintro ⟨x, hGt, hLt⟩
  omega

theorem deadPre_not_realizable : ¬ ContractRealizable deadPre deadPost :=
  not_contractRealizable_of_unsat_pre deadPre_not_satisfiable

#eval assertEnsuresVacuous
  (Lean.mkConst ``deadPost) (some (Lean.mkConst ``deadPre)) (some .deadPrecondition)

#eval show Lean.Meta.MetaM Unit from do
  let resDead ← checkRequiresSatisfiable (Lean.mkConst ``deadPre)
  unless resDead.satisfiable? == some false do
    throwError "expected deadPre unsatisfiable, got {repr resDead}"

/-! ### Class 2: `SpecViolation` -/

def specViolPre (x : Nat) : Prop := x < 10
def specViolPost (x ret : Nat) : Prop := x ≥ 10 ∧ ret = 5
def contraPost (_x ret : Nat) : Prop := ret = 1 ∧ ret = 2

theorem specViol_not_realizable : ¬ ContractRealizable specViolPre specViolPost := by
  rintro ⟨x, hLt, _, hGe, _⟩
  dsimp [specViolPre, specViolPost] at hLt hGe
  omega

theorem contraPost_not_realizable :
    ¬ ContractRealizable (fun _ : Nat => True) contraPost := by
  rintro ⟨_, _, ret, h1, h2⟩
  omega

#eval assertEnsuresVacuous
  (Lean.mkConst ``specViolPost) (some (Lean.mkConst ``specViolPre)) (some .specViolation)
#eval assertEnsuresVacuous
  (Lean.mkConst ``contraPost) none (some .specViolation)

/-! ### Class 3: `TrivialPostcondition` -/

def trivTruePost (_x _ret : Nat) : Prop := True
def trivReflPost (_x ret : Nat) : Prop := ret = ret
def trivNotNePost (_x ret : Nat) : Prop := ¬ (ret ≠ ret)
def trivDisjPost (_x ret : Nat) : Prop := ret = ret ∨ ret = 0
def trivImpPost (x ret : Nat) : Prop := (ret = x) → (ret = x)

theorem trivTruePost_not_dichotomy :
    ¬ PostconditionDichotomy (fun _ : Nat => True) trivTruePost :=
  not_postconditionDichotomy_of_post_true _

theorem trivReflPost_not_dichotomy :
    ¬ PostconditionDichotomy (fun _ : Nat => True) trivReflPost :=
  not_postconditionDichotomy_of_trivial (fun _ _ _ => rfl)

theorem trivNotNePost_not_dichotomy :
    ¬ PostconditionDichotomy (fun _ : Nat => True) trivNotNePost :=
  not_postconditionDichotomy_of_trivial (fun _ _ _ hNe => hNe rfl)

theorem trivDisjPost_not_dichotomy :
    ¬ PostconditionDichotomy (fun _ : Nat => True) trivDisjPost :=
  not_postconditionDichotomy_of_trivial (fun _ _ _ => Or.inl rfl)

theorem trivImpPost_not_dichotomy :
    ¬ PostconditionDichotomy (fun _ : Nat => True) trivImpPost :=
  not_postconditionDichotomy_of_trivial (fun _ _ _ h => h)

#eval assertEnsuresVacuous (Lean.mkConst ``trivTruePost) none (some .trivialPostcondition)
#eval assertEnsuresVacuous (Lean.mkConst ``trivReflPost) none (some .trivialPostcondition)
#eval assertEnsuresVacuous (Lean.mkConst ``trivNotNePost) none (some .trivialPostcondition)
#eval assertEnsuresVacuous (Lean.mkConst ``trivDisjPost) none (some .trivialPostcondition)
#eval assertEnsuresVacuous (Lean.mkConst ``trivImpPost) none (some .trivialPostcondition)

/-! ### Class 4: `UnboundReturnOutput` -/

def discardedLetPost (_x ret : Nat) : Prop :=
  let _ := ret
  True

def inputOnlyPost (x _ret : Nat) : Prop := x < 100

def optEmptyPost (_x : Nat) (ret : Option Empty) : Prop := ret = none

def memOnlyStatefulClaim : StatefulClaim := {
  body := statefulCounterStepBody
  pre := fun _ _ => True
  post := fun _ mem _ mem' => mem' = mem
}

def boilerplateOnlyExtContract : MirCallContract :=
  externalSpecCallContract "core::slice::is_empty" sliceIsEmptySidecar
    sliceIsEmptyPre (fun _ _ => True)

def restatedFrameContract : MirCallContract := {
  pre := fun _ => True
  post := fun req ans =>
    match ans with
    | .returned _ memAfter => callFramePreserved req.memory memAfter
    | .panicked memAfter => callFramePreserved req.memory memAfter
    | .aborted => True
}

theorem discardedLetPost_not_dichotomy :
    ¬ PostconditionDichotomy (fun _ : Nat => True) discardedLetPost :=
  not_postconditionDichotomy_of_trivial (fun _ _ _ => trivial)

theorem inputOnlyPost_not_dichotomy :
    ¬ PostconditionDichotomy (fun _ : Nat => True) inputOnlyPost :=
  not_postconditionDichotomy_of_outputInsensitive (fun _ _ _ _ => Iff.rfl)

theorem optEmptyPost_not_dichotomy :
    ¬ PostconditionDichotomy (fun _ : Nat => True) optEmptyPost :=
  @not_postconditionDichotomy_of_subsingleton _ _ optionEmpty_subsingleton _ _

theorem memOnlyStateful_dichotomy :
    StatefulClaimDichotomy memOnlyStatefulClaim := by
  refine ⟨([], emptyMemory), trivial,
    ⟨(.unit, emptyMemory), rfl⟩,
    ⟨(.unit, { emptyMemory with nextTag := 2 }), ?_⟩⟩
  intro hEq
  exact memory_nextTag_ne_1_2 hEq.symm

theorem memOnlyStateful_not_returnDichotomy :
    ¬ StatefulClaimReturnDichotomy memOnlyStatefulClaim := by
  rintro ⟨_, _, _, _, _, _, hOk, hBad⟩
  exact hBad hOk

theorem boilerplateOnlyExt_not_ensuresDichotomy :
    ¬ ExternalSpecEnsuresDichotomy "core::slice::is_empty" sliceIsEmptySidecar
        sliceIsEmptyPre (fun _ _ => True) :=
  not_externalSpecEnsuresDichotomy_of_trivial_extraPost
    "core::slice::is_empty" sliceIsEmptySidecar sliceIsEmptyPre (fun _ _ => trivial)

#eval assertEnsuresVacuous (Lean.mkConst ``discardedLetPost) none (some .unboundReturnOutput)
#eval assertEnsuresVacuous (Lean.mkConst ``inputOnlyPost) none (some .unboundReturnOutput)
#eval assertEnsuresVacuous (Lean.mkConst ``optEmptyPost) none (some .unboundReturnOutput)
#eval assertDeclEnsuresVacuous ``memOnlyStatefulClaim (some .unboundReturnOutput)
  { strictReturnValue := true }
#eval assertDeclEnsuresVacuous ``boilerplateOnlyExtContract (some .unboundReturnOutput)
#eval assertDeclEnsuresVacuous ``restatedFrameContract (some .unboundReturnOutput)

/-! ### Class 5: `SurvivedAllMutants` -/

def survivedPre (x : Nat) : Prop := x < 10
def survivedDisjPost (x ret : Nat) : Prop := x < 10 ∨ ret = 42
def survivedImpPost (x ret : Nat) : Prop := x ≥ 10 → ret = 42

theorem survivedDisj_not_dichotomy :
    ¬ PostconditionDichotomy survivedPre survivedDisjPost :=
  not_postconditionDichotomy_of_trivial (fun _ _ hPre => Or.inl hPre)

theorem survivedImp_not_dichotomy :
    ¬ PostconditionDichotomy survivedPre survivedImpPost :=
  not_postconditionDichotomy_of_trivial (fun _ _ hPre hGe => by
    dsimp [survivedPre] at hPre
    omega)

#eval assertEnsuresVacuous
  (Lean.mkConst ``survivedDisjPost) (some (Lean.mkConst ``survivedPre)) (some .survivedAllMutants)
#eval assertEnsuresVacuous
  (Lean.mkConst ``survivedImpPost) (some (Lean.mkConst ``survivedPre)) (some .survivedAllMutants)

#eval show Lean.Meta.MetaM Unit from do
  let resSat ← checkRequiresSatisfiable (Lean.mkConst ``survivedPre)
  unless resSat.satisfiable? == some true do
    throwError "expected survivedPre satisfiable, got {repr resSat}"

/-! ### Explicit Domain Traps 1, 2, 3 on `externalSpecCallContract` -/

/-- Trap 1 fixture: `externalSpecCallContract` with contradictory `extraPost := False`. -/
def trap1FalsePostContract : MirCallContract :=
  externalSpecCallContract "core::slice::is_empty" sliceIsEmptySidecar
    sliceIsEmptyPre (fun _ _ => False)

theorem trap1_naive_realizable_passes :
    ContractRealizable trap1FalsePostContract.pre trap1FalsePostContract.post :=
  (externalSpecCallContract_naive_realizable_iff_preSatisfiable
      "core::slice::is_empty" sliceIsEmptySidecar sliceIsEmptyPre (fun _ _ => False)).mpr
    ⟨{ defPath := "core::slice::is_empty",
       args := [.scalar { bits := 0, sizeBytes := 8 }],
       memory := emptyMemory },
     ⟨rfl, rfl, ⟨⟨0, by decide, rfl⟩, trivial⟩, ⟨0, by decide, rfl⟩⟩⟩

theorem trap1_normal_realizable_fails :
    ¬ MirCallContractRealizable trap1FalsePostContract :=
  not_mirCallContractRealizable_externalSpec_false_post
    "core::slice::is_empty" sliceIsEmptySidecar sliceIsEmptyPre

#eval assertDeclEnsuresVacuous ``trap1FalsePostContract (some .specViolation)

/-- Trap 2 fixture: nounwind `externalSpecCallContract` with empty `localDecls` and
    trivial `extraPost := True` (generic dichotomy holds via `.returned` vs `.panicked`). -/
def trap2NoUnwindSidecar : CapturedMir :=
  mkStubBody "ffi::nounwind_noop" 0 [] boolLayout false

def trap2Contract : MirCallContract :=
  externalSpecCallContract "ffi::nounwind_noop" trap2NoUnwindSidecar
    (fun _ => True) (fun _ _ => True)

theorem trap2_generic_dichotomy_passes :
    PostconditionDichotomy trap2Contract.pre trap2Contract.post := by
  let req : MirCallReq := { defPath := "ffi::nounwind_noop", args := [], memory := emptyMemory }
  refine ⟨req, ⟨rfl, rfl, trivial, trivial⟩,
    ⟨.returned .unit emptyMemory, ⟨callFramePreserved_refl emptyMemory, trivial, trivial⟩⟩,
    ⟨.panicked emptyMemory, fun h => h⟩⟩

theorem trap2_ensuresDichotomy_fails :
    ¬ ExternalSpecEnsuresDichotomy "ffi::nounwind_noop" trap2NoUnwindSidecar
        (fun _ => True) (fun _ _ => True) :=
  not_externalSpecEnsuresDichotomy_of_trivial_extraPost
    "ffi::nounwind_noop" trap2NoUnwindSidecar (fun _ => True) (fun _ _ => trivial)

theorem trap2_strict_separation :
    ∃ c : MirCallContract,
      PostconditionDichotomy c.pre c.post ∧ ¬ MirCallContractNormalDichotomy c :=
  normalDichotomy_strictly_stronger_than_dichotomy.2

/-- Trap 3: `boilerplateOnlyExtContract` passes `MirCallContractNormalDichotomy` solely
    because `retMatchesCalleeReturnTy` rejects `.unit`, yet fails
    `ExternalSpecEnsuresDichotomy` modulo boilerplate observations. -/
theorem trap3_normalDichotomy_passes_via_boilerplate :
    MirCallContractNormalDichotomy boilerplateOnlyExtContract := by
  let req : MirCallReq := {
    defPath := "core::slice::is_empty"
    args := [.scalar { bits := 0, sizeBytes := 8 }]
    memory := emptyMemory
  }
  refine ⟨req, .scalar { bits := 1, sizeBytes := 1 }, emptyMemory, .unit, emptyMemory,
    ⟨rfl, rfl, ⟨⟨0, by decide, rfl⟩, trivial⟩, ⟨0, by decide, rfl⟩⟩,
    ⟨callFramePreserved_refl emptyMemory, ⟨1, by decide, rfl⟩, trivial⟩,
    ?_⟩
  rintro ⟨_, ⟨b, _, hEq⟩, _⟩
  cases hEq

theorem trap3_ensuresDichotomy_fails :
    ¬ ExternalSpecEnsuresDichotomy "core::slice::is_empty" sliceIsEmptySidecar
        sliceIsEmptyPre (fun _ _ => True) :=
  boilerplateOnlyExt_not_ensuresDichotomy

/-! ## 3. Checker Hardening Regression Suite -/

/-! ### 3.1 Probe Budgets: Heartbeat Exhaustion Is Contained and Never Unlimited -/

/-- `cappedHeartbeats?` never yields `0` (Lean's "unlimited" `maxHeartbeats` sentinel):
    every cap it returns is at least one `maxHeartbeats` option unit. -/
theorem cappedHeartbeats_never_unlimited (remaining stepUnits cap : Nat)
    (h : cappedHeartbeats? remaining stepUnits = some cap) : 1000 ≤ cap := by
  unfold cappedHeartbeats? at h
  split at h
  · cases h
  · cases h
    exact Nat.le_max_left _ _

theorem cappedHeartbeats_exhausted (stepUnits : Nat) :
    cappedHeartbeats? 0 stepUnits = none :=
  rfl

/-- The total probe budget is never `0`, and under a limited enclosing `maxHeartbeats`
    context it never exceeds what that context has left. -/
theorem clampProbeBudget_bounds (requested : Nat) (outer? : Option Nat) :
    1000 ≤ clampProbeBudget requested outer? ∧
      ∀ outer, outer? = some outer →
        clampProbeBudget requested outer? ≤ max 1000 outer := by
  cases outer? with
  | none => exact ⟨Nat.le_max_left _ _, fun _ h => by cases h⟩
  | some remaining =>
    refine ⟨Nat.le_max_left _ _, fun outer h => ?_⟩
    cases h
    show max 1000 (min (max 1000 requested) (remaining / 4 * 3)) ≤ max 1000 remaining
    omega

/-- Genuine nonlinear postcondition used to starve the bounded prover. -/
def budgetProbePost (x ret : Nat) : Prop :=
  ∃ a b c : Nat, a + b + c = x ∧ ret = a * b + c ∧ (a < 3 ∨ b < 5 ∨ c < 7)

theorem budgetProbePost_dichotomy :
    PostconditionDichotomy (fun _ : Nat => True) budgetProbePost := by
  refine ⟨0, trivial, ⟨0, 0, 0, 0, rfl, rfl, Or.inl (by decide)⟩, ⟨1, ?_⟩⟩
  rintro ⟨a, b, c, hSum, hRet, _⟩
  have ha : a = 0 := by omega
  have hc : c = 0 := by omega
  subst ha
  subst hc
  omega

#eval show Lean.Meta.MetaM Unit from do
  -- A heartbeat-hungry computation under a 1000-heartbeat cap is cut off and reported
  -- as `none`: heartbeat exhaustion is a runtime exception that must not escape.
  let cutOff ← withBoundedHeartbeats 1000 do
    let mut acc := Lean.mkNatLit 0
    for i in [0:20000] do
      acc ← Lean.Meta.whnf (Lean.mkNatAdd acc (Lean.mkNatLit i))
      Lean.Core.checkSystem "SpecRealizabilityTests budget probe"
    return acc
  if cutOff.isSome then
    throwError "expected withBoundedHeartbeats to cut off an over-budget computation"
  -- With a one-unit per-snippet cap every prover probe times out. The checker must
  -- still return a verdict (an undecided probe never flags) instead of throwing.
  let starved ← checkEnsuresBindsOutput (Lean.mkConst ``budgetProbePost) none
    { stepHeartbeats := 1, totalHeartbeats := 250000 }
  unless starved.bindsOutput do
    throwError "expected starved probes to leave a genuine ensures accepted, got {repr starved}"
  -- A zero budget degrades to the purely syntactic phases, which still catch `True`.
  let zeroBudget ← checkEnsuresBindsOutput (Lean.mkConst ``trivTruePost) none
    { stepHeartbeats := 0, totalHeartbeats := 0 }
  unless zeroBudget.vacuityClass? == some .trivialPostcondition do
    throwError "expected zero-budget check to flag `True`, got {repr zeroBudget}"
  -- The default total budget is clamped to three quarters of what the enclosing
  -- `maxHeartbeats` context has left, so probes run dry before the outer limit.
  let now ← IO.getNumHeartbeats
  let clamped ← withTheReader Lean.Core.Context
    (fun ctx => { ctx with initHeartbeats := now, maxHeartbeats := 8000000 })
    (ProbeBudget.init {} : Lean.Meta.MetaM ProbeBudget)
  unless 1000 ≤ clamped.totalInternal && clamped.totalInternal ≤ 6000000 do
    throwError "expected a clamped total probe budget, got {clamped.totalInternal}"

/-! ### 3.2 `strictReturnValue`: Mentioning `retVal` Is Not Constraining It -/

/-- Pins `mem'` but only mentions `retVal` reflexively. -/
def reflRetStatefulClaim : StatefulClaim := {
  body := statefulCounterStepBody
  pre := fun _ _ => True
  post := fun _ mem retVal mem' => retVal = retVal ∧ mem' = mem
}

theorem reflRetStateful_not_returnDichotomy :
    ¬ StatefulClaimReturnDichotomy reflRetStatefulClaim :=
  not_statefulClaimReturnDichotomy_of_returnInsensitive
    (fun _ _ _ _ _ _ h => ⟨rfl, h.2⟩)

theorem reflRetStateful_dichotomy :
    StatefulClaimDichotomy reflRetStatefulClaim := by
  refine ⟨([], emptyMemory), trivial,
    ⟨(.unit, emptyMemory), ⟨rfl, rfl⟩⟩,
    ⟨(.unit, { emptyMemory with nextTag := 2 }), ?_⟩⟩
  rintro ⟨_, hEq⟩
  exact memory_nextTag_ne_1_2 hEq.symm

#eval assertDeclEnsuresVacuous ``reflRetStatefulClaim (some .unboundReturnOutput)
  { strictReturnValue := true }
-- Without `strictReturnValue` the pair `(retVal, mem')` is the output, and `mem' = mem`
-- does constrain it.
#eval assertDeclEnsuresBindsOutput ``reflRetStatefulClaim

/-! ### 3.3 Empty and Subsingleton Output Types: Recursive Inductives -/

/-- Uninhabited recursive inductive: its only constructor needs an inhabitant. -/
inductive EndlessChain : Type where
  | link : EndlessChain → EndlessChain

/-- Inhabited nested recursive inductive (`node []`). -/
inductive RoseTree : Type where
  | node : List RoseTree → RoseTree

/-- Non-recursive wrapper used to nest one type instance inside another. -/
structure Boxed (α : Type) : Type where
  val : α

theorem endlessChain_isEmpty (c : EndlessChain) : False := by
  induction c with
  | link _ ih => exact ih

theorem optionEndlessChain_subsingleton : Subsingleton (Option EndlessChain) :=
  ⟨fun a b => by
    cases a with
    | none =>
      cases b with
      | none => rfl
      | some c => exact (endlessChain_isEmpty c).elim
    | some c => exact (endlessChain_isEmpty c).elim⟩

def endlessChainPost (_x : Nat) (ret : EndlessChain) : Prop := ret = .link ret
def optEndlessChainPost (_x : Nat) (ret : Option EndlessChain) : Prop := ret = none
def optFinZeroPost (_x : Nat) (ret : Option (Fin 0)) : Prop := ret = none
def prodUnitEmptyPost (_x : Nat) (ret : Unit × Empty) : Prop := ret.1 = ()
def roseTreePost (_x : Nat) (ret : RoseTree) : Prop := ret = .node []
def listNatPost (x : Nat) (ret : List Nat) : Prop := ret = [x]
def boxedBoxedPost (x : Nat) (ret : Boxed (Boxed Nat)) : Prop := ret.val.val = x

theorem endlessChainPost_not_realizable :
    ¬ ContractRealizable (fun _ : Nat => True) endlessChainPost := by
  rintro ⟨_, _, c, _⟩
  exact endlessChain_isEmpty c

theorem optEndlessChainPost_not_dichotomy :
    ¬ PostconditionDichotomy (fun _ : Nat => True) optEndlessChainPost :=
  @not_postconditionDichotomy_of_subsingleton _ _ optionEndlessChain_subsingleton _ _

theorem roseTreePost_dichotomy :
    PostconditionDichotomy (fun _ : Nat => True) roseTreePost :=
  ⟨0, trivial, ⟨.node [], rfl⟩,
    ⟨.node [.node []], fun h => List.cons_ne_nil _ _ (RoseTree.node.inj h)⟩⟩

theorem listNatPost_dichotomy :
    PostconditionDichotomy (fun _ : Nat => True) listNatPost :=
  ⟨0, trivial, ⟨[0], rfl⟩, ⟨[], fun h => List.cons_ne_nil 0 [] (Eq.symm h)⟩⟩

theorem boxedBoxedPost_dichotomy :
    PostconditionDichotomy (fun _ : Nat => True) boxedBoxedPost :=
  ⟨0, trivial, ⟨⟨⟨0⟩⟩, rfl⟩, ⟨⟨⟨1⟩⟩, fun h => Nat.succ_ne_zero 0 h⟩⟩

#eval assertEnsuresVacuous (Lean.mkConst ``endlessChainPost) none (some .unboundReturnOutput)
#eval assertEnsuresVacuous (Lean.mkConst ``optEndlessChainPost) none (some .unboundReturnOutput)
#eval assertEnsuresVacuous (Lean.mkConst ``optFinZeroPost) none (some .unboundReturnOutput)
#eval assertEnsuresVacuous (Lean.mkConst ``prodUnitEmptyPost) none (some .unboundReturnOutput)
-- Inhabited recursive, list, and nested-instance output types must not be flagged.
#eval assertEnsuresBindsOutput (Lean.mkConst ``roseTreePost)
#eval assertEnsuresBindsOutput (Lean.mkConst ``listNatPost)
#eval assertEnsuresBindsOutput (Lean.mkConst ``boxedBoxedPost)

/-! ### 3.4 `r ≤ r` Is Only Trivial for a Reflexive Order -/

/-- Float-like value: comparisons involving a non-number are false. -/
structure MaybeNaN : Type where
  isNumber : Bool
  magnitude : Nat

instance : LE MaybeNaN :=
  ⟨fun a b => a.isNumber = true ∧ b.isNumber = true ∧ a.magnitude ≤ b.magnitude⟩

/-- `ret ≤ ret` holds exactly when `ret` is a number: a genuine constraint. -/
def notNaNPost (_x : Nat) (ret : MaybeNaN) : Prop := ret ≤ ret

def natLeReflPost (_x ret : Nat) : Prop := ret ≤ ret

theorem notNaNPost_dichotomy :
    PostconditionDichotomy (fun _ : Nat => True) notNaNPost := by
  refine ⟨0, trivial, ⟨⟨true, 0⟩, ⟨rfl, rfl, Nat.le_refl 0⟩⟩, ⟨⟨false, 0⟩, ?_⟩⟩
  rintro ⟨hNumber, _⟩
  cases hNumber

theorem natLeReflPost_not_dichotomy :
    ¬ PostconditionDichotomy (fun _ : Nat => True) natLeReflPost :=
  not_postconditionDichotomy_of_trivial (fun _ ret _ => Nat.le_refl ret)

#eval assertEnsuresBindsOutput (Lean.mkConst ``notNaNPost)
#eval assertEnsuresVacuous (Lean.mkConst ``natLeReflPost) none (some .trivialPostcondition)

/-! ### 3.5 Output Hidden Behind a Definition That Ignores It -/

def hiddenInputOnlyPost (x ret : Nat) : Prop := inputOnlyPost x ret

def hiddenWrapperPost : Nat → Nat → Prop := fun x ret => hiddenInputOnlyPost x ret

theorem hiddenWrapperPost_not_dichotomy :
    ¬ PostconditionDichotomy (fun _ : Nat => True) hiddenWrapperPost :=
  not_postconditionDichotomy_of_forwardOutputInsensitive (fun _ _ _ _ h => h)

#eval assertEnsuresVacuous (Lean.mkConst ``hiddenInputOnlyPost) none (some .unboundReturnOutput)
#eval assertEnsuresVacuous (Lean.mkConst ``hiddenWrapperPost) none (some .unboundReturnOutput)

/-! ### 3.6 Input-Only Postconditions: Tautological, Contradictory, or Unbound -/

def inputOnlyReflPost (x _ret : Nat) : Prop := x = x
def inputOnlyArithTautPost (x _ret : Nat) : Prop := x < 10 ∨ x ≥ 10
def inputOnlyContraPost (x _ret : Nat) : Prop := x < x

theorem inputOnlyArithTautPost_not_dichotomy :
    ¬ PostconditionDichotomy (fun _ : Nat => True) inputOnlyArithTautPost :=
  not_postconditionDichotomy_of_trivial (fun x _ _ => by
    show x < 10 ∨ x ≥ 10
    omega)

theorem inputOnlyContraPost_not_realizable :
    ¬ ContractRealizable (fun _ : Nat => True) inputOnlyContraPost := by
  rintro ⟨x, _, _, hLt⟩
  exact Nat.lt_irrefl x hLt

#eval assertEnsuresVacuous (Lean.mkConst ``inputOnlyReflPost) none (some .trivialPostcondition)
#eval assertEnsuresVacuous (Lean.mkConst ``inputOnlyArithTautPost) none (some .trivialPostcondition)
#eval assertEnsuresVacuous (Lean.mkConst ``inputOnlyContraPost) none (some .specViolation)
-- An input-only postcondition that is neither is still an unbound-output specification.
#eval assertEnsuresVacuous (Lean.mkConst ``inputOnlyPost) none (some .unboundReturnOutput)

/-! ### 3.7 Boilerplate Cofactoring: Contradictory Fibres, Insensitive Residuals, `requires` -/

open scoped Classical in
/-- Trap 3 variant: the frame-preserving fibre accepts every return value and the other
    fibre accepts none, so no fibre distinguishes return values even though the two
    fibres differ. The second fibre is contradictory but not syntactically `False`. -/
def contradictoryFibreContract : MirCallContract := {
  pre := fun _ => True
  post := fun req ans =>
    match ans with
    | .returned retVal memAfter =>
      if callFramePreserved req.memory memAfter then
        True
      else
        retVal = .unit ∧ retVal = .scalar { bits := 1, sizeBytes := 4 }
    | .panicked _ => False
    | .aborted => True
}

open scoped Classical in
theorem contradictoryFibre_not_returnValueDichotomy :
    ¬ MirCallContractReturnValueDichotomy contradictoryFibreContract := by
  rintro ⟨req, m, v_ok, v_bad, _, hOk, hBad⟩
  by_cases hFrame : callFramePreserved req.memory m
  · apply hBad
    show if callFramePreserved req.memory m then True
      else v_bad = .unit ∧ v_bad = .scalar { bits := 1, sizeBytes := 4 }
    rw [ite_eq_left hFrame]
    trivial
  · have hOk' : if callFramePreserved req.memory m then True
        else v_ok = .unit ∧ v_ok = .scalar { bits := 1, sizeBytes := 4 } := hOk
    rw [ite_eq_right hFrame] at hOk'
    have hEq : Value.unit = Value.scalar { bits := 1, sizeBytes := 4 } :=
      hOk'.1.symm.trans hOk'.2
    cases hEq

/-- External spec whose user `ensures` mentions `ret` but constrains only the inputs
    in a way compatible with `sliceIsEmptySidecar.argCount = 1`. -/
def argsEmptyIgnoringRetPost (args : List Value) (ret : Value) : Prop :=
  ret = ret ∧ args.length = 1

/-- External spec whose input-only `ensures` (`args = []`) contradicts `argCount = 1`,
    making normal return unrealizable (`SpecViolation`). -/
def argsEmptyContraRetPost (args : List Value) (ret : Value) : Prop :=
  ret = ret ∧ args = []

def argsEmptyIgnoringRetExtContract : MirCallContract :=
  externalSpecCallContract "core::slice::is_empty" sliceIsEmptySidecar
    (fun _ => True) argsEmptyIgnoringRetPost

def argsEmptyContraRetExtContract : MirCallContract :=
  externalSpecCallContract "core::slice::is_empty" sliceIsEmptySidecar
    (fun _ => True) argsEmptyContraRetPost

theorem argsEmptyIgnoringRet_not_ensuresDichotomy :
    ¬ ExternalSpecEnsuresDichotomy "core::slice::is_empty" sliceIsEmptySidecar
        (fun _ => True) argsEmptyIgnoringRetPost := by
  intro h
  rcases (externalSpecEnsuresDichotomy_iff_moduloObservation
    "core::slice::is_empty" sliceIsEmptySidecar (fun _ => True) argsEmptyIgnoringRetPost).mp h with
    ⟨_, _, _, _, _, _, _, _, hOk, hBad⟩
  exact hBad ⟨rfl, hOk.2⟩

/-- Call contract whose normal-return `ensures` binds `retVal` only outside `requires`. -/
def vacuousUnderRequiresCallContract : MirCallContract := {
  pre := fun req => req.args = []
  post := fun req ans =>
    match ans with
    | .returned retVal memAfter =>
      callFramePreserved req.memory memAfter ∧ (req.args = [] ∨ retVal = .unit)
    | .panicked _ => False
    | .aborted => True
}

theorem vacuousUnderRequiresCall_not_returnValueDichotomy :
    ¬ MirCallContractReturnValueDichotomy vacuousUnderRequiresCallContract :=
  not_mirCallContractReturnValueDichotomy_of_returnInsensitive
    (fun _ _ _ _ hPre h => ⟨h.1, Or.inl hPre⟩)

/-- Propositional tautology over a boilerplate atom. -/
def boilerplateExcludedMiddleContract : MirCallContract := {
  pre := fun _ => True
  post := fun req ans =>
    match ans with
    | .returned _ memAfter =>
      callFramePreserved req.memory memAfter ∨ ¬ callFramePreserved req.memory memAfter
    | .panicked _ => False
    | .aborted => True
}

/-- Biconditional between the two boilerplate atoms: no user constraint at all. -/
def boilerplateIffContract : MirCallContract := {
  pre := fun _ => True
  post := fun req ans =>
    match ans with
    | .returned retVal memAfter =>
      callFramePreserved req.memory memAfter ↔
        retMatchesCalleeReturnTy sliceIsEmptySidecar retVal
    | .panicked _ => False
    | .aborted => True
}

/-- Genuine conditional contract: the frame condition guards a return-value constraint. -/
def frameImpliesRetContract : MirCallContract := {
  pre := fun _ => True
  post := fun req ans =>
    match ans with
    | .returned retVal memAfter =>
      callFramePreserved req.memory memAfter →
        retVal = .scalar { bits := 7, sizeBytes := 4 }
    | .panicked _ => False
    | .aborted => True
}

theorem frameImpliesRet_returnValueDichotomy :
    MirCallContractReturnValueDichotomy frameImpliesRetContract := by
  let req : MirCallReq := { defPath := "", args := .nil, memory := emptyMemory }
  refine ⟨req, emptyMemory, .scalar { bits := 7, sizeBytes := 4 }, .unit,
    trivial, fun _ => rfl, ?_⟩
  intro hImp
  have hEq : Value.unit = Value.scalar { bits := 7, sizeBytes := 4 } :=
    hImp (callFramePreserved_refl emptyMemory)
  cases hEq

#eval assertDeclEnsuresVacuous ``contradictoryFibreContract (some .unboundReturnOutput)
#eval assertDeclEnsuresVacuous ``argsEmptyIgnoringRetExtContract (some .unboundReturnOutput)
#eval assertDeclEnsuresVacuous ``argsEmptyContraRetExtContract (some .specViolation)
#eval assertDeclEnsuresVacuous ``vacuousUnderRequiresCallContract (some .survivedAllMutants)
#eval assertDeclEnsuresVacuous ``boilerplateExcludedMiddleContract (some .trivialPostcondition)
#eval assertDeclEnsuresVacuous ``boilerplateIffContract (some .unboundReturnOutput)
-- Genuine conditional contracts must pass, with and without `strictReturnValue`.
#eval assertDeclEnsuresBindsOutput ``frameImpliesRetContract
#eval assertDeclEnsuresBindsOutput ``frameImpliesRetContract { strictReturnValue := true }
#eval assertDeclEnsuresBindsOutput ``condFrameContract { strictReturnValue := true }

/-! ### 3.8 Dependent Types: Substituted Goals Are Type-Checked Before Proving -/

/-- Genuine postcondition over an output whose type depends on the input. -/
def finSuccPost (n : Nat) (ret : Fin (n + 1)) : Prop := ret.val = n

/-- Precondition whose second input has a type depending on the first. -/
def dependentRequires (n : Nat) (i : Fin (n + 1)) : Prop := i.val = n

theorem dependentRequires_satisfiable :
    ∃ (n : Nat) (i : Fin (n + 1)), dependentRequires n i :=
  ⟨0, 0, rfl⟩

/-- Single-valued structure known to be a subsingleton only through its instance. -/
structure SoleToken : Type where
  token : Unit

instance : Subsingleton SoleToken :=
  ⟨fun a b => by
    cases a
    cases b
    rfl⟩

def soleTokenPost (_x : Nat) (ret : SoleToken) : Prop := ret = ⟨()⟩

theorem soleTokenPost_not_dichotomy :
    ¬ PostconditionDichotomy (fun _ : Nat => True) soleTokenPost :=
  not_postconditionDichotomy_of_subsingleton

/-- Trivially true precondition over an input type that is inhabited only by instance. -/
def soleTokenRequires (_t : SoleToken) : Prop := True

instance : Inhabited SoleToken := ⟨⟨()⟩⟩

/-- Trivially true precondition guarded by an unprovable hypothesis binder. -/
def absurdHypRequires (x : Nat) (_h : x < x) : Prop := True

theorem absurdHypRequires_unsatisfiable :
    ¬ ∃ (x : Nat) (h : x < x), absurdHypRequires x h := by
  rintro ⟨x, h, _⟩
  exact Nat.lt_irrefl x h

#eval assertEnsuresBindsOutput (Lean.mkConst ``finSuccPost)
-- `Subsingleton`, `Inhabited`, and `Nonempty` are `Sort`-polymorphic: instances must be
-- synthesized at the sort level of the type itself.
#eval assertEnsuresVacuous (Lean.mkConst ``soleTokenPost) none (some .unboundReturnOutput)

#eval show Lean.Meta.MetaM Unit from do
  let nat := Lean.mkConst ``Nat
  let eqNat (a b : Lean.Expr) : Lean.Expr :=
    Lean.mkApp3 (Lean.mkConst ``Eq [Lean.Level.succ Lean.Level.zero]) nat a b
  -- Positive control: `∀ n : Nat, n = n` is provable.
  let reflGoal := Lean.mkForall `n .default nat (eqNat (Lean.mkBVar 0) (Lean.mkBVar 0))
  unless ← tryProve reflGoal do
    throwError "expected tryProve to prove `∀ n : Nat, n = n`"
  -- `@Eq Nat True True` looks reflexive but is ill-typed (`True` is not a `Nat`): the
  -- prover must refuse it rather than report a proof.
  let illTyped := eqNat (Lean.mkConst ``True) (Lean.mkConst ``True)
  if ← tryProve illTyped then
    throwError "tryProve accepted an ill-typed goal"
  -- A non-proposition is never proved.
  if ← tryProve nat then
    throwError "tryProve accepted a non-proposition"
  -- The canonical witness for a dependent input is typed against the witnesses already
  -- chosen for the inputs it depends on.
  let depSat ← checkRequiresSatisfiable (Lean.mkConst ``dependentRequires)
  unless depSat.satisfiable? == some true do
    throwError "expected dependentRequires satisfiable, got {repr depSat}"
  -- `True` over an input type that is inhabited by instance is satisfiable.
  let tokenSat ← checkRequiresSatisfiable (Lean.mkConst ``soleTokenRequires)
  unless tokenSat.satisfiable? == some true do
    throwError "expected soleTokenRequires satisfiable, got {repr tokenSat}"
  -- A hypothesis binder is never assumed inhabited: `True` behind `h : x < x` is dead.
  let absurdSat ← checkRequiresSatisfiable (Lean.mkConst ``absurdHypRequires)
  unless absurdSat.satisfiable? == some false do
    throwError "expected absurdHypRequires unsatisfiable, got {repr absurdSat}"

/-! ### 3.9 Unreachable Boilerplate Fibres & Input-Only Boilerplate Residuals -/

open scoped Classical in
/-- Tautological frame atom (`callFramePreserved req.memory req.memory`) cannot hide an
    unbound return value behind its impossible `else` branch. -/
def reflMaskBypassContract : MirCallContract := {
  pre := fun _ => True
  post := fun req ans =>
    match ans with
    | .returned retVal memAfter =>
      if callFramePreserved req.memory req.memory then
        callFramePreserved req.memory memAfter
      else
        retVal = .unit
    | .panicked _ => False
    | .aborted => True
}

open scoped Classical in
theorem reflMaskBypass_not_returnValueDichotomy :
    ¬ MirCallContractReturnValueDichotomy reflMaskBypassContract := by
  rintro ⟨req, m, v_ok, v_bad, _, hOk, hBad⟩
  have hRefl : callFramePreserved req.memory req.memory := callFramePreserved_refl req.memory
  have hOk' : if callFramePreserved req.memory req.memory then
      callFramePreserved req.memory m else v_ok = .unit := hOk
  rw [ite_eq_left hRefl] at hOk'
  apply hBad
  show if callFramePreserved req.memory req.memory then
    callFramePreserved req.memory m else v_bad = .unit
  rw [ite_eq_left hRefl]
  exact hOk'

open scoped Classical in
/-- `memAfter = req.memory` implies `callFramePreserved req.memory memAfter`, so the
    `else` branch constraining `retVal` is unreachable. -/
def eqMemMaskBypassContract : MirCallContract := {
  pre := fun _ => True
  post := fun req ans =>
    match ans with
    | .returned retVal memAfter =>
      memAfter = req.memory ∧
      (if callFramePreserved req.memory memAfter then
        True
      else
        retVal = .unit)
    | .panicked _ => False
    | .aborted => True
}

open scoped Classical in
theorem eqMemMaskBypass_not_returnValueDichotomy :
    ¬ MirCallContractReturnValueDichotomy eqMemMaskBypassContract := by
  rintro ⟨req, m, v_ok, v_bad, _, hOk, hBad⟩
  have hEq : m = req.memory := hOk.1
  have hFrame : callFramePreserved req.memory m := by
    rw [hEq]
    exact callFramePreserved_refl req.memory
  apply hBad
  refine ⟨hEq, ?_⟩
  show if callFramePreserved req.memory m then True else v_bad = .unit
  rw [ite_eq_left hFrame]
  trivial

/-- Contradictory input-only residual behind a boilerplate guard is `SpecViolation`,
    not `UnboundReturnOutput`. -/
def contraInputOnlyBoilerplateContract : MirCallContract := {
  pre := fun req => req.args = []
  post := fun req ans =>
    match ans with
    | .returned _ memAfter =>
      callFramePreserved req.memory memAfter ∧ req.args ≠ []
    | .panicked _ => False
    | .aborted => True
}

theorem contraInputOnlyBoilerplate_not_realizable :
    ¬ MirCallContractRealizable contraInputOnlyBoilerplateContract := by
  rintro ⟨req, _, _, hPre, _, hNe⟩
  exact hNe hPre

/-- Tautological input-only disjunct beside a boilerplate atom is `TrivialPostcondition`. -/
def tautInputOnlyBoilerplateContract : MirCallContract := {
  pre := fun _ => True
  post := fun req ans =>
    match ans with
    | .returned _ memAfter =>
      callFramePreserved req.memory memAfter ∨ req.args = req.args
    | .panicked _ => False
    | .aborted => True
}

theorem tautInputOnlyBoilerplate_not_normalDichotomy :
    ¬ MirCallContractNormalDichotomy tautInputOnlyBoilerplateContract := by
  rintro ⟨_, _, _, _, _, _, _, hBad⟩
  exact hBad (Or.inr rfl)

#eval assertDeclEnsuresVacuous ``reflMaskBypassContract (some .unboundReturnOutput)
#eval assertDeclEnsuresVacuous ``reflMaskBypassContract (some .unboundReturnOutput)
  { strictReturnValue := true }
#eval assertDeclEnsuresVacuous ``eqMemMaskBypassContract (some .unboundReturnOutput)
  { strictReturnValue := true }
#eval assertDeclEnsuresVacuous ``eqMemMaskBypassContract (some .unboundReturnOutput)
  { strictReturnValue := true, userEnsuresOnly := false }
#eval assertDeclEnsuresVacuous ``contraInputOnlyBoilerplateContract (some .specViolation)
#eval assertDeclEnsuresVacuous ``tautInputOnlyBoilerplateContract (some .trivialPostcondition)

/-! ### 3.10 Projection Reduction, Nested Helper Predicates & Syntactic Disguises -/

/-- Custom two-field structure with no `@[simp]` lemmas on its projections. -/
structure PairBox (α β : Type) : Type where
  fst : α
  snd : β

def projDiscardStatefulClaim : StatefulClaim := {
  body := statefulCounterStepBody
  pre := fun _ _ => True
  post := fun _ mem retVal mem' => (PairBox.mk retVal mem').snd = mem
}

theorem projDiscardStateful_not_returnDichotomy :
    ¬ StatefulClaimReturnDichotomy projDiscardStatefulClaim :=
  not_statefulClaimReturnDichotomy_of_returnInsensitive
    (fun _ _ _ _ _ _ h => h)

def prodSndDiscardStatefulClaim : StatefulClaim := {
  body := statefulCounterStepBody
  pre := fun _ _ => True
  post := fun _ mem retVal mem' => (retVal, mem').2 = mem
}

theorem prodSndDiscardStateful_not_returnDichotomy :
    ¬ StatefulClaimReturnDichotomy prodSndDiscardStatefulClaim :=
  not_statefulClaimReturnDichotomy_of_returnInsensitive
    (fun _ _ _ _ _ _ h => h)

/-- Genuine postcondition projecting a binder-local variable under `∀` (must not
    trigger loose-bvar errors in `zetaBetaProjReduce`). -/
def quantifiedProjPost (x ret : Nat) : Prop :=
  ∀ p : Nat × Nat, p.1 = x → ret = x

theorem quantifiedProjPost_dichotomy :
    PostconditionDichotomy (fun _ : Nat => True) quantifiedProjPost := by
  refine ⟨0, trivial, ⟨0, fun _ _ => rfl⟩, ⟨1, ?_⟩⟩
  intro hAll
  have hEq : (1 : Nat) = 0 := hAll (0, 0) rfl
  exact Nat.succ_ne_zero 0 hEq

def discardedLetFalsePost (_x ret : Nat) : Prop :=
  let _ := ret
  False

theorem discardedLetFalse_not_realizable :
    ¬ ContractRealizable (fun _ : Nat => True) discardedLetFalsePost := by
  rintro ⟨_, _, _, hFalse⟩
  exact hFalse

def helperIgnoreRet (_ret : Nat) : Prop := True
def helperReflRet (ret : Nat) : Prop := ret = ret

def conjHelperIgnorePost (x ret : Nat) : Prop :=
  x < 100 ∧ helperIgnoreRet ret

def disjHelperReflPost (x ret : Nat) : Prop :=
  x < 100 ∨ helperReflRet ret

def symmEqIffPost (x ret : Nat) : Prop :=
  (ret = x) ↔ (x = ret)

def iteTautPost (x ret : Nat) : Prop :=
  if x < 10 then ret = ret else True

theorem conjHelperIgnorePost_not_dichotomy :
    ¬ PostconditionDichotomy (fun _ : Nat => True) conjHelperIgnorePost :=
  not_postconditionDichotomy_of_forwardOutputInsensitive (fun _ _ _ _ h => ⟨h.1, trivial⟩)

theorem disjHelperReflPost_not_dichotomy :
    ¬ PostconditionDichotomy (fun _ : Nat => True) disjHelperReflPost :=
  not_postconditionDichotomy_of_trivial (fun _ _ _ => Or.inr rfl)

theorem symmEqIffPost_not_dichotomy :
    ¬ PostconditionDichotomy (fun _ : Nat => True) symmEqIffPost :=
  not_postconditionDichotomy_of_trivial (fun _ _ _ => ⟨Eq.symm, Eq.symm⟩)

theorem iteTautPost_not_dichotomy :
    ¬ PostconditionDichotomy (fun _ : Nat => True) iteTautPost :=
  not_postconditionDichotomy_of_trivial (fun x ret _ => by
    show if x < 10 then ret = ret else True
    split
    · rfl
    · trivial)

#eval assertDeclEnsuresVacuous ``projDiscardStatefulClaim (some .unboundReturnOutput)
  { strictReturnValue := true }
#eval assertDeclEnsuresVacuous ``prodSndDiscardStatefulClaim (some .unboundReturnOutput)
  { strictReturnValue := true }
#eval assertEnsuresBindsOutput (Lean.mkConst ``quantifiedProjPost)
#eval assertEnsuresVacuous (Lean.mkConst ``discardedLetFalsePost) none (some .specViolation)
#eval assertEnsuresVacuous (Lean.mkConst ``conjHelperIgnorePost) none (some .unboundReturnOutput)
#eval assertEnsuresVacuous (Lean.mkConst ``disjHelperReflPost) none (some .trivialPostcondition)
#eval assertEnsuresVacuous (Lean.mkConst ``symmEqIffPost) none (some .trivialPostcondition)
  { stepHeartbeats := 0, totalHeartbeats := 0 }
#eval assertEnsuresVacuous (Lean.mkConst ``iteTautPost) none (some .trivialPostcondition)
  { stepHeartbeats := 0, totalHeartbeats := 0 }

/-! ### 3.11 Stateless `Memory`-Returning Specs & Conjunctive `requires` Unfolding -/

def statelessMemBuilderPre (a b c : Nat) : Prop := a + b + c < 100
def statelessMemBuilderPost (a _b _c : Nat) (ret : Memory) : Prop := ret.nextTag = a
def statelessMemBuilderBadPost (_a _b c : Nat) (_ret : Memory) : Prop := c = 0

theorem statelessMemBuilder_dichotomy :
    PostconditionDichotomy
      (fun t : Nat × Nat × Nat => statelessMemBuilderPre t.1 t.2.1 t.2.2)
      (fun t ret => statelessMemBuilderPost t.1 t.2.1 t.2.2 ret) := by
  refine ⟨(1, 0, 0), by dsimp [statelessMemBuilderPre]; decide,
    ⟨emptyMemory, rfl⟩,
    ⟨{ emptyMemory with nextTag := 2 }, ?_⟩⟩
  intro hEq
  dsimp [statelessMemBuilderPost, emptyMemory] at hEq
  omega

def hiddenContraClause (x : Nat) : Prop := x > 5 ∧ x < 3
def conjHiddenContraPre (x : Nat) : Prop := x < 100 ∧ hiddenContraClause x

theorem conjHiddenContraPre_not_satisfiable :
    ¬ PreconditionSatisfiable conjHiddenContraPre := by
  rintro ⟨x, hPre⟩
  rcases hPre with ⟨_, hClause⟩
  rcases hClause with ⟨hGt, hLt⟩
  omega

#eval assertEnsuresBindsOutput
  (Lean.mkConst ``statelessMemBuilderPost) (some (Lean.mkConst ``statelessMemBuilderPre))
#eval assertEnsuresBindsOutput
  (Lean.mkConst ``statelessMemBuilderPost) (some (Lean.mkConst ``statelessMemBuilderPre))
  { strictReturnValue := true }
#eval assertEnsuresVacuous
  (Lean.mkConst ``statelessMemBuilderBadPost) (some (Lean.mkConst ``statelessMemBuilderPre))
  (some .unboundReturnOutput)
#eval show Lean.Meta.MetaM Unit from do
  let res ← checkRequiresSatisfiable (Lean.mkConst ``conjHiddenContraPre)
  unless res.satisfiable? == some false do
    throwError "expected conjHiddenContraPre unsatisfiable, got {repr res}"

/-! ### 3.12 Nested `match ans`, Parameterized Contracts & Existential `requires` -/

/-- Helper predicate that re-matches on `ans`: its frame atom only becomes visible
    once the matcher is iota-reduced on `MirCallAns.returned retVal memAfter`. -/
def framedAnsHelper (req : MirCallReq) (ans : MirCallAns) : Prop :=
  match ans with
  | .returned _ memAfter => callFramePreserved req.memory memAfter
  | .panicked _ => False
  | .aborted => True

/-- Helper predicate hiding the return-type atom behind a second `match ans`. -/
def retTyAnsHelper (ans : MirCallAns) : Prop :=
  match ans with
  | .returned retVal _ => retMatchesCalleeReturnTy sliceIsEmptySidecar retVal
  | .panicked _ => False
  | .aborted => False

/-- Boilerplate-only contract whose atoms hide behind helper wrappers that re-match
    on `ans` under a conjunction. -/
def nestedMatchBoilerplateContract : MirCallContract := {
  pre := fun _ => True
  post := fun req ans => framedAnsHelper req ans ∧ retTyAnsHelper ans
}

/-- The normal-return postcondition is exactly the auto-generated boilerplate. -/
theorem nestedMatchBoilerplate_post_returned
    (req : MirCallReq) (retVal : Value) (memAfter : Memory) :
    nestedMatchBoilerplateContract.post req (.returned retVal memAfter) ↔
      (callFramePreserved req.memory memAfter ∧
        retMatchesCalleeReturnTy sliceIsEmptySidecar retVal) :=
  Iff.rfl

/-- Genuine contract behind the same helper plus an inline nested `match ans`: iota
    reduction must expose, not erase, the return-value constraint. -/
def nestedMatchGenuineContract : MirCallContract := {
  pre := fun _ => True
  post := fun req ans =>
    framedAnsHelper req ans ∧
    (match ans with
     | .returned retVal _ => retVal = Value.unit
     | .panicked _ => False
     | .aborted => False)
}

theorem nestedMatchGenuine_returnValueDichotomy :
    MirCallContractReturnValueDichotomy nestedMatchGenuineContract := by
  let req : MirCallReq := { defPath := "", args := .nil, memory := emptyMemory }
  refine ⟨req, emptyMemory, Value.unit, .scalar { bits := 7, sizeBytes := 4 },
    trivial, ⟨callFramePreserved_refl emptyMemory, rfl⟩, ?_⟩
  rintro ⟨_, hRet⟩
  have hEq : Value.scalar { bits := 7, sizeBytes := 4 } = Value.unit := hRet
  cases hEq

/-- Parameterized contract: `checkDeclEnsuresBindsOutput` must open the declaration's
    own parameters instead of misreading `Nat → Claim` as a non-`Prop` predicate. -/
def boundedEchoClaim (bound : Nat) : Claim := {
  body := sliceIsEmptySidecar
  pre := fun args => ∃ n : Nat, n < bound ∧ args = [.scalar { bits := n, sizeBytes := 8 }]
  post := fun args ret => args = [ret]
}

theorem boundedEchoClaim_dichotomy : ClaimDichotomy (boundedEchoClaim 1) := by
  refine ⟨[.scalar { bits := 0, sizeBytes := 8 }], ⟨0, by decide, rfl⟩,
    ⟨.scalar { bits := 0, sizeBytes := 8 }, rfl⟩,
    ⟨Value.unit, ?_⟩⟩
  intro hPost
  have hList : [Value.scalar { bits := 0, sizeBytes := 8 }] = [Value.unit] := hPost
  have hVal : Value.scalar { bits := 0, sizeBytes := 8 } = Value.unit :=
    list_singleton_inj hList
  cases hVal

/-- Parameterized contract whose `ensures` is trivial at every instantiation. -/
def boundedTrivialClaim (bound : Nat) : Claim := {
  body := sliceIsEmptySidecar
  pre := fun args => ∃ n : Nat, n < bound ∧ args = [.scalar { bits := n, sizeBytes := 8 }]
  post := fun _ _ => True
}

theorem boundedTrivialClaim_not_dichotomy (bound : Nat) :
    ¬ ClaimDichotomy (boundedTrivialClaim bound) := by
  rintro ⟨_, _, _, ⟨_, hBad⟩⟩
  exact hBad trivial

/-- Existential list-encoded `requires`, the shape of `sliceIsEmptyPre`. -/
def existsLenPre (args : List Value) : Prop :=
  ∃ len : Nat, len < 10 ∧ args = [.scalar { bits := len, sizeBytes := 8 }]

/-- Vacuous under the existential `requires`: every admissible `len` already satisfies
    the left disjunct, so `ret` is constrained only outside the precondition. -/
def existsLenVacuousPost (args : List Value) (ret : Value) : Prop :=
  ∀ len : Nat, args = [.scalar { bits := len, sizeBytes := 8 }] →
    len < 10 ∨ ret = Value.unit

def existsLenVacuousClaim : Claim := {
  body := sliceIsEmptySidecar
  pre := existsLenPre
  post := existsLenVacuousPost
}

theorem existsLenVacuousPost_not_dichotomy :
    ¬ PostconditionDichotomy existsLenPre existsLenVacuousPost :=
  not_postconditionDichotomy_of_forwardOutputInsensitive
    (fun _ hPre _ _ _ => by
      obtain ⟨n, hLt, hArgs⟩ := hPre
      intro len hLen
      have hEqArgs : [Value.scalar { bits := n, sizeBytes := 8 }] =
          [Value.scalar { bits := len, sizeBytes := 8 }] :=
        hArgs.symm.trans hLen
      have hN : n = len := (scalar_bits_inj (list_singleton_inj hEqArgs)).1
      subst hN
      exact Or.inl hLt)

-- Boilerplate atoms behind helper wrappers that re-match on `ans` are still cofactored.
#eval assertDeclEnsuresVacuous ``nestedMatchBoilerplateContract (some .unboundReturnOutput)
-- A genuine constraint behind a nested `match ans` must pass in both modes.
#eval assertDeclEnsuresBindsOutput ``nestedMatchGenuineContract
#eval assertDeclEnsuresBindsOutput ``nestedMatchGenuineContract { strictReturnValue := true }
-- Parameterized contracts are analyzed at arbitrary parameter values.
#eval assertDeclEnsuresBindsOutput ``boundedEchoClaim
#eval assertDeclEnsuresVacuous ``boundedTrivialClaim (some .trivialPostcondition)
-- `requires`-relative vacuity is caught under an existential list-encoded `requires`.
#eval assertEnsuresVacuous
  (Lean.mkConst ``existsLenVacuousPost) (some (Lean.mkConst ``existsLenPre))
  (some .survivedAllMutants)
#eval assertDeclEnsuresVacuous ``existsLenVacuousClaim (some .survivedAllMutants)

/-! ### 3.13 `dite`/Compound-`ite` Boilerplate, Disjunctive `requires` & Unrealizability Precedence -/

open scoped Classical in
/-- Boilerplate atoms inside both branches of a dependent `if h : ...` must be
    cofactored rather than escaping behind the branch lambdas. -/
def diteBoilerplateContract : MirCallContract := {
  pre := fun _ => True
  post := fun req ans =>
    match ans with
    | .returned retVal memAfter =>
      if _h : req.args = [] then
        callFramePreserved req.memory memAfter
      else
        callFramePreserved req.memory memAfter ∧
          retMatchesCalleeReturnTy sliceIsEmptySidecar retVal
    | .panicked _ => False
    | .aborted => True
}

open scoped Classical in
theorem diteBoilerplate_not_dichotomyModuloBoilerplate :
    ¬ DichotomyModuloObservation
        (externalSpecBoilerplateObs sliceIsEmptySidecar)
        diteBoilerplateContract.pre
        (fun req q => diteBoilerplateContract.post req (.returned q.1 q.2)) := by
  apply not_dichotomyModuloObservation_of_fibre_forwardInsensitive
  intro req q₁ q₂ _ hObsEq hOk
  have hFrameEq : callFramePreserved req.memory q₁.2 = callFramePreserved req.memory q₂.2 :=
    congrArg Prod.fst hObsEq
  have hTyEq : retMatchesCalleeReturnTy sliceIsEmptySidecar q₁.1 =
      retMatchesCalleeReturnTy sliceIsEmptySidecar q₂.1 :=
    congrArg Prod.snd hObsEq
  dsimp [diteBoilerplateContract] at hOk ⊢
  split at hOk <;> split
  · exact hFrameEq ▸ hOk
  · contradiction
  · contradiction
  · exact ⟨hFrameEq ▸ hOk.1, hTyEq ▸ hOk.2⟩

open scoped Classical in
/-- Genuine return constraint inside a dependent `if h : ...` branch must pass. -/
def diteGenuineContract : MirCallContract := {
  pre := fun _ => True
  post := fun req ans =>
    match ans with
    | .returned retVal memAfter =>
      if _h : req.args = [] then
        callFramePreserved req.memory memAfter ∧ retVal = Value.unit
      else
        callFramePreserved req.memory memAfter
    | .panicked _ => False
    | .aborted => True
}

open scoped Classical in
theorem diteGenuine_returnValueDichotomy :
    MirCallContractReturnValueDichotomy diteGenuineContract := by
  let req : MirCallReq := { defPath := "", args := .nil, memory := emptyMemory }
  refine ⟨req, emptyMemory, Value.unit, .scalar { bits := 7, sizeBytes := 4 },
    trivial, ?_, ?_⟩
  · dsimp [diteGenuineContract, req]
    exact ⟨callFramePreserved_refl emptyMemory, rfl⟩
  · intro hBad
    dsimp [diteGenuineContract, req] at hBad
    nomatch hBad.2

/-- Helper wrapping a boilerplate atom used inside an `ite` condition. -/
def hiddenFrameCond (req : MirCallReq) (memAfter : Memory) : Prop :=
  callFramePreserved req.memory memAfter

open scoped Classical in
def hiddenCondBoilerplateContract : MirCallContract := {
  pre := fun _ => True
  post := fun req ans =>
    match ans with
    | .returned _ memAfter =>
      if hiddenFrameCond req memAfter then True else False
    | .panicked _ => False
    | .aborted => True
}

open scoped Classical in
/-- Compound `ite` condition mixing a boilerplate atom and an input predicate. -/
def compoundIteCondBoilerplateContract : MirCallContract := {
  pre := fun _ => True
  post := fun req ans =>
    match ans with
    | .returned _ memAfter =>
      if callFramePreserved req.memory memAfter ∧ req.args = [] then True else False
    | .panicked _ => False
    | .aborted => True
}

/-- `let`-bound boilerplate atom must still be collected and cofactored. -/
def letBoilerplateContract : MirCallContract := {
  pre := fun _ => True
  post := fun req ans =>
    match ans with
    | .returned retVal memAfter =>
      let ok := callFramePreserved req.memory memAfter
      ok ∧ retMatchesCalleeReturnTy sliceIsEmptySidecar retVal
    | .panicked _ => False
    | .aborted => True
}

/-- Disjunctive precondition where branch 1 is vacuous and branch 2 genuinely binds `ret`:
    `PostconditionDichotomy` holds existentially, so the checker must NOT false-flag it. -/
def disjPartialVacuousPre (x : Nat) : Prop := x < 10 ∨ x ≥ 100
def disjPartialVacuousPost (x ret : Nat) : Prop := x < 10 ∨ ret = x

theorem disjPartialVacuous_dichotomy :
    PostconditionDichotomy disjPartialVacuousPre disjPartialVacuousPost := by
  change PostconditionDichotomy (fun x : Nat => x < 10 ∨ x ≥ 100) disjPartialVacuousPost
  apply Iff.mpr (postconditionDichotomy_or_pre_iff
    (pre₁ := fun x : Nat => x < 10) (pre₂ := fun x : Nat => x ≥ 100))
  refine Or.inr ⟨100, by omega, ⟨100, Or.inr rfl⟩, ⟨0, ?_⟩⟩
  intro hBad
  dsimp [disjPartialVacuousPost] at hBad
  rcases hBad with hLt | hEq <;> omega

/-- Disjunctive existential precondition: branch 1 is unsatisfiable and branch 2 forces
    `len < 10`, so `existsLenVacuousPost` is vacuous on every satisfiable branch. -/
def disjExistsVacuousPre (args : List Value) : Prop :=
  (∃ len : Nat, len > 10 ∧ len < 5 ∧ args = [.scalar { bits := len, sizeBytes := 8 }]) ∨
  (∃ len : Nat, len < 10 ∧ args = [.scalar { bits := len, sizeBytes := 8 }])

theorem disjExistsVacuous_not_dichotomy :
    ¬ PostconditionDichotomy disjExistsVacuousPre existsLenVacuousPost := by
  change ¬ PostconditionDichotomy
    (fun args =>
      (∃ len : Nat, len > 10 ∧ len < 5 ∧ args = [.scalar { bits := len, sizeBytes := 8 }]) ∨
      existsLenPre args)
    existsLenVacuousPost
  apply Iff.mpr (not_postconditionDichotomy_or_pre_iff
    (pre₁ := fun args =>
      ∃ len : Nat, len > 10 ∧ len < 5 ∧ args = [.scalar { bits := len, sizeBytes := 8 }])
    (pre₂ := existsLenPre))
  refine ⟨not_postconditionDichotomy_of_unsat_pre ?_, existsLenVacuousPost_not_dichotomy⟩
  rintro ⟨_, len, hGt, hLt, _⟩
  omega

/-- Disjunctive existential precondition where both branches are unsatisfiable. -/
def disjBothDeadPre (args : List Value) : Prop :=
  (∃ len : Nat, len > 10 ∧ len < 5 ∧ args = [.scalar { bits := len, sizeBytes := 8 }]) ∨
  (∃ len : Nat, len > 20 ∧ len < 15 ∧ args = [.scalar { bits := len, sizeBytes := 8 }])

theorem disjBothDeadPre_not_satisfiable :
    ¬ PreconditionSatisfiable disjBothDeadPre := by
  rintro ⟨_, hPre⟩
  rcases hPre with ⟨len, hGt, hLt, _⟩ | ⟨len, hGt, hLt, _⟩ <;> omega

/-- Discarded output binding with an arithmetically unsatisfiable residual (`SpecViolation`). -/
def discardedLetArithContraPost (x ret : Nat) : Prop :=
  let _ := ret
  x < x

/-- Unrealizable boilerplate-guarded contract mentioning `retVal` reflexively (`SpecViolation`). -/
def contraReflBoilerplateContract : MirCallContract := {
  pre := fun req => req.args = []
  post := fun req ans =>
    match ans with
    | .returned retVal memAfter =>
      callFramePreserved req.memory memAfter ∧ (retVal = retVal ∧ req.args ≠ [])
    | .panicked _ => False
    | .aborted => True
}

theorem contraReflBoilerplate_not_realizable :
    ¬ MirCallContractRealizable contraReflBoilerplateContract := by
  rintro ⟨req, _, _, hPre, _, _, hNe⟩
  exact hNe hPre

/-- Unrealizable under `survivedPre` (`x < 10`) while mentioning `ret` reflexively (`SpecViolation`). -/
def contraReflUnderReqPost (x ret : Nat) : Prop :=
  ret = ret ∧ x ≥ 10

theorem contraReflUnderReq_not_realizable :
    ¬ ContractRealizable survivedPre contraReflUnderReqPost := by
  rintro ⟨x, hLt, _, _, hGe⟩
  dsimp [survivedPre] at hLt
  omega

#eval assertDeclEnsuresVacuous ``diteBoilerplateContract (some .unboundReturnOutput)
#eval assertDeclEnsuresBindsOutput ``diteGenuineContract
#eval assertDeclEnsuresBindsOutput ``diteGenuineContract { strictReturnValue := true }
#eval assertDeclEnsuresVacuous ``hiddenCondBoilerplateContract (some .unboundReturnOutput)
#eval assertDeclEnsuresVacuous ``compoundIteCondBoilerplateContract (some .unboundReturnOutput)
#eval assertDeclEnsuresVacuous ``letBoilerplateContract (some .unboundReturnOutput)
-- Disjunctive `requires`: genuine branch passes; all-branches vacuous/dead are caught.
#eval assertEnsuresBindsOutput
  (Lean.mkConst ``disjPartialVacuousPost) (some (Lean.mkConst ``disjPartialVacuousPre))
#eval assertEnsuresVacuous
  (Lean.mkConst ``existsLenVacuousPost) (some (Lean.mkConst ``disjExistsVacuousPre))
  (some .survivedAllMutants)
#eval assertEnsuresVacuous
  (Lean.mkConst ``existsLenVacuousPost) (some (Lean.mkConst ``disjBothDeadPre))
  (some .deadPrecondition)
-- Unrealizability (`SpecViolation`) takes precedence over `UnboundReturnOutput` across Phases 2/3/4.
#eval assertEnsuresVacuous
  (Lean.mkConst ``discardedLetArithContraPost) none (some .specViolation)
#eval assertDeclEnsuresVacuous ``contraReflBoilerplateContract (some .specViolation)
#eval assertEnsuresVacuous
  (Lean.mkConst ``contraReflUnderReqPost) (some (Lean.mkConst ``survivedPre))
  (some .specViolation)

/-! ### 3.14 Closed Arithmetic Constants, `Trusted.Sequence.length` & Costly Type Indices -/

/-- Vacuously true: the guard is a closed falsehood. `scalarModulus 4` is an opaque atom
    to `omega`/`simp`, so the checker must evaluate it to a numeral before proving. -/
def closedModulusDeadGuardPost (x ret : Nat) : Prop :=
  scalarModulus 4 ≤ 0 → ret = x

theorem closedModulusDeadGuardPost_not_dichotomy :
    ¬ PostconditionDichotomy (fun _ : Nat => True) closedModulusDeadGuardPost :=
  not_postconditionDichotomy_of_trivial (fun x ret _ => by
    show scalarModulus 4 ≤ 0 → ret = x
    intro hLe
    exact absurd hLe (by decide))

/-- True of every `ret`: reduction modulo a closed positive modulus. -/
def closedModulusRangePost (_x ret : Nat) : Prop :=
  ret % scalarModulus 4 < scalarModulus 4

theorem closedModulusRangePost_not_dichotomy :
    ¬ PostconditionDichotomy (fun _ : Nat => True) closedModulusRangePost :=
  not_postconditionDichotomy_of_trivial (fun _ ret _ => by
    show ret % scalarModulus 4 < scalarModulus 4
    exact Nat.mod_lt ret (by decide))

/-- Genuine range constraint against the same closed modulus: must still pass. -/
def closedModulusBoundPost (_x ret : Nat) : Prop :=
  ret < scalarModulus 4

theorem closedModulusBoundPost_dichotomy :
    PostconditionDichotomy (fun _ : Nat => True) closedModulusBoundPost := by
  refine ⟨0, trivial, ⟨0, ?_⟩, ⟨scalarModulus 4, ?_⟩⟩
  · show (0 : Nat) < scalarModulus 4
    decide
  · show ¬ (scalarModulus 4 < scalarModulus 4)
    exact Nat.lt_irrefl _

/-- Argument-count conjunct written with `Trusted.Sequence.length`, exactly as in an
    external-spec `requires`: `args = []` contradicts the closed arity `1`, so no
    output satisfies the postcondition even though it mentions `ret`. -/
def seqLengthContraPost (args : List Value) (ret : Value) : Prop :=
  ret = ret ∧ args = [] ∧
    Trusted.Sequence.length args = sliceIsEmptySidecar.argCount

theorem seqLengthContraPost_not_realizable :
    ¬ ContractRealizable (fun _ : List Value => True) seqLengthContraPost := by
  rintro ⟨_, _, _, _, rfl, hLen⟩
  exact absurd hLen (by decide)

/-- Closed type index whose evaluation needs thousands of nested unfolding steps, far
    beyond the elaborator's recursion-depth limit. -/
def deepIndex : Nat → Nat
  | 0 => 1
  | n + 1 => deepIndex n + 1

theorem deepIndex_gt (n : Nat) : n < deepIndex n := by
  induction n with
  | zero => exact Nat.zero_lt_one
  | succ k ih =>
    show k + 1 < deepIndex k + 1
    exact Nat.succ_lt_succ ih

/-- `Fin (deepIndex 5000)` has 5001 inhabitants, but deciding whether it is `Fin 0` or
    `Fin 1` means evaluating the index, which exhausts the recursion depth. -/
def deepIndexFinPost (_x : Nat) (ret : Fin (deepIndex 5000)) : Prop :=
  ret.val = 0

theorem deepIndexFinPost_dichotomy :
    PostconditionDichotomy (fun _ : Nat => True) deepIndexFinPost :=
  ⟨0, trivial,
    ⟨⟨0, Nat.lt_of_le_of_lt (Nat.zero_le 5000) (deepIndex_gt 5000)⟩, rfl⟩,
    ⟨⟨1, Nat.lt_of_le_of_lt (by decide : (1 : Nat) ≤ 5000) (deepIndex_gt 5000)⟩,
      fun h => Nat.succ_ne_zero 0 h⟩⟩

-- Closed constants are evaluated before proving: a dead closed guard and a range fact
-- that holds for every output are both tautologies, while a genuine bound still passes.
#eval assertEnsuresVacuous
  (Lean.mkConst ``closedModulusDeadGuardPost) none (some .trivialPostcondition)
#eval assertEnsuresVacuous
  (Lean.mkConst ``closedModulusRangePost) none (some .trivialPostcondition)
#eval assertEnsuresBindsOutput (Lean.mkConst ``closedModulusBoundPost)
-- `Trusted.Sequence.length` and a closed sidecar arity reduce to `List.length args = 1`,
-- so unrealizability (`SpecViolation`) is proved instead of mere output-insensitivity.
#eval assertEnsuresVacuous
  (Lean.mkConst ``seqLengthContraPost) none (some .specViolation)
-- Inspecting a costly output-type index is contained: the check returns a verdict
-- (the output is genuinely bound) instead of escaping with a runtime exception.
#eval assertEnsuresBindsOutput (Lean.mkConst ``deepIndexFinPost)

/-! ### 3.15 Closed-Nat Isolation, Budget Starvation Notes & Boilerplate Restatement -/

/-- Combines a recursion-deep closed type index (`Fin (deepIndex 5000)`) with a cheap
    closed dead guard (`scalarModulus 4 ≤ 0`): per-subterm isolation must skip
    `deepIndex 5000` without preventing `scalarModulus 4` from folding. -/
def deepIndexWithClosedModulusPost (_x : Nat) (ret : Fin (deepIndex 5000)) : Prop :=
  scalarModulus 4 ≤ 0 → ret.val = 0

theorem deepIndexWithClosedModulusPost_not_dichotomy :
    ¬ PostconditionDichotomy (fun _ : Nat => True) deepIndexWithClosedModulusPost :=
  not_postconditionDichotomy_of_trivial (fun _ ret _ => by
    show scalarModulus 4 ≤ 0 → ret.val = 0
    intro hLe
    exact absurd hLe (by decide))

private theorem scalarModulus_pos (k : Nat) : 0 < scalarModulus k := by
  induction k with
  | zero => exact Nat.zero_lt_one
  | succ n ih =>
    show 0 < Nat.mul 256 (scalarModulus n)
    exact Nat.mul_pos (by decide) ih

/-- Polymorphic-exponent dichotomy helper: keeping `e` abstract avoids kernel
    reduction of large literal exponents (`2 ^ 1000000`) during elaboration. -/
private theorem lt_pow_and_modulus_dichotomy (e k : Nat) :
    PostconditionDichotomy (fun _ : Nat => True)
      (fun _ ret : Nat => ret < 2 ^ e ∧ ret < scalarModulus k) := by
  refine ⟨0, trivial, ⟨0, Nat.pow_pos Nat.zero_lt_two, scalarModulus_pos k⟩, ⟨2 ^ e, ?_⟩⟩
  rintro ⟨hLt, _⟩
  exact Nat.lt_irrefl (2 ^ e) hLt

/-- Genuine postcondition mentioning an oversized closed power (`2 ^ 1000000`) and
    large `scalarModulus 1000`: both must stay symbolic without bignum stalls. -/
def oversizedExpPost (_x ret : Nat) : Prop :=
  ret < 2 ^ 1000000 ∧ ret < scalarModulus 1000

theorem oversizedExpPost_dichotomy :
    PostconditionDichotomy (fun _ : Nat => True) oversizedExpPost :=
  lt_pow_and_modulus_dichotomy 1000000 1000

/-- Precondition over a recursion-deep type index: `checkRequiresSatisfiable` must
    contain typeclass and witness timeouts instead of throwing a runtime exception. -/
def deepIndexReq (_x : Fin (deepIndex 5000)) : Prop := True

/-- Conjunctive boilerplate restatement: `memAfter.activeProtectors = req.memory.activeProtectors`
    is already implied by `callFramePreserved req.memory memAfter`, so it constrains
    nothing beyond the frame boilerplate (`UnboundReturnOutput`). -/
def restateProtectorsAndContract : MirCallContract := {
  pre := fun _ => True
  post := fun req ans =>
    match ans with
    | .returned _ memAfter =>
      callFramePreserved req.memory memAfter ∧
        memAfter.activeProtectors = req.memory.activeProtectors
    | .panicked _ => False
    | .aborted => True
}

theorem restateProtectorsAnd_not_dichotomyModuloFrame :
    ¬ DichotomyModuloObservation
        (fun req (q : Value × Memory) => callFramePreserved req.memory q.2)
        restateProtectorsAndContract.pre
        (fun req q => restateProtectorsAndContract.post req (.returned q.1 q.2)) := by
  apply not_dichotomyModuloObservation_of_fibre_forwardInsensitive
  intro req q₁ q₂ _ hObsEq hOk
  dsimp [restateProtectorsAndContract] at hOk ⊢
  have hFrame₂ : callFramePreserved req.memory q₂.2 := hObsEq ▸ hOk.1
  rcases hFrame₂ with ⟨hC, hS, hA, hP, hF⟩
  exact ⟨⟨hC, hS, hA, hP, hF⟩, hP⟩

/-- Implicational boilerplate restatement: holds for every `(req, retVal, memAfter)`
    because `callFramePreserved` already implies `activeProtectors` equality, so the
    normal-return postcondition is universally valid (`TrivialPostcondition`). -/
def restateProtectorsImpliesContract : MirCallContract := {
  pre := fun _ => True
  post := fun req ans =>
    match ans with
    | .returned _ memAfter =>
      callFramePreserved req.memory memAfter →
        memAfter.activeProtectors = req.memory.activeProtectors
    | .panicked _ => False
    | .aborted => True
}

theorem restateProtectorsImplies_not_normalDichotomy :
    ¬ MirCallContractNormalDichotomy restateProtectorsImpliesContract := by
  rintro ⟨_, _, _, _, _, _, _, hBad⟩
  apply hBad
  intro hFrame
  rcases hFrame with ⟨_, _, _, hP, _⟩
  exact hP

/-- 3-argument `externalSpecCallContract`-shaped contract whose precondition carries
    all parameter-validity conjuncts, `rangeClampPre`, and `req.memory.activeProtectors = []`.
    Inside the frame-preserving fibre, transitivity of equality forces
    `memAfter.activeProtectors = []`, so the `retVal` disjunct is vacuous under `pre`
    (`SurvivedAllMutants`). Unpacking all precondition and boilerplate conjuncts requires
    more than 32 hypothesis-destruction steps. -/
def multiArgConjProtectorsContract : MirCallContract := {
  pre := fun req =>
    (externalSpecCallContract "core::cmp::Ord::clamp" rangeClampSidecar
      rangeClampPre (fun _ _ => True)).pre req ∧
    req.memory.activeProtectors = []
  post := fun req ans =>
    match ans with
    | .returned retVal memAfter =>
      callFramePreserved req.memory memAfter ∧
        retMatchesCalleeReturnTy rangeClampSidecar retVal ∧
        (memAfter.activeProtectors = [] ∨ retVal = .scalar { bits := 0, sizeBytes := 4 })
    | .panicked _ => False
    | .aborted => True
}

theorem multiArgConjProtectors_not_dichotomyModuloBoilerplate :
    ¬ DichotomyModuloObservation
        (externalSpecBoilerplateObs rangeClampSidecar)
        multiArgConjProtectorsContract.pre
        (fun req q => multiArgConjProtectorsContract.post req (.returned q.1 q.2)) := by
  apply not_dichotomyModuloObservation_of_fibre_forwardInsensitive
  intro req q₁ q₂ hPre hObsEq hOk
  have hFrameEq : callFramePreserved req.memory q₁.2 = callFramePreserved req.memory q₂.2 :=
    congrArg Prod.fst hObsEq
  have hTyEq : retMatchesCalleeReturnTy rangeClampSidecar q₁.1 =
      retMatchesCalleeReturnTy rangeClampSidecar q₂.1 :=
    congrArg Prod.snd hObsEq
  dsimp [multiArgConjProtectorsContract] at hPre hOk ⊢
  have hFrame₂ : callFramePreserved req.memory q₂.2 := hFrameEq ▸ hOk.1
  have hTy₂ : retMatchesCalleeReturnTy rangeClampSidecar q₂.1 := hTyEq ▸ hOk.2.1
  rcases hFrame₂ with ⟨hC, hS, hA, hP, hF⟩
  exact ⟨⟨hC, hS, hA, hP, hF⟩, hTy₂, Or.inl (hP.trans hPre.2)⟩

-- Per-subterm isolation folds `scalarModulus 4` even beside `Fin (deepIndex 5000)`.
#eval assertEnsuresVacuous
  (Lean.mkConst ``deepIndexWithClosedModulusPost) none (some .trivialPostcondition)
-- Oversized exponents and moduli stay symbolic without stalling bignum evaluation.
#eval assertEnsuresBindsOutput (Lean.mkConst ``oversizedExpPost)
-- Boilerplate restatements and deep multi-arg conjunctive equation propagation.
#eval assertDeclEnsuresVacuous ``restateProtectorsAndContract (some .unboundReturnOutput)
#eval assertDeclEnsuresVacuous ``restateProtectorsImpliesContract (some .trivialPostcondition)
#eval assertDeclEnsuresVacuous ``multiArgConjProtectorsContract (some .survivedAllMutants)

#eval show Lean.Meta.MetaM Unit from do
  -- `checkRequiresSatisfiable` contains costly type indices without throwing.
  let reqRes ← checkRequiresSatisfiable (Lean.mkConst ``deepIndexReq)
  if reqRes.satisfiable? == some false then
    throwError "expected deepIndexReq not falsely refuted, got {repr reqRes}"
  -- Phase 1 cutoff on `deepIndexFinPost` records an informative conservative-degradation note.
  let deepRes ← checkEnsuresBindsOutput (Lean.mkConst ``deepIndexFinPost)
  unless deepRes.bindsOutput && !deepRes.notes.isEmpty do
    throwError "expected deepIndexFinPost to accept with cutoff note, got {repr deepRes}"
  -- Starved probes on a hard genuine postcondition degrade conservatively with notes.
  let starvedRes ← checkEnsuresBindsOutput (Lean.mkConst ``budgetProbePost) none
    { stepHeartbeats := 1, totalHeartbeats := 250000 }
  unless starvedRes.bindsOutput && !starvedRes.notes.isEmpty do
    throwError "expected starved budgetProbePost to accept with degradation note, got {repr starvedRes}"
  -- Starved multi-fibre `MirCallAns` check degrades conservatively with notes.
  let starvedCall ← checkDeclEnsuresBindsOutput ``frameImpliesRetContract
    { stepHeartbeats := 1, totalHeartbeats := 1 }
  unless starvedCall.bindsOutput && !starvedCall.notes.isEmpty do
    throwError "expected starved MirCallAns check to accept with degradation note, got {repr starvedCall}"

/-! ### 3.16 A Failed Probe Is Not a Cutoff: Degradation Notes Only on Real Cutoffs -/

/-- Genuine linear postcondition. Every vacuity probe against it fails fast: the
    tactics give up with an ordinary error long before any heartbeat or recursion cap. -/
def succExactPost (x ret : Nat) : Prop := ret = x + 1

theorem succExactPost_dichotomy :
    PostconditionDichotomy (fun _ : Nat => True) succExactPost := by
  refine ⟨0, trivial, ⟨1, ?_⟩, ⟨0, ?_⟩⟩
  · show (1 : Nat) = 0 + 1
    rfl
  · intro h
    have h' : (0 : Nat) = 0 + 1 := h
    omega

#eval show Lean.Meta.MetaM Unit from do
  -- An ordinary exception (what a tactic that cannot close its goal throws) is a
  -- failure, not a cutoff; only heartbeat or recursion exhaustion is a cutoff.
  let errOutcome ← withBoundedHeartbeatsOutcome 1000000
    (throwError "ordinary probe failure" : Lean.Meta.MetaM Nat)
  match errOutcome with
  | .failed => pure ()
  | _ => throwError "expected .failed constructor for ordinary exception"
  unless errOutcome.isFailed && !errOutcome.isCutOff && errOutcome.toOption.isNone do
    throwError "expected an ordinary exception to be classified as failed, not cut off"
  let doneOutcome ← withBoundedHeartbeatsOutcome 1000000 (pure 7 : Lean.Meta.MetaM Nat)
  match doneOutcome with
  | .done 7 => pure ()
  | _ => throwError "expected .done 7 constructor for normal return"
  unless doneOutcome.toOption == some 7 && !doneOutcome.isFailed && !doneOutcome.isCutOff do
    throwError "expected a normal return to be classified as done"
  let cutOffOutcome ← withBoundedHeartbeatsOutcome 1000 do
    let mut acc := Lean.mkNatLit 0
    for i in [0:20000] do
      acc ← Lean.Meta.whnf (Lean.mkNatAdd acc (Lean.mkNatLit i))
      Lean.Core.checkSystem "SpecRealizabilityTests cutoff classification probe"
    return acc
  match cutOffOutcome with
  | .cutOff => pure ()
  | _ => throwError "expected .cutOff constructor for heartbeat exhaustion"
  unless cutOffOutcome.isCutOff && !cutOffOutcome.isFailed && cutOffOutcome.toOption.isNone do
    throwError "expected heartbeat exhaustion to be classified as cut off"
  -- A genuine postcondition under the default budget is accepted with no note at
  -- all: its probes are refuted by failing tactics, and a failed tactic must not be
  -- reported as a probe that "exceeded its heartbeat/recursion cap".
  let cleanRes ← checkEnsuresBindsOutput (Lean.mkConst ``succExactPost)
  unless cleanRes.bindsOutput && cleanRes.notes.isEmpty do
    throwError "expected succExactPost accepted without degradation notes, got {repr cleanRes}"
  -- The same postcondition under a one-unit per-snippet cap really is cut off, and
  -- only then carries a degradation note.
  let starvedClean ← checkEnsuresBindsOutput (Lean.mkConst ``succExactPost) none
    { stepHeartbeats := 1, totalHeartbeats := 250000 }
  unless starvedClean.bindsOutput && !starvedClean.notes.isEmpty do
    throwError "expected starved succExactPost accepted with a degradation note, got {repr starvedClean}"

/-! ### 3.17 `TotalClaim` and `ModularClaim` Declarations -/

/-- Total-correctness counterpart of `statefulCounterStepClaim`. -/
def totalCounterStepClaim : TotalClaim := {
  body := statefulCounterStepBody
  pre := statefulCounterStepPre
  post := statefulCounterStepPost
}

/-- Rely-guarantee counterpart of `statefulCounterStepClaim`. -/
def modularCounterStepClaim : ModularClaim := {
  body := statefulCounterStepBody
  envAssumed := fun _ => True
  pre := statefulCounterStepPre
  post := statefulCounterStepPost
}

/-- Total-correctness claim that pins `mem'` and never mentions the return value. -/
def memOnlyTotalClaim : TotalClaim := {
  body := statefulCounterStepBody
  pre := fun _ _ => True
  post := fun _ mem _ mem' => mem' = mem
}

/-- Rely-guarantee claim that pins `mem'` and never mentions the return value. -/
def memOnlyModularClaim : ModularClaim := {
  body := statefulCounterStepBody
  envAssumed := fun _ => True
  pre := fun _ _ => True
  post := fun _ mem _ mem' => mem' = mem
}

theorem totalCounterStep_returnDichotomy :
    TotalClaimReturnDichotomy totalCounterStepClaim := by
  refine ⟨[], emptyMemory, { emptyMemory with nextTag := emptyMemory.nextTag + 1 },
    .scalar { bits := emptyMemory.nextTag, sizeBytes := 4 },
    .scalar { bits := 0, sizeBytes := 4 },
    ⟨rfl, by decide⟩, ⟨rfl, rfl⟩, ?_⟩
  rintro ⟨hRet, _⟩
  have hBits : (0 : Nat) = emptyMemory.nextTag := (scalar_bits_inj hRet).1
  dsimp [emptyMemory] at hBits
  omega

theorem modularCounterStep_returnDichotomy :
    ModularClaimReturnDichotomy modularCounterStepClaim := by
  refine ⟨[], emptyMemory, { emptyMemory with nextTag := emptyMemory.nextTag + 1 },
    .scalar { bits := emptyMemory.nextTag, sizeBytes := 4 },
    .scalar { bits := 0, sizeBytes := 4 },
    ⟨rfl, by decide⟩, ⟨rfl, rfl⟩, ?_⟩
  rintro ⟨hRet, _⟩
  have hBits : (0 : Nat) = emptyMemory.nextTag := (scalar_bits_inj hRet).1
  dsimp [emptyMemory] at hBits
  omega

theorem memOnlyTotal_not_returnDichotomy :
    ¬ TotalClaimReturnDichotomy memOnlyTotalClaim := by
  rintro ⟨_, _, _, _, _, _, hOk, hBad⟩
  exact hBad hOk

theorem memOnlyModular_not_returnDichotomy :
    ¬ ModularClaimReturnDichotomy memOnlyModularClaim := by
  rintro ⟨_, _, _, _, _, _, hOk, hBad⟩
  exact hBad hOk

-- `checkDeclEnsuresBindsOutput` reads `pre` / `post` off all four claim structures:
-- the genuine counter step passes and the return-ignoring claim is flagged, exactly
-- as for the `StatefulClaim` versions of the same contracts.
#eval assertDeclEnsuresBindsOutput ``totalCounterStepClaim
#eval assertDeclEnsuresBindsOutput ``totalCounterStepClaim { strictReturnValue := true }
#eval assertDeclEnsuresBindsOutput ``modularCounterStepClaim
#eval assertDeclEnsuresBindsOutput ``modularCounterStepClaim { strictReturnValue := true }
#eval assertDeclEnsuresVacuous ``memOnlyTotalClaim (some .unboundReturnOutput)
  { strictReturnValue := true }
#eval assertDeclEnsuresVacuous ``memOnlyModularClaim (some .unboundReturnOutput)
  { strictReturnValue := true }
-- Without `strictReturnValue` the pair `(retVal, mem')` is the output, and `mem' = mem`
-- does constrain it.
#eval assertDeclEnsuresBindsOutput ``memOnlyTotalClaim
#eval assertDeclEnsuresBindsOutput ``memOnlyModularClaim

/-! ### 3.18 Cross-Language `VacuityClass` Wire Names -/

-- The five canonical names are pinned literally. The Rust dynamic checker's
-- `VacuityClass::canonical_name` returns exactly these strings, and its test suite
-- pins the same five literals, so neither side can drift without a test failing.
example : VacuityClass.deadPrecondition.canonicalName = "DeadPrecondition" := rfl
example : VacuityClass.specViolation.canonicalName = "SpecViolation" := rfl
example : VacuityClass.trivialPostcondition.canonicalName = "TrivialPostcondition" := rfl
example : VacuityClass.unboundReturnOutput.canonicalName = "UnboundReturnOutput" := rfl
example : VacuityClass.survivedAllMutants.canonicalName = "SurvivedAllMutants" := rfl

/-! ### 3.19 Starved-Budget Syntactic Fibres & Final Negative Controls -/

/-- Polymorphic-exponent dichotomy helper for a single upper-bound postcondition. -/
private theorem lt_pow_dichotomy (e : Nat) :
    PostconditionDichotomy (fun _ : Nat => True) (fun _ ret : Nat => ret < 2 ^ e) := by
  refine ⟨0, trivial, ⟨0, Nat.pow_pos Nat.zero_lt_two⟩, ⟨2 ^ e, ?_⟩⟩
  intro hLt
  exact Nat.lt_irrefl (2 ^ e) hLt

/-- Genuine postcondition with a closed power between Lean's exponentiation warning
    threshold (`256`) and `closedNatFoldBound` (`512`): `normalizeGoalArith` must
    isolate `Core.State.messages` so folding `2 ^ 300` never leaks a warning. -/
def midExpPost (_x ret : Nat) : Prop :=
  ret < 2 ^ 300

theorem midExpPost_dichotomy :
    PostconditionDichotomy (fun _ : Nat => True) midExpPost :=
  lt_pow_dichotomy 300

/-- Multi-branch native `Option Nat` postcondition: `some (a - b)` when `b ≤ a`,
    `none` when `a < b`. -/
def checkedSubOptionPost (a b : Nat) (ret : Option Nat) : Prop :=
  match ret with
  | some v => b ≤ a ∧ v + b = a
  | none => a < b

theorem checkedSubOptionPost_dichotomy :
    PostconditionDichotomy (fun _ : Nat × Nat => True)
      (fun p ret => checkedSubOptionPost p.1 p.2 ret) := by
  refine ⟨(5, 2), trivial, ⟨some 3, ⟨by decide, rfl⟩⟩, ⟨none, ?_⟩⟩
  intro hLt
  dsimp [checkedSubOptionPost] at hLt
  omega

/-- Multi-branch native `Except Nat Nat` (Lean `Result` analog) postcondition:
    `ok` carries an in-range quotient when `b ≠ 0`, `error` echoes `a` when `b = 0`. -/
def checkedDivExceptPost (a b : Nat) (ret : Except Nat Nat) : Prop :=
  match ret with
  | .ok q => b ≠ 0 ∧ q * b ≤ a
  | .error e => b = 0 ∧ e = a

theorem checkedDivExceptPost_dichotomy :
    PostconditionDichotomy (fun _ : Nat × Nat => True)
      (fun p ret => checkedDivExceptPost p.1 p.2 ret) := by
  refine ⟨(6, 2), trivial, ⟨.ok 3, ⟨by decide, by decide⟩⟩, ⟨.error 6, ?_⟩⟩
  intro hBad
  dsimp [checkedDivExceptPost] at hBad
  exact Nat.succ_ne_zero 1 hBad.1

/-- Inhabited multi-constructor binary tree inductive: negative control confirming
    inhabited recursive types are never false-flagged as empty or subsingleton. -/
inductive BinTree : Type where
  | leaf : Nat → BinTree
  | branch : BinTree → BinTree → BinTree

def binTreeLeafPost (x : Nat) (ret : BinTree) : Prop :=
  ret = .leaf x

theorem binTreeLeafPost_dichotomy :
    PostconditionDichotomy (fun _ : Nat => True) binTreeLeafPost := by
  refine ⟨0, trivial, ⟨.leaf 0, rfl⟩, ⟨.leaf 1, ?_⟩⟩
  intro hEq
  have hVal : (1 : Nat) = 0 := BinTree.leaf.inj hEq
  exact Nat.succ_ne_zero 0 hVal

-- Mid-range closed power (`2 ^ 300`), multi-branch `Option`/`Except`, and binary-tree
-- negative controls must all pass cleanly without false-flagging or leaking warnings.
#eval assertEnsuresBindsOutput (Lean.mkConst ``midExpPost)
#eval assertEnsuresBindsOutput (Lean.mkConst ``checkedSubOptionPost)
#eval assertEnsuresBindsOutput (Lean.mkConst ``checkedDivExceptPost)
#eval assertEnsuresBindsOutput (Lean.mkConst ``binTreeLeafPost)

-- Even once `ProbeBudget` is exhausted before or during Phase 3, pure boilerplate
-- cofactoring and syntactic fibre checks still catch syntactically vacuous
-- `MirCallContract`s while genuine external-spec contracts degrade conservatively.
#eval assertDeclEnsuresVacuous ``boilerplateOnlyExtContract (some .unboundReturnOutput)
  { stepHeartbeats := 1, totalHeartbeats := 1 }
#eval assertDeclEnsuresVacuous ``boilerplateIffContract (some .unboundReturnOutput)
  { stepHeartbeats := 1, totalHeartbeats := 1 }
#eval assertDeclEnsuresVacuous ``boilerplateExcludedMiddleContract (some .trivialPostcondition)
  { stepHeartbeats := 1, totalHeartbeats := 1 }
#eval assertDeclEnsuresVacuous ``trap1FalsePostContract (some .specViolation)
  { stepHeartbeats := 1, totalHeartbeats := 1 }
#eval assertDeclEnsuresVacuous ``tautInputOnlyBoilerplateContract (some .trivialPostcondition)
  { stepHeartbeats := 1, totalHeartbeats := 1 }
#eval show Lean.Meta.MetaM Unit from do
  let starvedExt ← checkDeclEnsuresBindsOutput ``sliceIsEmptyExtContract
    { stepHeartbeats := 1, totalHeartbeats := 1 }
  unless starvedExt.bindsOutput && !starvedExt.notes.isEmpty do
    throwError "expected starved sliceIsEmptyExtContract accepted with degradation note, got {repr starvedExt}"

/-! ### 3.20 Prover-Free Syntactic Layer: Contradictions, Hypotheses & Disguised Tautologies -/

-- Every fixture below is settled by `detectSyntacticTautology` /
-- `detectSyntacticContradiction` alone: the `#eval` checks run with a starved probe
-- budget, under which no tactic can prove anything.

/-- Ex falso from a contradictory hypothesis. -/
def exFalsoHypPost (x ret : Nat) : Prop := ret ≠ ret → x = 0

/-- Projection out of a conjunctive hypothesis. -/
def conjHypProjPost (x ret : Nat) : Prop := (ret = x ∧ x < 10) → ret = x

/-- Symmetric restatement of an equality hypothesis. -/
def symmHypPost (x ret : Nat) : Prop := x = ret → ret = x

/-- The law of non-contradiction. -/
def nonContradictionPost (x ret : Nat) : Prop := ¬ (ret = x ∧ ret ≠ x)

/-- Boolean-decidable reflexivity. -/
def decideReflPost (_x ret : Nat) : Prop := decide (ret = ret) = true

/-- Reflexivity under a dependent `∀`. -/
def forallReflPost (_x ret : Nat) : Prop := ∀ k : Nat, k + ret = k + ret

/-- Excluded middle split across a nested disjunction. -/
def nestedExcludedMiddlePost (x ret : Nat) : Prop := (ret = x ∨ x < 5) ∨ ret ≠ x

/-- Symmetric restatement as an equality of propositions. -/
def symmEqPropPost (x ret : Nat) : Prop := (ret = x) = (x = ret)

/-- A complementary pair of conjuncts: unrealizable. -/
def contraSynPost (x ret : Nat) : Prop := ret = x ∧ ret ≠ x

/-- A complementary pair of conjuncts in a `requires`: dead. -/
def deadSynPre (x : Nat) : Prop := x = 0 ∧ x ≠ 0

/-- Negative control: a hypothesis that does not entail the conclusion. -/
def hypGuardedGenuinePost (x ret : Nat) : Prop := x < 10 → ret = x

/-- Negative control: conjuncts that only look complementary. -/
def eqAndNeOtherPost (x ret : Nat) : Prop := ret = x ∧ ret ≠ x + 1

theorem exFalsoHypPost_not_dichotomy :
    ¬ PostconditionDichotomy (fun _ : Nat => True) exFalsoHypPost :=
  not_postconditionDichotomy_of_trivial (fun _ _ _ h => absurd rfl h)

theorem conjHypProjPost_not_dichotomy :
    ¬ PostconditionDichotomy (fun _ : Nat => True) conjHypProjPost :=
  not_postconditionDichotomy_of_trivial (fun _ _ _ h => h.1)

theorem symmHypPost_not_dichotomy :
    ¬ PostconditionDichotomy (fun _ : Nat => True) symmHypPost :=
  not_postconditionDichotomy_of_trivial (fun _ _ _ h => h.symm)

theorem nonContradictionPost_not_dichotomy :
    ¬ PostconditionDichotomy (fun _ : Nat => True) nonContradictionPost :=
  not_postconditionDichotomy_of_trivial (fun _ _ _ h => h.2 h.1)

theorem decideReflPost_not_dichotomy :
    ¬ PostconditionDichotomy (fun _ : Nat => True) decideReflPost :=
  not_postconditionDichotomy_of_trivial (fun _ ret _ => by
    show decide (ret = ret) = true
    exact decide_eq_true rfl)

theorem forallReflPost_not_dichotomy :
    ¬ PostconditionDichotomy (fun _ : Nat => True) forallReflPost :=
  not_postconditionDichotomy_of_trivial (fun _ _ _ _ => rfl)

theorem nestedExcludedMiddlePost_not_dichotomy :
    ¬ PostconditionDichotomy (fun _ : Nat => True) nestedExcludedMiddlePost :=
  not_postconditionDichotomy_of_trivial (fun x ret _ => by
    show (ret = x ∨ x < 5) ∨ ret ≠ x
    by_cases h : ret = x
    · exact Or.inl (Or.inl h)
    · exact Or.inr h)

theorem symmEqPropPost_not_dichotomy :
    ¬ PostconditionDichotomy (fun _ : Nat => True) symmEqPropPost :=
  not_postconditionDichotomy_of_trivial (fun x ret _ => by
    show (ret = x) = (x = ret)
    exact propext ⟨Eq.symm, Eq.symm⟩)

theorem contraSynPost_not_realizable :
    ¬ ContractRealizable (fun _ : Nat => True) contraSynPost := by
  rintro ⟨_, _, _, hEq, hNe⟩
  exact hNe hEq

theorem deadSynPre_not_satisfiable : ¬ PreconditionSatisfiable deadSynPre := by
  rintro ⟨_, hEq, hNe⟩
  exact hNe hEq

theorem hypGuardedGenuinePost_dichotomy :
    PostconditionDichotomy (fun _ : Nat => True) hypGuardedGenuinePost := by
  refine ⟨0, trivial, ⟨0, ?_⟩, ⟨1, ?_⟩⟩ <;> simp [hypGuardedGenuinePost]

theorem eqAndNeOtherPost_dichotomy :
    PostconditionDichotomy (fun _ : Nat => True) eqAndNeOtherPost := by
  refine ⟨0, trivial, ⟨0, ?_⟩, ⟨1, ?_⟩⟩ <;> simp [eqAndNeOtherPost]

#eval assertEnsuresVacuous (Lean.mkConst ``exFalsoHypPost) none (some .trivialPostcondition)
  { stepHeartbeats := 0, totalHeartbeats := 0 }
#eval assertEnsuresVacuous (Lean.mkConst ``conjHypProjPost) none (some .trivialPostcondition)
  { stepHeartbeats := 0, totalHeartbeats := 0 }
#eval assertEnsuresVacuous (Lean.mkConst ``symmHypPost) none (some .trivialPostcondition)
  { stepHeartbeats := 0, totalHeartbeats := 0 }
#eval assertEnsuresVacuous (Lean.mkConst ``nonContradictionPost) none
  (some .trivialPostcondition) { stepHeartbeats := 0, totalHeartbeats := 0 }
#eval assertEnsuresVacuous (Lean.mkConst ``decideReflPost) none (some .trivialPostcondition)
  { stepHeartbeats := 0, totalHeartbeats := 0 }
#eval assertEnsuresVacuous (Lean.mkConst ``forallReflPost) none (some .trivialPostcondition)
  { stepHeartbeats := 0, totalHeartbeats := 0 }
#eval assertEnsuresVacuous (Lean.mkConst ``nestedExcludedMiddlePost) none
  (some .trivialPostcondition) { stepHeartbeats := 0, totalHeartbeats := 0 }
#eval assertEnsuresVacuous (Lean.mkConst ``symmEqPropPost) none (some .trivialPostcondition)
  { stepHeartbeats := 0, totalHeartbeats := 0 }
-- A syntactically contradictory `ensures` is unrealizable, and a syntactically
-- contradictory `requires` is dead, with no prover involved.
#eval assertEnsuresVacuous (Lean.mkConst ``contraSynPost) none (some .specViolation)
  { stepHeartbeats := 0, totalHeartbeats := 0 }
#eval assertEnsuresVacuous
  (Lean.mkConst ``deadPost) (some (Lean.mkConst ``deadSynPre)) (some .deadPrecondition)
  { stepHeartbeats := 0, totalHeartbeats := 0 }
#eval show Lean.Meta.MetaM Unit from do
  let starved ← checkRequiresSatisfiable (Lean.mkConst ``deadSynPre)
    { stepHeartbeats := 0, totalHeartbeats := 0 }
  unless starved.satisfiable? == some false do
    throwError "expected deadSynPre refuted syntactically, got {repr starved}"
-- Negative controls: neither recognizer may fire on a genuine postcondition.
#eval assertEnsuresBindsOutput (Lean.mkConst ``hypGuardedGenuinePost)
#eval assertEnsuresBindsOutput (Lean.mkConst ``eqAndNeOtherPost)

/-! ### 3.21 Cross-Language 1:1 Vacuity Parity Suite (`CrossLanguageParitySuite`) -/

namespace CrossLanguageParitySuite

/-!
#### Cross-Language Vacuity Parity Benchmark Matrix

Each row is one contract, stated once here over `Nat` models of the Rust types and
once in `crates/anneal-spec/tests/spec_check_tests.rs` (module
`cross_language_parity_suite`) as a real `#[spec]` / `#[external_spec]` /
`#[embed_spec]` companion. Both files use the canonical benchmark ID verbatim as the
name of the row.

| Benchmark ID                       | Verdict in both languages |
|------------------------------------|---------------------------|
| `CL_POS_01_checked_add_u32`        | strong                    |
| `CL_POS_02_slice_bounds_and_empty` | strong                    |
| `CL_POS_03_saturating_clamp_u32`   | strong                    |
| `CL_POS_04_stateful_bounded_step`  | strong                    |
| `CL_VAC_01_dead_precondition`      | `DeadPrecondition`        |
| `CL_VAC_02_spec_violation`         | `SpecViolation`           |
| `CL_VAC_03_trivial_postcondition`  | `TrivialPostcondition`    |
| `CL_VAC_04_unbound_return_output`  | `UnboundReturnOutput`     |
| `CL_VAC_05_survived_all_mutants`   | `SurvivedAllMutants`      |

The contracts (`requires` ⟹ `ensures`):

* `CL_POS_01`: `u32::checked_add`, `Some(a + b)` iff `a + b ≤ u32::MAX`, else `None`.
* `CL_POS_02`: `idx ≤ len` ⟹ `ret = (len == 0, idx < len)` (emptiness and index bounds).
* `CL_POS_03`: `lo ≤ hi` ⟹ `ret = clamp(val, lo, hi)`.
* `CL_POS_04`: `val < limit` ⟹ `ret = val' = val + 1` and `limit' = limit` (`&mut` step).
* `CL_VAC_01`: `x > 100 ∧ x < 50` ⟹ `ret = x` (contradictory `requires`).
* `CL_VAC_02`: `lo ≤ hi` ⟹ `lo ≤ ret ≤ hi ∧ ret = hi + 1` (dishonest off-by-one clamp).
* `CL_VAC_03`: `ret = ret ∨ ret = 0` (disguised reflexive tautology).
* `CL_VAC_04`: `lo ≤ hi` ⟹ `let _ = ret; lo ≤ hi` (discarded output).
* `CL_VAC_05`: `x < 10` ⟹ `x < 10 ∨ ret = 42` (`requires`-masked postcondition).

Lean reaches each verdict statically (`checkEnsuresBindsOutput`, backed by the kernel
theorems below); Rust reaches it dynamically (`check_contract` /
`check_stateful_contract` with the classification probe allowed to leave the
precondition, matching the fact that the static analysis reasons about `ensures` on
every input).
-/

/-! ##### `CL_POS_01_checked_add_u32` -/

def CL_POS_01_checked_add_u32_pre (a b : Nat) : Prop :=
  a < 4294967296 ∧ b < 4294967296

def CL_POS_01_checked_add_u32_post (a b : Nat) (ret : Option Nat) : Prop :=
  (a + b < 4294967296 ∧ ret = some (a + b)) ∨ (4294967296 ≤ a + b ∧ ret = none)

theorem CL_POS_01_checked_add_u32_realizable_some :
    ContractRealizable (fun p : Nat × Nat => CL_POS_01_checked_add_u32_pre p.1 p.2)
      (fun p ret => CL_POS_01_checked_add_u32_post p.1 p.2 ret) := by
  refine ⟨(2, 3), ?_, some 5, ?_⟩ <;>
    simp [CL_POS_01_checked_add_u32_pre, CL_POS_01_checked_add_u32_post]

theorem CL_POS_01_checked_add_u32_realizable_none :
    ContractRealizable (fun p : Nat × Nat => CL_POS_01_checked_add_u32_pre p.1 p.2)
      (fun p ret => CL_POS_01_checked_add_u32_post p.1 p.2 ret) := by
  refine ⟨(4294967295, 1), ?_, none, ?_⟩ <;>
    simp [CL_POS_01_checked_add_u32_pre, CL_POS_01_checked_add_u32_post]

theorem CL_POS_01_checked_add_u32_dichotomy :
    PostconditionDichotomy (fun p : Nat × Nat => CL_POS_01_checked_add_u32_pre p.1 p.2)
      (fun p ret => CL_POS_01_checked_add_u32_post p.1 p.2 ret) := by
  refine ⟨(2, 3), ?_, ⟨some 5, ?_⟩, ⟨none, ?_⟩⟩ <;>
    simp [CL_POS_01_checked_add_u32_pre, CL_POS_01_checked_add_u32_post]

/-! ##### `CL_POS_02_slice_bounds_and_empty` -/

def CL_POS_02_slice_bounds_and_empty_pre (len idx : Nat) : Prop := idx ≤ len

/-- `ret.1` is `is_empty` and `ret.2` is whether `idx` is a valid index. -/
def CL_POS_02_slice_bounds_and_empty_post (len idx : Nat) (ret : Bool × Bool) : Prop :=
  (ret.1 = true ↔ len = 0) ∧ (ret.2 = true ↔ idx < len)

theorem CL_POS_02_slice_bounds_and_empty_realizable_empty :
    ContractRealizable (fun p : Nat × Nat => CL_POS_02_slice_bounds_and_empty_pre p.1 p.2)
      (fun p ret => CL_POS_02_slice_bounds_and_empty_post p.1 p.2 ret) := by
  refine ⟨(0, 0), ?_, (true, false), ?_⟩ <;>
    simp [CL_POS_02_slice_bounds_and_empty_pre, CL_POS_02_slice_bounds_and_empty_post]

theorem CL_POS_02_slice_bounds_and_empty_realizable_in_bounds :
    ContractRealizable (fun p : Nat × Nat => CL_POS_02_slice_bounds_and_empty_pre p.1 p.2)
      (fun p ret => CL_POS_02_slice_bounds_and_empty_post p.1 p.2 ret) := by
  refine ⟨(1, 0), ?_, (false, true), ?_⟩ <;>
    simp [CL_POS_02_slice_bounds_and_empty_pre, CL_POS_02_slice_bounds_and_empty_post]

theorem CL_POS_02_slice_bounds_and_empty_dichotomy :
    PostconditionDichotomy
      (fun p : Nat × Nat => CL_POS_02_slice_bounds_and_empty_pre p.1 p.2)
      (fun p ret => CL_POS_02_slice_bounds_and_empty_post p.1 p.2 ret) := by
  refine ⟨(0, 0), ?_, ⟨(true, false), ?_⟩, ⟨(false, false), ?_⟩⟩ <;>
    simp [CL_POS_02_slice_bounds_and_empty_pre, CL_POS_02_slice_bounds_and_empty_post]

/-! ##### `CL_POS_03_saturating_clamp_u32` -/

def CL_POS_03_saturating_clamp_u32_pre (_val lo hi : Nat) : Prop := lo ≤ hi

def CL_POS_03_saturating_clamp_u32_post (val lo hi ret : Nat) : Prop :=
  lo ≤ ret ∧ ret ≤ hi ∧
    ((val < lo ∧ ret = lo) ∨ (hi < val ∧ ret = hi) ∨ (lo ≤ val ∧ val ≤ hi ∧ ret = val))

theorem CL_POS_03_saturating_clamp_u32_realizable_eq_bounds :
    ContractRealizable
      (fun p : Nat × Nat × Nat => CL_POS_03_saturating_clamp_u32_pre p.1 p.2.1 p.2.2)
      (fun p ret => CL_POS_03_saturating_clamp_u32_post p.1 p.2.1 p.2.2 ret) := by
  refine ⟨(7, 3, 3), ?_, 3, ?_⟩ <;>
    simp [CL_POS_03_saturating_clamp_u32_pre, CL_POS_03_saturating_clamp_u32_post]

theorem CL_POS_03_saturating_clamp_u32_dichotomy :
    PostconditionDichotomy
      (fun p : Nat × Nat × Nat => CL_POS_03_saturating_clamp_u32_pre p.1 p.2.1 p.2.2)
      (fun p ret => CL_POS_03_saturating_clamp_u32_post p.1 p.2.1 p.2.2 ret) := by
  refine ⟨(5, 0, 10), ?_, ⟨5, ?_⟩, ⟨6, ?_⟩⟩ <;>
    simp [CL_POS_03_saturating_clamp_u32_pre, CL_POS_03_saturating_clamp_u32_post]

/-! ##### `CL_POS_04_stateful_bounded_step` -/

/-- Pre-state `(val, limit)` of the bounded counter behind `&mut self`. -/
def CL_POS_04_stateful_bounded_step_pre (val limit : Nat) : Prop :=
  val < limit ∧ limit < 4294967296

/-- `ret.1` is the returned value, `ret.2.1` the post-state `val'`, and `ret.2.2` the
    post-state `limit'`. -/
def CL_POS_04_stateful_bounded_step_post
    (val limit : Nat) (ret : Nat × Nat × Nat) : Prop :=
  ret.1 = val + 1 ∧ ret.2.1 = val + 1 ∧ ret.2.2 = limit

theorem CL_POS_04_stateful_bounded_step_dichotomy :
    PostconditionDichotomy
      (fun p : Nat × Nat => CL_POS_04_stateful_bounded_step_pre p.1 p.2)
      (fun p ret => CL_POS_04_stateful_bounded_step_post p.1 p.2 ret) := by
  refine ⟨(0, 1), ?_, ⟨(1, 1, 1), ?_⟩, ⟨(2, 1, 1), ?_⟩⟩ <;>
    simp [CL_POS_04_stateful_bounded_step_pre, CL_POS_04_stateful_bounded_step_post]

/-- The return value is constrained with the post-state held fixed (the Rust checker's
    return-value mutant axis). -/
theorem CL_POS_04_stateful_bounded_step_returnAxisDichotomy :
    DichotomyModuloObservation
      (fun (_ : Nat × Nat) (ret : Nat × Nat × Nat) => ret.2)
      (fun p : Nat × Nat => CL_POS_04_stateful_bounded_step_pre p.1 p.2)
      (fun p ret => CL_POS_04_stateful_bounded_step_post p.1 p.2 ret) := by
  refine ⟨(0, 1), ?_, (1, 1, 1), (2, 1, 1), ?_, ?_, ?_⟩ <;>
    simp [CL_POS_04_stateful_bounded_step_pre, CL_POS_04_stateful_bounded_step_post]

/-- The post-state is constrained with the return value held fixed (the Rust checker's
    state mutant axis). -/
theorem CL_POS_04_stateful_bounded_step_stateAxisDichotomy :
    DichotomyModuloObservation
      (fun (_ : Nat × Nat) (ret : Nat × Nat × Nat) => ret.1)
      (fun p : Nat × Nat => CL_POS_04_stateful_bounded_step_pre p.1 p.2)
      (fun p ret => CL_POS_04_stateful_bounded_step_post p.1 p.2 ret) := by
  refine ⟨(0, 1), ?_, (1, 1, 1), (1, 2, 1), ?_, ?_, ?_⟩ <;>
    simp [CL_POS_04_stateful_bounded_step_pre, CL_POS_04_stateful_bounded_step_post]

/-! ##### `CL_VAC_01_dead_precondition` -/

def CL_VAC_01_dead_precondition_pre (x : Nat) : Prop := x > 100 ∧ x < 50

def CL_VAC_01_dead_precondition_post (x ret : Nat) : Prop := ret = x

theorem CL_VAC_01_dead_precondition_pre_unsat :
    ¬ PreconditionSatisfiable CL_VAC_01_dead_precondition_pre := by
  rintro ⟨x, hGt, hLt⟩
  omega

theorem CL_VAC_01_dead_precondition_not_realizable :
    ¬ ContractRealizable CL_VAC_01_dead_precondition_pre CL_VAC_01_dead_precondition_post :=
  not_contractRealizable_of_unsat_pre CL_VAC_01_dead_precondition_pre_unsat

/-! ##### `CL_VAC_02_spec_violation` -/

def CL_VAC_02_spec_violation_pre (_val lo hi : Nat) : Prop := lo ≤ hi

/-- Dishonest off-by-one clamp: the result is claimed to lie in `[lo, hi]` and to equal
    `hi + 1`. -/
def CL_VAC_02_spec_violation_post (_val lo hi ret : Nat) : Prop :=
  lo ≤ ret ∧ ret ≤ hi ∧ ret = hi + 1

theorem CL_VAC_02_spec_violation_unrealizable (val lo hi ret : Nat) :
    ¬ CL_VAC_02_spec_violation_post val lo hi ret := by
  rintro ⟨_, hLe, hEq⟩
  omega

theorem CL_VAC_02_spec_violation_not_realizable :
    ¬ ContractRealizable
        (fun p : Nat × Nat × Nat => CL_VAC_02_spec_violation_pre p.1 p.2.1 p.2.2)
        (fun p ret => CL_VAC_02_spec_violation_post p.1 p.2.1 p.2.2 ret) := by
  rintro ⟨p, _, ret, hPost⟩
  exact CL_VAC_02_spec_violation_unrealizable p.1 p.2.1 p.2.2 ret hPost

/-! ##### `CL_VAC_03_trivial_postcondition` -/

def CL_VAC_03_trivial_postcondition_post (_x ret : Nat) : Prop := ret = ret ∨ ret = 0

theorem CL_VAC_03_trivial_postcondition_not_dichotomy :
    ¬ PostconditionDichotomy (fun _ : Nat => True) CL_VAC_03_trivial_postcondition_post :=
  not_postconditionDichotomy_of_trivial (fun _ _ _ => Or.inl rfl)

/-! ##### `CL_VAC_04_unbound_return_output` -/

def CL_VAC_04_unbound_return_output_pre (_val lo hi : Nat) : Prop := lo ≤ hi

def CL_VAC_04_unbound_return_output_post (_val lo hi ret : Nat) : Prop :=
  let _ := ret
  lo ≤ hi

theorem CL_VAC_04_unbound_return_output_not_dichotomy :
    ¬ PostconditionDichotomy
        (fun p : Nat × Nat × Nat => CL_VAC_04_unbound_return_output_pre p.1 p.2.1 p.2.2)
        (fun p ret => CL_VAC_04_unbound_return_output_post p.1 p.2.1 p.2.2 ret) :=
  not_postconditionDichotomy_of_forwardOutputInsensitive (fun _ _ _ _ h => h)

/-! ##### `CL_VAC_05_survived_all_mutants` -/

def CL_VAC_05_survived_all_mutants_pre (x : Nat) : Prop := x < 10

def CL_VAC_05_survived_all_mutants_post (x ret : Nat) : Prop := x < 10 ∨ ret = 42

theorem CL_VAC_05_survived_all_mutants_not_dichotomy :
    ¬ PostconditionDichotomy
        CL_VAC_05_survived_all_mutants_pre CL_VAC_05_survived_all_mutants_post :=
  not_postconditionDichotomy_of_trivial (fun _ _ hPre => Or.inl hPre)

/-- Outside `requires` the same postcondition does bind the output, which is what
    separates `SurvivedAllMutants` from `TrivialPostcondition` and
    `UnboundReturnOutput`. -/
theorem CL_VAC_05_survived_all_mutants_dichotomy_without_requires :
    PostconditionDichotomy (fun _ : Nat => True) CL_VAC_05_survived_all_mutants_post := by
  refine ⟨10, trivial, ⟨42, ?_⟩, ⟨0, ?_⟩⟩ <;> simp [CL_VAC_05_survived_all_mutants_post]

/-! ##### The Matrix, Checked at Compile Time -/

/-- One row of the benchmark matrix: its canonical cross-language ID and the names of
    its `ensures` and (optional) `requires` predicates. -/
structure Benchmark where
  benchmarkId : String
  ensuresName : Lean.Name
  requiresName? : Option Lean.Name

/-- The 4 shared strong contracts, in canonical order. -/
def positiveBenchmarks : List Benchmark := [
  { benchmarkId := "CL_POS_01_checked_add_u32"
    ensuresName := ``CL_POS_01_checked_add_u32_post
    requiresName? := some ``CL_POS_01_checked_add_u32_pre },
  { benchmarkId := "CL_POS_02_slice_bounds_and_empty"
    ensuresName := ``CL_POS_02_slice_bounds_and_empty_post
    requiresName? := some ``CL_POS_02_slice_bounds_and_empty_pre },
  { benchmarkId := "CL_POS_03_saturating_clamp_u32"
    ensuresName := ``CL_POS_03_saturating_clamp_u32_post
    requiresName? := some ``CL_POS_03_saturating_clamp_u32_pre },
  { benchmarkId := "CL_POS_04_stateful_bounded_step"
    ensuresName := ``CL_POS_04_stateful_bounded_step_post
    requiresName? := some ``CL_POS_04_stateful_bounded_step_pre }
]

/-- The 5 shared intentional vacuity mutants with their expected class, in canonical
    order. -/
def vacuityBenchmarks : List (Benchmark × VacuityClass) := [
  ({ benchmarkId := "CL_VAC_01_dead_precondition"
     ensuresName := ``CL_VAC_01_dead_precondition_post
     requiresName? := some ``CL_VAC_01_dead_precondition_pre }, .deadPrecondition),
  ({ benchmarkId := "CL_VAC_02_spec_violation"
     ensuresName := ``CL_VAC_02_spec_violation_post
     requiresName? := some ``CL_VAC_02_spec_violation_pre }, .specViolation),
  ({ benchmarkId := "CL_VAC_03_trivial_postcondition"
     ensuresName := ``CL_VAC_03_trivial_postcondition_post
     requiresName? := none }, .trivialPostcondition),
  ({ benchmarkId := "CL_VAC_04_unbound_return_output"
     ensuresName := ``CL_VAC_04_unbound_return_output_post
     requiresName? := some ``CL_VAC_04_unbound_return_output_pre }, .unboundReturnOutput),
  ({ benchmarkId := "CL_VAC_05_survived_all_mutants"
     ensuresName := ``CL_VAC_05_survived_all_mutants_post
     requiresName? := some ``CL_VAC_05_survived_all_mutants_pre }, .survivedAllMutants)
]

/-- The class names `CL_VAC_01..CL_VAC_05` must emit, in order. The Rust suite pins the
    same list (`EXPECTED_CLASS_NAMES`). -/
def expectedClassNames : List String :=
  ["DeadPrecondition", "SpecViolation", "TrivialPostcondition", "UnboundReturnOutput",
    "SurvivedAllMutants"]

-- The benchmark IDs are the canonical ones, in canonical order.
#eval show Lean.Meta.MetaM Unit from do
  let positiveIds := positiveBenchmarks.map (fun b => b.benchmarkId)
  unless positiveIds ==
      ["CL_POS_01_checked_add_u32", "CL_POS_02_slice_bounds_and_empty",
        "CL_POS_03_saturating_clamp_u32", "CL_POS_04_stateful_bounded_step"] do
    throwError "unexpected positive benchmark IDs: {positiveIds}"
  let vacuityIds := vacuityBenchmarks.map (fun row => row.1.benchmarkId)
  unless vacuityIds ==
      ["CL_VAC_01_dead_precondition", "CL_VAC_02_spec_violation",
        "CL_VAC_03_trivial_postcondition", "CL_VAC_04_unbound_return_output",
        "CL_VAC_05_survived_all_mutants"] do
    throwError "unexpected vacuity benchmark IDs: {vacuityIds}"

/-- Run the static checker on one row of the matrix. -/
def checkBenchmark (b : Benchmark) : Lean.Meta.MetaM EnsuresCheckResult :=
  checkEnsuresBindsOutput (Lean.mkConst b.ensuresName)
    (b.requiresName?.map (fun n => Lean.mkConst n))

/-- Assert that positive row `idx` is accepted as a strong contract whose `requires`
    is never refuted. -/
def assertPositiveRow (idx : Nat) : Lean.Meta.MetaM Unit := do
  let some b := positiveBenchmarks[idx]?
    | throwError "no positive benchmark at row {idx}"
  let res ← checkBenchmark b
  unless res.bindsOutput do
    throwError "{b.benchmarkId}: expected a strong contract, got {repr res}"
  if let some pre := b.requiresName? then
    let sat ← checkRequiresSatisfiable (Lean.mkConst pre)
    if sat.satisfiable? == some false then
      throwError "{b.benchmarkId}: requires was refuted: {repr sat}"

/-- Assert that vacuity row `idx` is flagged with exactly its expected class, and that
    the canonical name it emits is entry `idx` of `expectedClassNames`. -/
def assertVacuityRow (idx : Nat) : Lean.Meta.MetaM Unit := do
  let some (b, expected) := vacuityBenchmarks[idx]?
    | throwError "no vacuity benchmark at row {idx}"
  let res ← checkBenchmark b
  if res.bindsOutput then
    throwError "{b.benchmarkId}: expected {expected.canonicalName}, but it was accepted"
  let some cls := res.vacuityClass?
    | throwError "{b.benchmarkId}: flagged vacuous without a VacuityClass"
  unless cls == expected do
    throwError "{b.benchmarkId}: expected {expected.canonicalName}, got \
      {cls.canonicalName} ({repr res})"
  unless expectedClassNames[idx]? == some cls.canonicalName do
    throwError "{b.benchmarkId}: emitted {cls.canonicalName} out of cross-language order"

-- The matrix has 4 strong contracts and 5 vacuity mutants, and its expected-class
-- column is the canonical name list in the shared 1:1 order.
#eval show Lean.Meta.MetaM Unit from do
  unless positiveBenchmarks.length == 4 && vacuityBenchmarks.length == 5 do
    throwError "the matrix must hold 4 strong contracts and 5 vacuity mutants"
  let expectedColumn := vacuityBenchmarks.map (fun row => row.2.canonicalName)
  unless expectedColumn == expectedClassNames do
    throwError "expected-class column out of cross-language order: {expectedColumn}"

-- `CL_POS_01..CL_POS_04`: every strong contract is accepted, and its `requires` is
-- never refuted. Each row is checked by its own command, so every row gets a full
-- probe budget.
#eval assertPositiveRow 0
#eval assertPositiveRow 1
#eval assertPositiveRow 2
#eval assertPositiveRow 3

-- The MIR-level `&mut`-state form of `CL_POS_04_stateful_bounded_step` (a
-- `StatefulClaim` over `Memory`) passes with the post-memory held fixed.
#eval assertDeclEnsuresBindsOutput ``statefulCounterStepClaim { strictReturnValue := true }

-- `CL_VAC_01..CL_VAC_05`: row `i` is flagged with exactly its expected class and emits
-- entry `i` of `expectedClassNames`, so the five canonical class names come out as
-- `["DeadPrecondition", "SpecViolation", "TrivialPostcondition", "UnboundReturnOutput",
-- "SurvivedAllMutants"]` in exact 1:1 order.
#eval assertVacuityRow 0
#eval assertVacuityRow 1
#eval assertVacuityRow 2
#eval assertVacuityRow 3
#eval assertVacuityRow 4

-- `CL_VAC_01_dead_precondition`: the `requires` itself is refuted.
#eval show Lean.Meta.MetaM Unit from do
  let dead ← checkRequiresSatisfiable (Lean.mkConst ``CL_VAC_01_dead_precondition_pre)
  unless dead.satisfiable? == some false do
    throwError "CL_VAC_01_dead_precondition: expected a refuted requires, got {repr dead}"

-- The frozen taxonomy enumerates the classes in the same order, and every canonical
-- name parses back to its class.
#eval show Lean.Meta.MetaM Unit from do
  unless VacuityClass.all.map VacuityClass.canonicalName == expectedClassNames do
    throwError "VacuityClass.all is out of cross-language order"
  for c in VacuityClass.all do
    unless VacuityClass.ofCanonicalName? c.canonicalName == some c do
      throwError "canonical name {c.canonicalName} does not round-trip"
  unless (VacuityClass.ofCanonicalName? "NotAVacuityClass").isNone do
    throwError "an unknown canonical name was parsed"

end CrossLanguageParitySuite

/-! ### 3.22 Indirect Vacuity Disguises: Branch Projections, Quantifier Wrappers & Boilerplate Bounds -/

/-- Projection over `ite` discarding `ret` in both branches (`UnboundReturnOutput`). -/
def iteTupleDiscardedPost (x ret : Nat) : Prop :=
  (if x < 10 then (True, ret) else (True, ret)).1

/-- Projection over `ite` with input-dependent non-trivial branches (`UnboundReturnOutput`). -/
def iteProdDiscardedPost (x ret : Nat) : Prop :=
  (if x < 10 then (x, ret) else (x + 1, ret)).1 = x

/-- Projection over `dite` discarding `ret` (`UnboundReturnOutput`). -/
def diteProdDiscardedPost (x ret : Nat) : Prop :=
  (if _ : x < 10 then (x, ret) else (x, ret)).1 = x

/-- Projection over `match` discarding `ret` (`UnboundReturnOutput`). -/
def matchBoolProdDiscardedPost (b : Bool) (x ret : Nat) : Prop :=
  (match b with
  | true => (x, ret)
  | false => (x + 1, ret)).1 = x

/-- Projection over `ite` with contradictory `False` branches (`SpecViolation`). -/
def iteTupleContraPost (x ret : Nat) : Prop :=
  (if x < 10 then (False, ret) else (False, ret)).1

/-- Negative control: projection over `match` genuinely keeping `ret` in field 1. -/
def matchBoolProdGenuinePost (b : Bool) (x ret : Nat) : Prop :=
  (match b with
  | true => (ret, x)
  | false => (ret, x + 1)).1 = x

/-- Existential wrapper `∃ k, k = ret` (trivially true via `⟨ret, rfl⟩`). -/
def existsEqRetPost (_x ret : Nat) : Prop :=
  ∃ k : Nat, k = ret

/-- Symmetric existential wrapper `∃ k, ret = k`. -/
def existsRetEqPost (_x ret : Nat) : Prop :=
  ∃ k : Nat, ret = k

/-- Branching existential wrapper: trivially true in every branch, yet neither
    `simp_all`, `omega`, nor `grind` synthesizes the branching Skolem witness. -/
def existsBranchEqRetPost (x ret : Nat) : Prop :=
  ∃ k : Nat, if x < 10 then k = ret else k = ret + 1

/-- Existential wrapper over `Unit` paired with a discarded `let _ := ret`. -/
def existsUnitDiscardedPost (_x ret : Nat) : Prop :=
  ∃ u : Unit, u = () ∧ (let _ := ret; True)

/-- One-point existential masking an input-only predicate (`UnboundReturnOutput`). -/
def existsOnePointInputOnlyPost (x ret : Nat) : Prop :=
  ∃ k : Nat, k = ret ∧ x < 10

/-- Universal tautology `∀ k, k = ret → k = ret` (implication inside a dependent `∀`). -/
def forallEqSelfImpPost (_x ret : Nat) : Prop :=
  ∀ k : Nat, k = ret → k = ret

/-- Universal symmetric tautology `∀ k, k = ret → ret = k`. -/
def forallEqSymmImpPost (_x ret : Nat) : Prop :=
  ∀ k : Nat, k = ret → ret = k

/-- User helper predicates hidden beneath `∃` and dependent `∀`. -/
def helperEqPred (a b : Nat) : Prop := a = b
def helperTruePred (_a _b : Nat) : Prop := True

def existsHiddenHelperPost (_x ret : Nat) : Prop :=
  ∃ k : Nat, helperEqPred k ret

def forallHiddenHelperPost (_x ret : Nat) : Prop :=
  ∀ k : Nat, helperTruePred k ret

/-- `BEq` reflexivity over lawful `Nat` (`(ret == ret) = true`, caught by prover). -/
def beqSelfNatPost (_x ret : Nat) : Prop :=
  (ret == ret) = true

/-- `decide (ret ≠ ret) = false` (syntactically tautological in all models). -/
def decideNeFalsePost (_x ret : Nat) : Prop :=
  decide (ret ≠ ret) = false

/-- Negative control: one-point existential genuinely constraining `ret = x`. -/
def existsOnePointGenuinePost (x ret : Nat) : Prop :=
  ∃ k : Nat, k = ret ∧ k = x

/-- Negative control: universal implication genuinely bounding `ret` by `x`. -/
def forallGenuineBoundPost (x ret : Nat) : Prop :=
  ∀ k : Nat, k < ret → k < x

/-- External-spec `extraPost` merely restating `retMatchesCalleeReturnTy` for `u32`. -/
def restatesU32BoundsExtraPost (_args : List Value) (retVal : Value) : Prop :=
  match retVal with
  | .scalar sv => sv.bits < scalarModulus 4
  | _ => False

def restatesU32BoundsExtContract : MirCallContract :=
  externalSpecCallContract "test::u32_bounds_only" rangeClampSidecar
    (fun _ => True) restatesU32BoundsExtraPost

/-- External-spec `extraPost` merely restating `retMatchesCalleeReturnTy` for `bool`. -/
def restatesBoolBoundsExtraPost (_args : List Value) (retVal : Value) : Prop :=
  match retVal with
  | .scalar sv => sv.bits = 0 ∨ sv.bits = 1
  | _ => False

def restatesBoolBoundsExtContract : MirCallContract :=
  externalSpecCallContract "test::bool_bounds_only" sliceIsEmptySidecar
    (fun _ => True) restatesBoolBoundsExtraPost

/-- External-spec boilerplate wrapped in a one-point existential `∃ k, k = retVal ∧ ...`. -/
def existsWrappedBoilerplateContract : MirCallContract := {
  pre := fun _ => True
  post := fun req ans =>
    match ans with
    | .returned retVal memAfter =>
      ∃ k : Value, k = retVal ∧
        callFramePreserved req.memory memAfter ∧
        retMatchesCalleeReturnTy rangeClampSidecar k
    | .panicked _ => False
    | .aborted => True
}

theorem iteTupleDiscardedPost_not_dichotomy :
    ¬ PostconditionDichotomy (fun _ : Nat => True) iteTupleDiscardedPost :=
  not_postconditionDichotomy_of_trivial (fun x _ _ => by
    by_cases hx : x < 10 <;> simp [iteTupleDiscardedPost, hx])

theorem iteProdDiscardedPost_not_dichotomy :
    ¬ PostconditionDichotomy (fun _ : Nat => True) iteProdDiscardedPost :=
  not_postconditionDichotomy_of_forwardOutputInsensitive (fun x _ _ _ h => by
    by_cases hx : x < 10 <;> simp_all [iteProdDiscardedPost])

theorem diteProdDiscardedPost_not_dichotomy :
    ¬ PostconditionDichotomy (fun _ : Nat => True) diteProdDiscardedPost :=
  not_postconditionDichotomy_of_trivial (fun x _ _ => by
    by_cases hx : x < 10 <;> simp [diteProdDiscardedPost, hx])

theorem matchBoolProdDiscardedPost_not_dichotomy :
    ¬ PostconditionDichotomy
        (fun _ : Bool × Nat => True)
        (fun p ret => matchBoolProdDiscardedPost p.1 p.2 ret) :=
  not_postconditionDichotomy_of_forwardOutputInsensitive (fun p _ _ _ h => by
    rcases p with ⟨b, x⟩
    cases b <;> exact h)

theorem iteTupleContraPost_not_realizable :
    ¬ ContractRealizable (fun _ : Nat => True) iteTupleContraPost := by
  rintro ⟨x, _, _, h⟩
  by_cases hx : x < 10 <;> simp [iteTupleContraPost, hx] at h

theorem matchBoolProdGenuinePost_dichotomy :
    PostconditionDichotomy
        (fun _ : Bool × Nat => True)
        (fun p ret => matchBoolProdGenuinePost p.1 p.2 ret) := by
  refine ⟨(true, 0), trivial, ⟨0, rfl⟩, ⟨1, by simp [matchBoolProdGenuinePost]⟩⟩

theorem existsEqRetPost_not_dichotomy :
    ¬ PostconditionDichotomy (fun _ : Nat => True) existsEqRetPost :=
  not_postconditionDichotomy_of_trivial (fun _ ret _ => ⟨ret, rfl⟩)

theorem existsRetEqPost_not_dichotomy :
    ¬ PostconditionDichotomy (fun _ : Nat => True) existsRetEqPost :=
  not_postconditionDichotomy_of_trivial (fun _ ret _ => ⟨ret, rfl⟩)

theorem existsBranchEqRetPost_not_dichotomy :
    ¬ PostconditionDichotomy (fun _ : Nat => True) existsBranchEqRetPost :=
  not_postconditionDichotomy_of_trivial (fun x ret _ => by
    dsimp [existsBranchEqRetPost]
    by_cases hx : x < 10
    · exact ⟨ret, by simp [hx]⟩
    · exact ⟨ret + 1, by simp [hx]⟩)

theorem existsUnitDiscardedPost_not_dichotomy :
    ¬ PostconditionDichotomy (fun _ : Nat => True) existsUnitDiscardedPost :=
  not_postconditionDichotomy_of_trivial (fun _ _ _ => ⟨(), rfl, trivial⟩)

theorem existsOnePointInputOnlyPost_not_dichotomy :
    ¬ PostconditionDichotomy (fun _ : Nat => True) existsOnePointInputOnlyPost :=
  not_postconditionDichotomy_of_forwardOutputInsensitive (fun _ _ _ y₂ ⟨_, _, hx⟩ =>
    ⟨y₂, rfl, hx⟩)

theorem forallEqSelfImpPost_not_dichotomy :
    ¬ PostconditionDichotomy (fun _ : Nat => True) forallEqSelfImpPost :=
  not_postconditionDichotomy_of_trivial (fun _ _ _ _ h => h)

theorem forallEqSymmImpPost_not_dichotomy :
    ¬ PostconditionDichotomy (fun _ : Nat => True) forallEqSymmImpPost :=
  not_postconditionDichotomy_of_trivial (fun _ _ _ _ h => h.symm)

theorem existsHiddenHelperPost_not_dichotomy :
    ¬ PostconditionDichotomy (fun _ : Nat => True) existsHiddenHelperPost :=
  not_postconditionDichotomy_of_trivial (fun _ ret _ => ⟨ret, rfl⟩)

theorem forallHiddenHelperPost_not_dichotomy :
    ¬ PostconditionDichotomy (fun _ : Nat => True) forallHiddenHelperPost :=
  not_postconditionDichotomy_of_trivial (fun _ _ _ _ => trivial)

theorem beqSelfNatPost_not_dichotomy :
    ¬ PostconditionDichotomy (fun _ : Nat => True) beqSelfNatPost :=
  not_postconditionDichotomy_of_trivial (fun _ _ _ => by simp [beqSelfNatPost])

theorem decideNeFalsePost_not_dichotomy :
    ¬ PostconditionDichotomy (fun _ : Nat => True) decideNeFalsePost :=
  not_postconditionDichotomy_of_trivial (fun _ _ _ => by simp [decideNeFalsePost])

theorem existsOnePointGenuinePost_dichotomy :
    PostconditionDichotomy (fun _ : Nat => True) existsOnePointGenuinePost := by
  refine ⟨0, trivial, ⟨0, 0, rfl, rfl⟩, ⟨1, ?_⟩⟩
  rintro ⟨_, hk1, hk0⟩
  exact Nat.succ_ne_zero 0 (hk1.symm.trans hk0)

theorem forallGenuineBoundPost_dichotomy :
    PostconditionDichotomy (fun _ : Nat => True) forallGenuineBoundPost := by
  refine ⟨0, trivial, ⟨0, by simp [forallGenuineBoundPost]⟩, ⟨1, ?_⟩⟩
  intro h
  have hZero : 0 < 0 := h 0 (by decide)
  omega

theorem restatesU32BoundsExtContract_not_ensuresDichotomy :
    ¬ ExternalSpecEnsuresDichotomy "test::u32_bounds_only" rangeClampSidecar
        (fun _ => True) restatesU32BoundsExtraPost := by
  intro h
  rcases (externalSpecEnsuresDichotomy_iff_moduloObservation
    "test::u32_bounds_only" rangeClampSidecar
    (fun _ => True) restatesU32BoundsExtraPost).mp h with
    ⟨_, _, _, v_bad, _, _, _, hTyBad, _, hNotBad⟩
  have hTy : ∃ bits : Nat, bits < scalarModulus 4 ∧
      v_bad = .scalar { bits := bits, sizeBytes := 4 } := hTyBad
  rcases hTy with ⟨bits, hLt, hEq⟩
  subst hEq
  exact hNotBad hLt

theorem restatesBoolBoundsExtContract_not_ensuresDichotomy :
    ¬ ExternalSpecEnsuresDichotomy "test::bool_bounds_only" sliceIsEmptySidecar
        (fun _ => True) restatesBoolBoundsExtraPost := by
  intro h
  rcases (externalSpecEnsuresDichotomy_iff_moduloObservation
    "test::bool_bounds_only" sliceIsEmptySidecar
    (fun _ => True) restatesBoolBoundsExtraPost).mp h with
    ⟨_, _, _, v_bad, _, _, _, hTyBad, _, hNotBad⟩
  have hTy : ∃ b : Nat, b < 2 ∧
      v_bad = .scalar { bits := b, sizeBytes := 1 } := hTyBad
  rcases hTy with ⟨b, hLt, hEq⟩
  subst hEq
  exact hNotBad (by dsimp [restatesBoolBoundsExtraPost]; omega)

theorem existsWrappedBoilerplateContract_not_dichotomyModuloObs :
    ¬ DichotomyModuloObservation
        (externalSpecBoilerplateObs rangeClampSidecar)
        existsWrappedBoilerplateContract.pre
        (fun req q => existsWrappedBoilerplateContract.post req (.returned q.1 q.2)) := by
  apply not_dichotomyModuloObservation_of_fibre_forwardInsensitive
  intro req q₁ q₂ _ hObsEq hOk
  dsimp [existsWrappedBoilerplateContract] at hOk ⊢
  rcases hOk with ⟨k, hk, hFrame₁, hTyK⟩
  subst hk
  have hFrameEq : callFramePreserved req.memory q₁.2 = callFramePreserved req.memory q₂.2 :=
    congrArg Prod.fst hObsEq
  have hTyEq : retMatchesCalleeReturnTy rangeClampSidecar q₁.1 =
      retMatchesCalleeReturnTy rangeClampSidecar q₂.1 :=
    congrArg Prod.snd hObsEq
  exact ⟨q₂.1, rfl, hFrameEq ▸ hFrame₁, hTyEq ▸ hTyK⟩

-- Branch projections (`ite`/`dite`/`match`) drop discarded outputs syntactically even
-- with zero prover budget.
#eval assertEnsuresVacuous (Lean.mkConst ``iteTupleDiscardedPost) none
  (some .unboundReturnOutput) { stepHeartbeats := 0, totalHeartbeats := 0 }
#eval assertEnsuresVacuous (Lean.mkConst ``iteProdDiscardedPost) none
  (some .unboundReturnOutput) { stepHeartbeats := 0, totalHeartbeats := 0 }
#eval assertEnsuresVacuous (Lean.mkConst ``diteProdDiscardedPost) none
  (some .unboundReturnOutput) { stepHeartbeats := 0, totalHeartbeats := 0 }
#eval assertEnsuresVacuous (Lean.mkConst ``matchBoolProdDiscardedPost) none
  (some .unboundReturnOutput) { stepHeartbeats := 0, totalHeartbeats := 0 }
#eval assertEnsuresVacuous (Lean.mkConst ``iteTupleContraPost) none
  (some .specViolation) { stepHeartbeats := 0, totalHeartbeats := 0 }
#eval assertEnsuresBindsOutput (Lean.mkConst ``matchBoolProdGenuinePost)

-- Existential wrappers, dependent universal tautologies, hidden helpers, and `decide`/`BEq`.
#eval assertEnsuresVacuous (Lean.mkConst ``existsEqRetPost) none
  (some .trivialPostcondition) { stepHeartbeats := 0, totalHeartbeats := 0 }
#eval assertEnsuresVacuous (Lean.mkConst ``existsRetEqPost) none
  (some .trivialPostcondition) { stepHeartbeats := 0, totalHeartbeats := 0 }
#eval assertEnsuresVacuous (Lean.mkConst ``existsBranchEqRetPost) none
  (some .trivialPostcondition) { stepHeartbeats := 0, totalHeartbeats := 0 }
#eval assertEnsuresVacuous (Lean.mkConst ``existsUnitDiscardedPost) none
  (some .unboundReturnOutput) { stepHeartbeats := 0, totalHeartbeats := 0 }
#eval assertEnsuresVacuous (Lean.mkConst ``existsOnePointInputOnlyPost) none
  (some .unboundReturnOutput) { stepHeartbeats := 0, totalHeartbeats := 0 }
#eval assertEnsuresVacuous (Lean.mkConst ``forallEqSelfImpPost) none
  (some .trivialPostcondition) { stepHeartbeats := 0, totalHeartbeats := 0 }
#eval assertEnsuresVacuous (Lean.mkConst ``forallEqSymmImpPost) none
  (some .trivialPostcondition) { stepHeartbeats := 0, totalHeartbeats := 0 }
#eval assertEnsuresVacuous (Lean.mkConst ``existsHiddenHelperPost) none
  (some .trivialPostcondition) { stepHeartbeats := 0, totalHeartbeats := 0 }
#eval assertEnsuresVacuous (Lean.mkConst ``forallHiddenHelperPost) none
  (some .trivialPostcondition) { stepHeartbeats := 0, totalHeartbeats := 0 }
#eval assertEnsuresVacuous (Lean.mkConst ``beqSelfNatPost) none (some .trivialPostcondition)
#eval assertEnsuresVacuous (Lean.mkConst ``decideNeFalsePost) none
  (some .trivialPostcondition) { stepHeartbeats := 0, totalHeartbeats := 0 }
#eval assertEnsuresBindsOutput (Lean.mkConst ``existsOnePointGenuinePost)
#eval assertEnsuresBindsOutput (Lean.mkConst ``forallGenuineBoundPost)

-- External specs restating `retMatchesCalleeReturnTy` bit-width invariants or wrapping
-- boilerplate inside a one-point existential are caught as `UnboundReturnOutput`.
#eval assertDeclEnsuresVacuous ``restatesU32BoundsExtContract (some .unboundReturnOutput)
#eval assertDeclEnsuresVacuous ``restatesBoolBoundsExtContract (some .unboundReturnOutput)
#eval assertDeclEnsuresVacuous ``existsWrappedBoilerplateContract (some .unboundReturnOutput)
  { stepHeartbeats := 0, totalHeartbeats := 0 }

/-! ## 4. Mandatory Compile-Time Kernel Axiom Audit -/

/-- Axioms a kernel-checked declaration of this development may depend on. -/
def auditAllowedAxioms : List Lean.Name :=
  [``propext, ``Classical.choice, ``Quot.sound]

/-- Describes the first way in which constant `n` violates the audit policy, if any:
    it must exist, be safe, be neither an axiom nor an opaque (`opaque` / `partial`)
    constant, and depend transitively only on `auditAllowedAxioms`. This applies to
    every kind of constant (theorems, definitions, instances, structures), so a
    *definition* depending on `sorryAx` or `Lean.ofReduceBool` is rejected just like a
    theorem. -/
def auditViolation? (n : Lean.Name) : Lean.Meta.MetaM (Option String) := do
  let env ← Lean.getEnv
  let some ci := env.find? n
    | return some "unknown constant"
  if ci.isUnsafe then
    return some "unsafe declaration"
  if ci matches .axiomInfo _ then
    return some "axiom declaration"
  if ci matches .opaqueInfo _ then
    return some "opaque declaration (`opaque` or `partial`)"
  for ax in (← Lean.collectAxioms n) do
    unless auditAllowedAxioms.contains ax do
      return some s!"depends on disallowed axiom `{ax}`"
  return none

-- Self-test: the audit policy rejects each forbidden kind of constant and accepts a
-- standard-axiom theorem, so a silently permissive audit cannot pass.
#eval show Lean.Meta.MetaM Unit from do
  let mustReject : List Lean.Name :=
    [``sorryAx, ``Lean.ofReduceBool, ``Lean.trustCompiler, ``unsafeCast,
      ``IO.getNumHeartbeats, `SpecRealizabilityTests.thisConstantDoesNotExist]
  for n in mustReject do
    if (← auditViolation? n).isNone then
      throwError "kernel audit self-test failed: `{n}` was not rejected"
  let mustAccept : List Lean.Name :=
    [``Nat.add_comm, ``Classical.em, ``postconditionDichotomy_iff_exists_killed_mutant,
      ``checkEnsuresBindsOutput, ``auditViolation?]
  for n in mustAccept do
    if let some why ← auditViolation? n then
      throwError "kernel audit self-test failed: `{n}` was rejected ({why})"

#eval show Lean.Meta.MetaM Unit from do
  let env ← Lean.getEnv
  -- Audit by defining module rather than by name prefix, so a declaration placed
  -- outside the `Anneal.SpecRealizability` / `SpecRealizabilityTests` namespaces (or
  -- under `_root_`) cannot escape: every constant defined by the
  -- `Anneal.SpecRealizability` module and by this file is audited.
  let some specModIdx := env.getModuleIdx? `Anneal.SpecRealizability
    | throwError "kernel audit failed: module `Anneal.SpecRealizability` is not imported"
  let isTarget (n : Lean.Name) : Bool :=
    match env.getModuleIdxFor? n with
    | some idx => idx.toNat == specModIdx.toNat
    | none => true
  let allEntries : List (Lean.Name × Lean.ConstantInfo) :=
    env.constants.map₁.toList ++ env.constants.map₂.toList
  let mut declCount : Nat := 0
  let mut thmCount : Nat := 0
  let mut specDeclCount : Nat := 0
  let mut testDeclCount : Nat := 0
  for (n, ci) in allEntries do
    if !isTarget n then
      continue
    declCount := declCount + 1
    if (env.getModuleIdxFor? n).isSome then
      specDeclCount := specDeclCount + 1
    else
      testDeclCount := testDeclCount + 1
    if ci matches .thmInfo _ then
      thmCount := thmCount + 1
    if let some why ← auditViolation? n then
      throwError "kernel audit failed: `{n}`: {why}"
  -- The load-bearing results must exist and be kernel theorems (not definitions,
  -- axioms, or opaque constants standing in for them).
  let requiredTheorems : List Lean.Name := [
    ``VacuityClass.canonicalName_injective,
    ``postconditionDichotomy_iff_exists_killed_mutant,
    ``contractDeterministicOn_iff_kills_every_obs_nonequivalent_mutant,
    ``not_postconditionDichotomy_of_trivial,
    ``not_postconditionDichotomy_of_outputInsensitive,
    ``not_postconditionDichotomy_of_forwardOutputInsensitive,
    ``not_postconditionDichotomy_of_subsingleton,
    ``not_dichotomyModuloObservation_of_fibre_forwardInsensitive,
    ``postconditionDichotomy_or_pre_iff,
    ``not_postconditionDichotomy_or_pre_iff,
    ``statefulClaimReturnDichotomy_iff_moduloMemory,
    ``not_statefulClaimReturnDichotomy_of_returnInsensitive,
    ``not_mirCallContractReturnValueDichotomy_of_returnInsensitive,
    ``externalSpecCallContract_naive_realizable_iff_preSatisfiable,
    ``normalDichotomy_strictly_stronger_than_dichotomy,
    ``externalSpecEnsuresDichotomy_iff_moduloObservation,
    ``not_externalSpecEnsuresDichotomy_of_trivial_extraPost,
    ``exists_handler_holdsOn_of_universalNormalRealizable,
    ``cappedHeartbeats_never_unlimited
  ]
  for n in requiredTheorems do
    unless isTarget n do
      throwError "kernel audit failed: required theorem `{n}` is outside the audited modules"
    match env.find? n with
    | some (.thmInfo _) => pure ()
    | _ => throwError "kernel audit failed: `{n}` is not a kernel theorem"
  if specDeclCount == 0 || testDeclCount == 0 then
    throwError "kernel audit failed: audited {specDeclCount} library and \
      {testDeclCount} test declarations"
  if thmCount < 140 then
    throwError "kernel audit failed: audited only {thmCount} theorems (expected ≥ 140)"
  Lean.logInfo
    m!"SpecRealizability kernel axiom audit passed: {declCount} declarations ({thmCount} theorems, all clean)"

end SpecRealizabilityTests
