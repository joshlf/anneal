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
   tautologies, contradictory and `requires`-vacuous boilerplate fibres, and
   type-checked substituted goals.
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

/-- External spec whose user `ensures` mentions `ret` but constrains only the inputs. -/
def argsEmptyIgnoringRetPost (args : List Value) (ret : Value) : Prop :=
  ret = ret ∧ args = []

def argsEmptyIgnoringRetExtContract : MirCallContract :=
  externalSpecCallContract "core::slice::is_empty" sliceIsEmptySidecar
    (fun _ => True) argsEmptyIgnoringRetPost

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
